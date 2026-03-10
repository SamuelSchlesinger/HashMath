#!/usr/bin/env bash
#
# deploy.sh — Deploy an hm-net seed node to Google Cloud (GCE e2-micro, free tier)
#
# Prerequisites:
#   - gcloud CLI installed and authenticated (gcloud auth login)
#   - A GCP project (gcloud config set project <PROJECT_ID>)
#   - Docker installed locally (for building the image)
#   - Billing enabled on the GCP project (required for Artifact Registry)
#
# Usage:
#   ./deploy/gce/deploy.sh              # Deploy with defaults
#   ./deploy/gce/deploy.sh --teardown   # Remove everything
#
# The script is idempotent — safe to run multiple times.
#

set -euo pipefail

# ── Configuration ────────────────────────────────────────────────────
INSTANCE_NAME="${HM_INSTANCE_NAME:-hashmath-seed}"
ZONE="${HM_ZONE:-us-east1-b}"
MACHINE_TYPE="${HM_MACHINE_TYPE:-e2-micro}"
REGION="${ZONE%-*}"
REPO_NAME="hashmath"
IMAGE_NAME="hm-net"
TAG="latest"
NETWORK_TAG="hm-net"
FIREWALL_RULE="allow-hm-net"
DISK_SIZE="10"  # GB

# ── Resolve paths ────────────────────────────────────────────────────
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
HM_NET_DIR="$PROJECT_ROOT/hm-net"

# ── Helpers ──────────────────────────────────────────────────────────
info()  { echo "==> $*"; }
error() { echo "ERROR: $*" >&2; exit 1; }

get_project_id() {
    local project
    project=$(gcloud config get-value project 2>/dev/null)
    if [[ -z "$project" || "$project" == "(unset)" ]]; then
        error "No GCP project set. Run: gcloud config set project <PROJECT_ID>"
    fi
    echo "$project"
}

# ── Teardown ─────────────────────────────────────────────────────────
if [[ "${1:-}" == "--teardown" ]]; then
    PROJECT_ID=$(get_project_id)
    info "Tearing down hm-net deployment in project $PROJECT_ID..."

    # Delete instance
    if gcloud compute instances describe "$INSTANCE_NAME" --zone="$ZONE" &>/dev/null; then
        info "Deleting instance $INSTANCE_NAME..."
        gcloud compute instances delete "$INSTANCE_NAME" --zone="$ZONE" --quiet
    fi

    # Release static IP
    if gcloud compute addresses describe "$INSTANCE_NAME-ip" --region="$REGION" &>/dev/null; then
        info "Releasing static IP..."
        gcloud compute addresses delete "$INSTANCE_NAME-ip" --region="$REGION" --quiet
    fi

    # Delete firewall rule
    if gcloud compute firewall-rules describe "$FIREWALL_RULE" &>/dev/null; then
        info "Deleting firewall rule..."
        gcloud compute firewall-rules delete "$FIREWALL_RULE" --quiet
    fi

    info "Teardown complete."
    exit 0
fi

# ── Preflight checks ────────────────────────────────────────────────
command -v gcloud >/dev/null || error "gcloud CLI not found. Install: https://cloud.google.com/sdk/docs/install"
command -v docker >/dev/null || error "Docker not found. Install: https://docs.docker.com/get-docker/"

PROJECT_ID=$(get_project_id)
FULL_IMAGE="${REGION}-docker.pkg.dev/${PROJECT_ID}/${REPO_NAME}/${IMAGE_NAME}:${TAG}"

info "Project:  $PROJECT_ID"
info "Zone:     $ZONE"
info "Instance: $INSTANCE_NAME"
info "Image:    $FULL_IMAGE"
echo

# ── Step 1: Enable required APIs ────────────────────────────────────
info "Enabling required APIs..."
gcloud services enable \
    compute.googleapis.com \
    artifactregistry.googleapis.com \
    --quiet

# ── Step 2: Create Artifact Registry repo (if needed) ───────────────
if ! gcloud artifacts repositories describe "$REPO_NAME" \
    --location="$REGION" &>/dev/null; then
    info "Creating Artifact Registry repository..."
    gcloud artifacts repositories create "$REPO_NAME" \
        --repository-format=docker \
        --location="$REGION" \
        --description="HashMath container images"
fi

# ── Step 3: Build and push Docker image ─────────────────────────────
info "Configuring Docker auth for Artifact Registry..."
gcloud auth configure-docker "${REGION}-docker.pkg.dev" --quiet

info "Building hm-net Docker image (linux/amd64)..."
docker build --platform linux/amd64 -t "$FULL_IMAGE" "$HM_NET_DIR"

info "Pushing image to Artifact Registry..."
docker push "$FULL_IMAGE"

# ── Step 4: Reserve static IP (if needed) ───────────────────────────
if ! gcloud compute addresses describe "$INSTANCE_NAME-ip" \
    --region="$REGION" &>/dev/null; then
    info "Reserving static external IP..."
    gcloud compute addresses create "$INSTANCE_NAME-ip" \
        --region="$REGION" \
        --network-tier=STANDARD
fi

STATIC_IP=$(gcloud compute addresses describe "$INSTANCE_NAME-ip" \
    --region="$REGION" --format='get(address)')
info "Static IP: $STATIC_IP"

# ── Step 5: Create firewall rule (if needed) ────────────────────────
if ! gcloud compute firewall-rules describe "$FIREWALL_RULE" &>/dev/null; then
    info "Creating firewall rule for port 4256 (libp2p)..."
    gcloud compute firewall-rules create "$FIREWALL_RULE" \
        --allow=tcp:4256,tcp:4257 \
        --target-tags="$NETWORK_TAG" \
        --description="Allow HashMath DHT traffic"
fi

# ── Step 6: Create or update instance ───────────────────────────────
if gcloud compute instances describe "$INSTANCE_NAME" --zone="$ZONE" &>/dev/null; then
    info "Updating existing instance with new container image..."
    gcloud compute instances update-container "$INSTANCE_NAME" \
        --zone="$ZONE" \
        --container-image="$FULL_IMAGE"
else
    info "Creating GCE instance ($MACHINE_TYPE)..."
    gcloud compute instances create-with-container "$INSTANCE_NAME" \
        --zone="$ZONE" \
        --machine-type="$MACHINE_TYPE" \
        --tags="$NETWORK_TAG" \
        --container-image="$FULL_IMAGE" \
        --container-arg="--data-dir" --container-arg="/data" \
        --container-arg="--listen" --container-arg="/ip4/0.0.0.0/tcp/4256" \
        --container-arg="--public" \
        --container-arg="--headless" \
        --container-arg="--health-port" --container-arg="4257" \
        --container-arg="--no-default-bootstrap" \
        --container-mount-disk=name="${INSTANCE_NAME}-data",mount-path=/data \
        --network-tier=STANDARD \
        --address="$STATIC_IP" \
        --boot-disk-size="${DISK_SIZE}GB" \
        --create-disk="name=${INSTANCE_NAME}-data,size=1GB,auto-delete=yes" \
        --metadata=google-logging-enabled=true
fi

# ── Step 7: Wait for node to start and get PeerId ───────────────────
info "Waiting for node to start..."
for attempt in $(seq 1 30); do
    if HEALTH=$(curl -s --connect-timeout 2 "http://${STATIC_IP}:4257/health" 2>/dev/null); then
        PEER_ID=$(echo "$HEALTH" | grep -o '"peer_id":"[^"]*"' | cut -d'"' -f4)
        if [[ -n "$PEER_ID" ]]; then
            break
        fi
    fi
    sleep 2
done

if [[ -z "${PEER_ID:-}" ]]; then
    info "Node may still be starting. Check manually:"
    info "  curl http://${STATIC_IP}:4257/health"
    info ""
    info "Once running, get the PeerId from the health endpoint and add"
    info "the bootstrap address to hm-net/src/main.rs DEFAULT_BOOTSTRAP_PEERS:"
    info "  \"/ip4/${STATIC_IP}/tcp/4256/p2p/<PEER_ID>\""
    exit 0
fi

BOOTSTRAP_ADDR="/ip4/${STATIC_IP}/tcp/4256/p2p/${PEER_ID}"

echo
info "═══════════════════════════════════════════════════════════"
info "  hm-net seed node is running!"
info ""
info "  IP:        $STATIC_IP"
info "  PeerId:    $PEER_ID"
info "  Bootstrap: $BOOTSTRAP_ADDR"
info ""
info "  Health:    curl http://${STATIC_IP}:4257/health"
info ""
info "  To make this the default for all users, add to"
info "  hm-net/src/main.rs DEFAULT_BOOTSTRAP_PEERS:"
info ""
info "    \"$BOOTSTRAP_ADDR\""
info ""
info "  To connect manually:"
info "    hm serve  (then the sidecar uses the compiled-in default)"
info "    # or explicitly:"
info "    hm-net --bootstrap $BOOTSTRAP_ADDR"
info "═══════════════════════════════════════════════════════════"
