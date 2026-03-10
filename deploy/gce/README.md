# Deploying an hm-net seed node to Google Cloud

## Cost

- **e2-micro** VM: free tier eligible (1 per billing account, us-east1/us-west1/us-central1)
- **Static IP**: free while attached to a running VM (STANDARD tier)
- **Artifact Registry**: free up to 500 MB/month
- **Disk**: 10 GB boot + 1 GB data = $0.40/month

Total: effectively **$0/month** on free tier.

## Prerequisites

1. [Google Cloud SDK](https://cloud.google.com/sdk/docs/install) (`gcloud` CLI)
2. [Docker](https://docs.docker.com/get-docker/)
3. A GCP project with billing enabled

```sh
gcloud auth login
gcloud config set project <YOUR_PROJECT_ID>
```

## Deploy

```sh
./deploy/gce/deploy.sh
```

The script:
1. Enables Compute Engine and Artifact Registry APIs
2. Creates an Artifact Registry repo for the container image
3. Builds and pushes the `hm-net` Docker image
4. Reserves a static external IP
5. Opens TCP port 4256 (libp2p) and 4257 (health check)
6. Creates an e2-micro VM running the container
7. Waits for the node to start and prints the bootstrap address

## Configuration

Override defaults via environment variables:

| Variable | Default | Description |
|----------|---------|-------------|
| `HM_INSTANCE_NAME` | `hashmath-seed` | GCE instance name |
| `HM_ZONE` | `us-east1-b` | GCE zone (pick a free-tier zone) |
| `HM_MACHINE_TYPE` | `e2-micro` | Machine type |

## After deployment

The script prints a bootstrap address like:

```
/ip4/34.56.78.90/tcp/4256/p2p/12D3KooW...
```

Add this to `DEFAULT_BOOTSTRAP_PEERS` in `hm-net/src/main.rs` so all nodes
auto-connect:

```rust
const DEFAULT_BOOTSTRAP_PEERS: &[&str] = &[
    "/ip4/34.56.78.90/tcp/4256/p2p/12D3KooW...",
];
```

Then rebuild and release. New users will connect to the seed automatically.

## Teardown

```sh
./deploy/gce/deploy.sh --teardown
```

Removes the VM, static IP, and firewall rule.

## Monitoring

```sh
# Health check
curl http://<IP>:4257/health

# View logs
gcloud compute instances get-serial-port-output hashmath-seed --zone=us-east1-b

# SSH into the VM
gcloud compute ssh hashmath-seed --zone=us-east1-b
```
