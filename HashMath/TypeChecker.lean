/-
  HashMath.TypeChecker — Declaration checking for HashMath CIC
-/

import HashMath.DefEq

namespace HashMath

/-- Check if any non-parameter field of any constructor in a Prop inductive has
    type in a universe higher than Prop (Sort 0). Uses type inference. -/
private def checkHasTypeLevelField (env : Environment) (block : InductiveBlock)
    (blockHash : Hash) (typeIdx : Nat) : Bool :=
  match block.types[typeIdx]? with
  | none => false
  | some indTy =>
    (List.range indTy.ctors.length).any fun j =>
      let ctorHash := hashCtor blockHash typeIdx j
      match env.getConstructorInfo ctorHash with
      | none => false
      | some ctorInfo => hasHighField ctorInfo.ty block.numParams 0 []
where
  hasHighField (ty : Expr) (numParams : Nat) (depth : Nat) (ctx : LocalCtx) : Bool :=
    match ty with
    | .forallE domTy body =>
      if depth < numParams then hasHighField body numParams (depth + 1) (domTy :: ctx)
      else
        match inferType env ctx domTy with
        | .ok domTyTy =>
          let domTyTy' := whnf env domTyTy
          match domTyTy' with
          | .sort fieldLevel =>
            match fieldLevel.normalize.toNat with
            | some 0 => hasHighField body numParams (depth + 1) (domTy :: ctx)
            | some _ => true  -- field in Sort n (n>0), blocks large elim
            | none => hasHighField body numParams (depth + 1) (domTy :: ctx)  -- polymorphic
          | _ => hasHighField body numParams (depth + 1) (domTy :: ctx)
        | .error _ => hasHighField body numParams (depth + 1) (domTy :: ctx)
    | _ => false

/-- Check universe constraints on constructor fields using type inference.
    For each field after `numParams`, infer the type of the domain (which should
    be `Sort l`), then check `l ≤ targetLevel`. This catches fields whose types
    compute to a universe that's too large, even when not syntactically apparent. -/
private def checkFieldUniverses (env : Environment) (ctorTy : Expr)
    (numParams : Nat) (targetLevel : Level) : Except String Unit :=
  go ctorTy 0 []
where
  go (ty : Expr) (depth : Nat) (ctx : LocalCtx) : Except String Unit :=
    match ty with
    | .forallE domTy body =>
      if depth < numParams then
        go body (depth + 1) (domTy :: ctx)
      else
        match inferType env ctx domTy with
        | .ok domTyTy =>
          let domTyTy' := whnf env domTyTy
          match domTyTy' with
          | .sort fieldLevel =>
            match fieldLevel.normalize.leq targetLevel.normalize with
            | some true => go body (depth + 1) (domTy :: ctx)
            | some false =>
              throw s!"checkDecl: field universe Sort {repr fieldLevel} exceeds target Sort {repr targetLevel} in constructor at depth {depth}"
            | none => go body (depth + 1) (domTy :: ctx)  -- polymorphic, can't determine statically
          | _ => throw s!"checkDecl: field domain type does not have a Sort type"
        | .error e => throw s!"checkDecl: cannot infer field type: {e}"
    | _ => .ok ()

/-- Check that a declaration is well-typed and add it to the environment. -/
def checkDecl (env : Environment) (d : Decl) : Except String (Hash × Environment) := do
  match d with
  | .axiom _numUnivs ty =>
    let tyTy ← inferTypeClosed env ty
    let tyTy' := whnf env tyTy
    match tyTy' with
    | .sort _ => pure ()
    | _ => throw "checkDecl: axiom type must be a type (Sort)"
    return env.addDecl d

  | .definition _numUnivs ty val =>
    let tyTy ← inferTypeClosed env ty
    let tyTy' := whnf env tyTy
    match tyTy' with
    | .sort _ => pure ()
    | _ => throw "checkDecl: definition type must be a type (Sort)"
    let valTy ← inferTypeClosed env val
    if !(isSubtype env [] valTy ty) then
      throw "checkDecl: definition value type mismatch"
    return env.addDecl d

  | .inductive block =>
    match checkInductiveBlock env block with
    | .ok () =>
      let (h, env') := env.addDecl d
      -- Update recursor info with proper generated types
      let env'' := (List.range block.types.length).foldl (fun env i =>
        let recHash := hashRec h i
        let recInfo := generateRecursorInfo block i h
        { env with recs := env.recs.insert recHash recInfo }
      ) env'
      -- For each inductive type, check universe constraints and refine large elimination
      let mut envFinal := env''
      for i in List.range block.types.length do
        match block.types[i]? with
        | some indTy =>
          let targetLevel := match getTargetSort indTy.type with
            | some l => l
            | none => Level.zero
          let isProp := match targetLevel.normalize.toNat with
            | some 0 => true
            | _ => false
          if !isProp then
            -- Non-Prop: check all field universes fit in the target
            for j in List.range indTy.ctors.length do
              let ctorHash := hashCtor h i j
              match envFinal.getConstructorInfo ctorHash with
              | some ctorInfo =>
                checkFieldUniverses envFinal ctorInfo.ty block.numParams targetLevel
              | none => throw "checkDecl: constructor not found after registration"
          else
            -- Prop: check if large elimination should be blocked due to Type-level fields
            let recHash := hashRec h i
            match envFinal.recs[recHash]? with
            | some recInfo =>
              if recInfo.allowsLargeElim then
                -- Verify using inferType that all non-param fields are in Prop
                let hasTypeLevelField := checkHasTypeLevelField envFinal block h i
                if hasTypeLevelField then
                  -- Regenerate recursor with large elim disabled
                  let recInfo' := { recInfo with
                    allowsLargeElim := false
                    recTy := generateRecursorType block i h false
                  }
                  envFinal := { envFinal with recs := envFinal.recs.insert recHash recInfo' }
            | none => pure ()
        | none => pure ()
      return (h, envFinal)
    | .error e => throw s!"checkDecl: inductive error: {e}"

  | .quotient _ =>
    return env.addDecl d

/-- Check that an expression has a given type. -/
def checkType (env : Environment) (e : Expr) (expectedTy : Expr) : Except String Unit := do
  let inferredTy ← inferTypeClosed env e
  if !(isSubtype env [] inferredTy expectedTy) then
    throw "checkType: type mismatch"

end HashMath
