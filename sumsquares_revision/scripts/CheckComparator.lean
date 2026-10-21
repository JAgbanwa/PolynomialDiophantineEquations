import Lean

/-!
# Offline check of the comparator conditions

Run with `lake env lean --run scripts/CheckComparator.lean` (after `lake build`).

This script performs, independently of the comparator tool, the checks that the
comparator performs on `comparator.json`:

1. every theorem listed in `theorem_names` exists in `Challenge` and in `Solution`, with
   syntactically identical statements (`Expr` equality);
2. every constant defined in the `Challenge` module and used by those statements (the
   definitions `PolyQF.S2`, `PolyQF.Du`, `PolyQF.bqf`, `PolyQF.AdmissibleDegrees` and their
   auxiliary constants) exists in the solution environment with the same kind, type and value;
3. each listed theorem in `Solution` depends only on the axioms in `permitted_axioms`.

It is a convenience check only; the authoritative check is running the comparator itself
(see `verify.sh`).
-/

open Lean

/-- Axioms used by a constant, collected transitively. -/
partial def collectAxiomsIn (env : Environment) (n : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, axs) ← get
  if seen.contains n then return
  set (seen.insert n, axs)
  match env.find? n with
  | some (.axiomInfo _) => modify fun (s, a) => (s, a.push n)
  | some ci =>
    for m in ci.type.getUsedConstants do collectAxiomsIn env m
    if let some v := ci.value? (allowOpaque := true) then
      for m in v.getUsedConstants do collectAxiomsIn env m
  | none => pure ()

def sameConst (a b : ConstantInfo) : Bool :=
  a.type == b.type && a.levelParams == b.levelParams &&
    (a.value? (allowOpaque := true)) == (b.value? (allowOpaque := true)) &&
    (match a, b with
      | .defnInfo _, .defnInfo _ | .thmInfo _, .thmInfo _ | .opaqueInfo _, .opaqueInfo _
      | .axiomInfo _, .axiomInfo _ | .inductInfo _, .inductInfo _ | .ctorInfo _, .ctorInfo _
      | .recInfo _, .recInfo _ | .quotInfo _, .quotInfo _ => true
      | _, _ => false)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let cfgStr ← IO.FS.readFile "comparator.json"
  let cfg ← IO.ofExcept (Json.parse cfgStr)
  let names : Array String ← IO.ofExcept (cfg.getObjValAs? (Array String) "theorem_names")
  let permitted : Array String ← IO.ofExcept (cfg.getObjValAs? (Array String) "permitted_axioms")
  let chMod : String ← IO.ofExcept (cfg.getObjValAs? String "challenge_module")
  let solMod : String ← IO.ofExcept (cfg.getObjValAs? String "solution_module")
  let chEnv ← importModules #[{ module := chMod.toName }] {} (loadExts := false)
  let solEnv ← importModules #[{ module := solMod.toName }] {} (loadExts := false)
  let some chIdx := chEnv.getModuleIdx? chMod.toName
    | IO.eprintln s!"module {chMod} not found"; return 1
  let mut ok := true
  -- constants of the challenge module reachable from the statements
  let mut todo : Array Name := #[]
  for s in names do
    let n := s.toName
    match chEnv.find? n, solEnv.find? n with
    | some c, some d =>
      if c.type != d.type then
        IO.eprintln s!"statement mismatch: {n}"; ok := false
      unless d matches .thmInfo _ do
        IO.eprintln s!"not a theorem in the solution: {n}"; ok := false
      todo := todo ++ c.type.getUsedConstants
      let ((), (_, axs)) := (collectAxiomsIn solEnv n).run ({}, #[])
      for a in axs do
        unless permitted.contains a.toString do
          IO.eprintln s!"{n} uses non-permitted axiom {a}"; ok := false
    | none, _ => IO.eprintln s!"missing in challenge: {n}"; ok := false
    | _, none => IO.eprintln s!"missing in solution: {n}"; ok := false
  let mut seen : NameSet := {}
  let mut checked := 0
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if chEnv.getModuleIdxFor? n != some chIdx then continue
    match chEnv.find? n, solEnv.find? n with
    | some c, some d =>
      checked := checked + 1
      if !sameConst c d then
        IO.eprintln s!"definition mismatch: {n}"; ok := false
      todo := todo ++ c.type.getUsedConstants
      if let some v := c.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
    | _, _ => IO.eprintln s!"definition missing in solution: {n}"; ok := false
  if ok then
    IO.println s!"OK: {names.size} statements identical, {checked} challenge definitions identical, only permitted axioms used."
    return 0
  else
    return 1
