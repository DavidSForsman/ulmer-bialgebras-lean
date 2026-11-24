module

meta import Companion.Proofs
meta import Lean

/-!
Compare the compiled types of every theorem in comparator.json, including inferred binders.
The types must be definitionally equal and have the same binder kinds (`isDefEq` ignores the
difference between `(x : α)` and `{x : α}`).
Run `lake env lean scripts/check_compiled_types.lean` after building the project.
The comparison uses the shared trusted definitions and the Solution environment.

## References

* [Comparator](https://github.com/leanprover/comparator), which this check complements
-/

open Lean Meta

-- BEGIN binderKinds (kept identical in `stmt_hashes.lean`, `check_compiled_types.lean` and
-- `review_cone.lean`;
-- `test_check_statements.py` checks this)
/-- The binder kinds of `e` (`∀` and `fun` binders, in preorder): `0` explicit, `1` implicit,
`2` strict implicit, `3` instance implicit. `Expr.hash` and `isDefEq` both ignore them. -/
partial def binderKinds (e : Expr) : Array Nat := go e #[]
where
  /-- The code of a binder kind. -/
  code : BinderInfo → Nat
    | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
  /-- Accumulate the binder kinds of an expression. -/
  go : Expr → Array Nat → Array Nat
    | .forallE _ t b bi, acc => go b (go t (acc.push (code bi)))
    | .lam _ t b bi, acc => go b (go t (acc.push (code bi)))
    | .letE _ t v b _, acc => go b (go v (go t acc))
    | .app f a, acc => go a (go f acc)
    | .mdata _ e, acc => go e acc
    | .proj _ _ e, acc => go e acc
    | _, acc => acc
-- END binderKinds

set_option maxHeartbeats 2000000 in
#eval show MetaM Unit from do
  let challengeEnv ← importModules #[{ module := `Companion.Statements }] {} (loadExts := false)
  let solutionEnv ← getEnv
  let raw ← if ← System.FilePath.pathExists "scripts/lib/checked_lists.py" then
    IO.Process.run { cmd := "python3", args := #["scripts/lib/checked_lists.py"] }
  else if ← System.FilePath.pathExists "comparator.all.json" then
    IO.FS.readFile "comparator.all.json"
  else
    IO.FS.readFile "comparator.json"
  let cfg ← match Json.parse raw with
    | .ok cfg => pure cfg
    | .error msg => throwError "Invalid comparator.json: {msg}"
  let theoremNames ← match cfg.getObjValAs? (Array String) "theorem_names" with
    | .ok names => pure names
    | .error msg => throwError "Invalid theorem list: {msg}"
  unless !theoremNames.isEmpty do
    throwError "No checked theorems configured"
  let names := theoremNames.map fun s => (s.splitOn ".").foldl Name.str Name.anonymous
  for n in names do
    let some c := challengeEnv.find? n | throwError "Missing Challenge theorem {n}"
    let some s := solutionEnv.find? n | throwError "Missing Solution theorem {n}"
    unless c.levelParams.length == s.levelParams.length do
      throwError "Universe parameter count differs for {n}"
    let levels := (List.range c.levelParams.length).map fun i =>
      Level.param (Name.mkSimple s!"compare_u{i}")
    let ct := c.type.instantiateLevelParams c.levelParams levels
    let st := s.type.instantiateLevelParams s.levelParams levels
    unless ← withNewMCtxDepth (withTransparency .all (isDefEq ct st)) do
      throwError "Compiled types differ for {n}\nChallenge: {ct}\nSolution: {st}"
    unless binderKinds ct == binderKinds st do
      throwError "Binder kinds differ for {n}\nChallenge: {ct}\nSolution: {st}"
  IO.println s!"Compiled type comparison passed: {names.size}/{names.size}"
