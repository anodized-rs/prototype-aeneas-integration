import Aeneas

/-!
# `Anodized` specification sugar

`Anodized f` is the Aeneas specification statement for a function `f` carrying an
anodized `#[spec(...)]` annotation: *for all arguments, if the precondition holds then
running `f` produces a result satisfying the postcondition.*

For a function `f a₁ … aₙ` it expands to:
```
∀ a₁ … aₙ,
  __anodized_fn_requires_f a₁ … aₙ = ok true →
    f a₁ … aₙ ⦃ result => __anodized_fn_ensures_f a₁ … aₙ result = ok true ⦄
```
(the no-argument case drops the `∀`). The `⦃ ⦄` triple desugars to `Aeneas.Std.WP.spec`.

The `__anodized_fn_requires_<f>` / `__anodized_fn_ensures_<f>` declarations are the ones
Aeneas extracts alongside `f`; this elaborator derives those names from `f` and reads the
argument count off the `requires` declaration's type.
-/

open Lean Elab Term Meta

namespace Anodized

/-- The sibling declaration `<pre><f>` living in the same namespace as `f`
(e.g. `e01.f4` ↦ `e01.__anodized_fn_ensures_f4`). -/
def siblingName (pre : String) (f : Name) : Name :=
  match f with
  | .str p s => .str p (pre ++ s)
  | n        => .str n pre

/-- Number of explicit arguments in a (function) type. -/
def explicitArity (type : Expr) : MetaM Nat :=
  forallTelescopeReducing type fun xs _ =>
    xs.foldlM (init := 0) fun n x => do
      return n + (if (← x.fvarId!.getDecl).binderInfo.isExplicit then 1 else 0)

end Anodized

/-- `Anodized f` is the Aeneas specification statement for a function `f` carrying an
anodized `#[spec(...)]` annotation: *for all arguments, if the precondition holds then
running `f` produces a result satisfying the postcondition.*
-/
elab:max "Anodized " f:ident : term <= expectedType? => do
  let fName ← realizeGlobalConstNoOverloadWithInfo f
  let reqName := Anodized.siblingName "__anodized_fn_requires_" fName
  let ensName := Anodized.siblingName "__anodized_fn_ensures_" fName
  let reqInfo ← getConstInfo reqName
  let arity ← Anodized.explicitArity reqInfo.type
  let xs : Array Ident := (Array.range arity).map fun i => mkIdent (.mkSimple s!"x_{i}")
  let reqId := mkIdent reqName
  let ensId := mkIdent ensName
  let okTrue ← `(Aeneas.Std.Result.ok true)
  let reqApp ← if arity == 0 then `($reqId)        else `($reqId $xs*)
  let fApp   ← if arity == 0 then `($f)            else `($f $xs*)
  let ensApp ← if arity == 0 then `($ensId result) else `($ensId $xs* result)
  let mut stmt ← `($reqApp = $okTrue → Aeneas.Std.WP.spec $fApp (fun result => $ensApp = $okTrue))
  for x in xs.reverse do
    stmt ← `(∀ $x:ident, $stmt)
  elabTerm stmt expectedType?

/-- Tag every extracted `__anodized_fn_{requires,ensures}_*` declaration with `@[step_simps]`
so that `step*` unfolds the spec predicates (and their closure machinery, which shares the
name prefix) automatically — avoiding manual `unfold __anodized_fn_ensures_… .closure.…call`.

Call once per proof file, *after* importing the crate's translation. Idempotent: re-tagging
a declaration is a no-op, so calling it from several files is harmless. -/
elab "register_anodized_simps" : command => do
  let env ← Lean.getEnv
  let mut ids : Array Lean.Ident := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.splitOn "__anodized_fn_ensures").length ≥ 2 ||
       (s.splitOn "__anodized_fn_requires").length ≥ 2 then
      ids := ids.push (Lean.mkIdent n)
  if ids.isEmpty then return
  Lean.Elab.Command.elabCommand (← `(attribute [step_simps] $ids*))

/-- `m = ok v ↔ m ⦃ x => x = v ⦄` (the Aeneas WP triple is total). Use it to turn a
postcondition `… = ok true` — or a hypothesis of that shape — into a `⦃ ⦄` triple that
`step*` can evaluate. -/
theorem eq_ok_iff {α} {m : Aeneas.Std.Result α} {v : α} :
    m = .ok v ↔ Aeneas.Std.WP.spec m (fun x => x = v) := by
  rw [Aeneas.Std.WP.spec_equiv_exists]
  exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨_, hy, h⟩ => h ▸ hy⟩
