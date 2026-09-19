import examples.e01.translation.FunsExternal

/-!
# Specifications for the external slice-iterator operations

Aeneas' `core.iter.traits.iterator.Iterator` trait models only `next`, `step_by`, `enumerate` and
`take`, so Charon emits `Iterator::all` as an opaque axiom. The same happens to the
`impl PartialOrd<&B> for &A` comparison. Both land in `examples/e01/translation/FunsExternal.lean`,
which is regenerated (and its directory deleted) by `npm run translate`, so the specifications for
them live here instead — the same arrangement as `Proofs.IntExternal`.

Everything below is stated for an arbitrary slice iterator and closure, so it is reusable across
crates: nothing here mentions a particular extracted function.

`Aeneas.Std.core.slice.iter.Iter` is a concrete structure `⟨slice, i⟩`, so the elements an iterator
has yet to yield are exactly `it.slice.val.drop it.i`.
-/

open Aeneas Std Result

/-- Comparison on shared references delegates to the underlying `PartialOrd` instance:
`(&a) <= (&b)` is `a <= b`. Since `core.cmp.PartialOrd` is a concrete structure in Aeneas' model,
this equation is all that is needed — the instance's own `le` then reduces as usual. -/
@[simp, step_simps] axiom shared_le_eq {A B : Type}
    (inst : core.cmp.PartialOrd A B) (x : A) (y : B) :
  Shared1A.Insts.CoreCmpPartialOrdShared0B.le inst x y = inst.le x y

/-- `Iterator::all` on a slice iterator, for a closure that decides a pure predicate `q` and
leaves its captured state untouched (`hq`). The result is `List.all q` over the elements the
iterator has not yet yielded.

Only the `Bool` component is constrained: Rust's `all` short-circuits on the first `false`, so the
position of the returned iterator depends on the data and is deliberately left unspecified.

`q` cannot be recovered from the goal by unification, so this is not a `@[step]` lemma; apply it
explicitly, supplying `q`. -/
axiom slice_iter_all_spec {T F : Type}
    (inst : core.ops.function.FnMut F T Bool) (f : F) (q : T → Bool)
    (hq : ∀ v, inst.call_mut f v ⦃ r => r.1 = q v ∧ r.2 = f ⦄)
    (it : core.slice.iter.Iter T) :
  core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all inst it f
  ⦃ r => r.1 = (it.slice.val.drop it.i).all q ⦄
