module

public import UlmerBialgebras.Proofs.Sec5.ExtrasAlgTheory
public import Companion.Proofs.AlgTheoryFO

/-!
# Solution: single-sorted equational theories and Mathlib's first-order semantics

Proofs of the two statements of `Companion/Statements/ExtrasAlgTheory.lean` that compare with
Mathlib's
first-order logic (an addition beyond the paper). A companion file to
`UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean`, so that the paper's results do not import the
Mathlib bridge
`Companion/Proofs/AlgTheoryFO.lean`.

* `ofLanguage_model_iff` and `ofLanguage_isHom_iff` compare realizations and homomorphisms with
  Mathlib's (`Companion/Proofs/AlgTheoryFO.lean`).

## Main results

* `UlmerBialgebras.Paper.ofLanguage_model_iff`
* `UlmerBialgebras.Paper.ofLanguage_isHom_iff`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale]
-/

@[expose] public section

universe w uF uR

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Cart MSLanguage

/-- **Set models are Mathlib's first-order models** (addition beyond [forsman2026syntactic]): for
a single-sorted Mathlib language `L'` and an equational theory `T` over it, a Mathlib
`L'`-structure `M` satisfies the first-order theory `T.toFOTheory` (Mathlib's `M ⊨ T`) iff the
one-sorted family `M` in `Type w` is a model of `T`. -/
theorem ofLanguage_model_iff {L' : FirstOrder.Language.{uF, uR}} (T : (ofLanguage L').Theory)
    (M : Type w) [L'.Structure M] :
    FirstOrder.Language.Theory.Model M (Theory.toFOTheory T) ↔
      MSLanguage.Theory.Model (fun _ : Unit => M) T := by
  rw [FirstOrder.Language.Theory.model_iff]
  constructor
  · intro h
    exact ⟨fun φ hφ => (realize_toSentence_iff φ).1 (h _ ⟨φ, hφ, rfl⟩)⟩
  · rintro ⟨h⟩ _ ⟨φ, hφ, rfl⟩
    exact (realize_toSentence_iff φ).2 (h φ hφ)

open FirstOrder in
/-- **Set homomorphisms are Mathlib's homomorphisms** (addition beyond [forsman2026syntactic]):
for an algebraic single-sorted Mathlib language `L'`, a function `g : M → N` underlies a Mathlib
homomorphism `M →[L'] N` iff it underlies a homomorphism of the one-sorted families. -/
theorem ofLanguage_isHom_iff {L' : FirstOrder.Language.{uF, uR}} [L'.IsAlgebraic]
    (M N : Type w) [L'.Structure M] [L'.Structure N] (g : M → N) :
    (∃ φ : FirstOrder.Language.Hom L' M N, ⇑φ = g) ↔
      ∃ h : (ofLanguage L').Hom (fun _ : Unit => M) (fun _ : Unit => N),
        ∀ s, h.toFun s = TypeCat.ofHom g := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨⟨fun _ => TypeCat.ofHom φ, fun f =>
      (funMap_comm_iff f φ).2 fun x => φ.map_fun' f.2 x⟩, fun _ => rfl⟩
  · rintro ⟨h, hh⟩
    have hf : ∀ f : (ofLanguage L').Functions, ∀ x : Fin f.1 → M,
        g (Language.Structure.funMap f.2 x) = Language.Structure.funMap f.2 (g ∘ x) := by
      intro f
      refine (funMap_comm_iff f g).1 ?_
      have := h.map_fun' f
      simpa only [hh] using this
    exact ⟨⟨g, fun f x => hf ⟨_, f⟩ x, fun r => isEmptyElim r⟩, rfl⟩

end UlmerBialgebras.Paper
