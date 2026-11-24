module

public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Nakayama's lemma for nilpotent ideals

Two elementary but basic facts, used in the "nilpotent" half of the proof of Takeuchi's faithful
flatness theorem (Waterhouse, *Introduction to Affine Group Schemes*, §14.2), where they appear as
the repeated phrase "*`L = IL` and some `Iⁿ = 0`, hence `L = 0`*".

Unlike the classical Nakayama lemma (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` in Mathlib),
no finite generation is needed when the ideal is nilpotent.

## Main results

* `Submodule.eq_bot_of_le_smul_self`: if `N ≤ I • N` and `I ^ n = ⊥` then `N = ⊥`;
* `Submodule.eq_top_of_sup_smul_top`: if `S ⊔ I • ⊤ = ⊤` and `I ^ n = ⊥` then `S = ⊤`.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Section 14.2
-/

@[expose] public section

section
namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `N ≤ I • N` then `N ≤ Iⁿ • N` for every `n`. -/
lemma le_pow_smul_self (I : Ideal R) (N : Submodule R M) (h : N ≤ I • N) :
    ∀ n : ℕ, N ≤ I ^ n • N := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc N ≤ I • N := h
    _ ≤ I • (I ^ n • N) := Submodule.smul_mono le_rfl ih
    _ = I ^ (n + 1) • N := by rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_succ']

/-- **Nakayama's lemma for a nilpotent ideal.**  If `N ≤ I • N` and `I` is nilpotent, `N = ⊥`. -/
theorem eq_bot_of_le_smul_self {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥) (N : Submodule R M)
    (h : N ≤ I • N) : N = ⊥ :=
  le_bot_iff.mp (by simpa [hI] using le_pow_smul_self I N h n)

/-- If `S ⊔ I • ⊤ = ⊤` then `S ⊔ Iⁿ • ⊤ = ⊤` for every `n`. -/
lemma sup_pow_smul_top (I : Ideal R) (S : Submodule R M) (h : S ⊔ I • ⊤ = ⊤) :
    ∀ n : ℕ, S ⊔ I ^ n • (⊤ : Submodule R M) = ⊤ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    refine top_le_iff.mp ?_
    calc (⊤ : Submodule R M) = S ⊔ I • ⊤ := h.symm
    _ = S ⊔ I • (S ⊔ I ^ n • ⊤) := by rw [ih]
    _ = S ⊔ (I • S ⊔ I • (I ^ n • ⊤)) := by rw [Submodule.smul_sup]
    _ = (S ⊔ I • S) ⊔ I ^ (n + 1) • ⊤ := by
        rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_succ', ← sup_assoc]
    _ ≤ S ⊔ I ^ (n + 1) • (⊤ : Submodule R M) := by
        gcongr
        exact sup_le le_rfl (Submodule.smul_le_right)

/-- **Nakayama's lemma for a nilpotent ideal, "surjectivity" form.**  If `S ⊔ I • ⊤ = ⊤` and `I` is
nilpotent, then `S = ⊤`. -/
theorem eq_top_of_sup_smul_top {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥) (S : Submodule R M)
    (h : S ⊔ I • (⊤ : Submodule R M) = ⊤) : S = ⊤ := by
  have := sup_pow_smul_top I S h n
  simpa [hI] using this

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- If a linear map `ψ` admits a "weak section" `σ` (i.e. `ψ ∘ σ ∘ ψ = ψ`, which happens as soon
as `ψ` is surjective onto a projective module) and its kernel is contained in `I • ⊤` for a
nilpotent ideal `I`, then `ψ` is injective.

This is the step "*since `B ⊗_A B` is free we can lift back its generators and get a complement to
the kernel `M`; since the map modulo `I` is injective this implies `M = IM`, hence `M = 0`*" of
Waterhouse's proof. -/
theorem ker_eq_bot_of_weak_section {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥) (ψ : M →ₗ[R] N)
    (σ : N →ₗ[R] M) (hσ : ∀ m, ψ (σ (ψ m)) = ψ m)
    (hker : LinearMap.ker ψ ≤ I • (⊤ : Submodule R M)) : LinearMap.ker ψ = ⊥ := by
  refine eq_bot_of_le_smul_self hI _ fun m hm => ?_
  -- `p := id - σ ∘ ψ` is a projection onto the kernel which is the identity on the kernel
  set p : M →ₗ[R] M := LinearMap.id - σ ∘ₗ ψ with hp
  have hpker : ∀ y : M, p y ∈ LinearMap.ker ψ := by
    intro y
    simp [hp, LinearMap.mem_ker, hσ y]
  have hpm : p m = m := by
    have : ψ m = 0 := hm
    simp [hp, this]
  have hmem : m ∈ I • (⊤ : Submodule R M) := hker hm
  have key : ∀ y ∈ I • (⊤ : Submodule R M), p y ∈ I • LinearMap.ker ψ := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun r hr z _ => ?_) (fun u v hu hv => ?_)
    · simpa using Submodule.smul_mem_smul hr (hpker z)
    · rw [map_add]; exact Submodule.add_mem _ hu hv
  rw [← hpm]
  exact key m hmem

end Submodule
end
