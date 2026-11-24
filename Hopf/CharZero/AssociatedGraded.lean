module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Hopf.CharZero.TangentEstimate

/-!
# The associated graded algebra of a commutative Hopf algebra in characteristic zero

Building on `Hopf/CharZero/TangentEstimate.lean`, this file shows that for a commutative
bialgebra `A` over a field `k` of characteristic zero the associated graded algebra of the
augmentation filtration behaves like a polynomial algebra: if `y ∈ Iᵃ \ Iᵃ⁺¹` and
`z ∈ I^b \ I^(b+1)`, then `y * z ∉ I^(a+b+1)` (`HopfAlgebra.CharZero.Frame.mul_notMem_pow_succ`).

The bookkeeping is organised around a *tangent frame*: a finite family `x₁, …, x_r` of elements of
the augmentation ideal whose classes form a basis of `I/I²` (`HopfAlgebra.CharZero.Frame`). Such a
frame exists whenever `I` is a finitely generated ideal, e.g. for a noetherian `A`
(`HopfAlgebra.CharZero.exists_frame`).

The main consequence, proved here, is `HopfAlgebra.CharZero.mem_pow_of_sq_eq_zero`: an element
with `z ^ 2 = 0` lies in every power of the augmentation ideal.

## Main results

* `HopfAlgebra.CharZero.Frame`: a tangent frame, a finite family of elements of the augmentation
  ideal `I` whose classes modulo `I²` are linearly independent and span `I/I²`.
* `HopfAlgebra.CharZero.exists_frame`: if `I` is finitely generated, a tangent frame exists.
* `HopfAlgebra.CharZero.Frame.mul_notMem_pow_succ`: given a tangent frame, if `y ∈ Iᵃ \ Iᵃ⁺¹` and
  `z ∈ I^b \ I^(b+1)`, then `y * z ∉ I^(a+b+1)`.
* `HopfAlgebra.CharZero.mem_pow_of_sq_eq_zero`: in characteristic zero, given a tangent frame, an
  element `z` with `z * z = 0` lies in `Iⁿ` for every `n`.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 11.4
-/

@[expose] public section

section
open HopfAlgebra.Commutative
namespace HopfAlgebra.CharZero

open TensorProduct Coalgebra MvPolynomial HopfAlgebra.Commutative

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A]

/-- A *tangent frame* of a commutative bialgebra: a finite family of elements of the augmentation
ideal `I` whose classes modulo `I²` are linearly independent and span `I/I²`. -/
structure Frame (k A : Type*) [Field k] [CommRing A] [Bialgebra k A] where
  /-- the number of elements of the frame -/
  r : ℕ
  /-- the elements of the frame -/
  x : Fin r → A
  /-- they lie in the augmentation ideal -/
  mem : ∀ i, x i ∈ augmentationIdeal k A
  /-- their classes modulo `I²` are linearly independent -/
  indep : LinearIndependent k fun i => Ideal.Quotient.mk ((augmentationIdeal k A) ^ 2) (x i)
  /-- their classes span `I/I²` -/
  spans : ∀ v ∈ augmentationIdeal k A,
    ∃ c : Fin r → k, v - ∑ i, c i • x i ∈ (augmentationIdeal k A) ^ 2

namespace Frame

variable (F : Frame k A)

/-- Evaluating a homogeneous polynomial of degree `n` at the frame lands in `I ^ n`. -/
lemma aeval_mem_pow {n : ℕ} {P : MvPolynomial (Fin F.r) k} (hP : P.IsHomogeneous n) :
    aeval F.x P ∈ (augmentationIdeal k A) ^ n :=
  aeval_mem_pow_of_isHomogeneous _ _ F.mem hP

/-- Every element of `Iⁿ` is, modulo `Iⁿ⁺¹`, a homogeneous polynomial of degree `n` in the
frame. -/
theorem exists_isHomogeneous_approx :
    ∀ (n : ℕ), ∀ y ∈ (augmentationIdeal k A) ^ n,
      ∃ P : MvPolynomial (Fin F.r) k, P.IsHomogeneous n ∧
        y - aeval F.x P ∈ (augmentationIdeal k A) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
      -- in degree `0`, `y` is approximated by the constant `ε(y)`: `y - ε(y) ∈ I`
      intro y _
      refine ⟨C (counit (R := k) y), isHomogeneous_C _ _, ?_⟩
      have : aeval F.x (C (counit (R := k) y)) = algebraMap k A (counit (R := k) y) := by simp
      rw [this, pow_one]
      simp [mem_augmentationIdeal]
  | succ n ih =>
      intro y hy
      -- `Iⁿ⁺¹ = Iⁿ · I`: it suffices to treat products `a * b` and sums
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · -- approximate `a ∈ Iⁿ` by `P` and `b ∈ I` by its linear part `∑ cᵢ xᵢ`
        intro a ha b hb
        obtain ⟨P, hP, hPa⟩ := ih a ha
        obtain ⟨c, hc⟩ := F.spans b hb
        refine ⟨P * ∑ i, C (c i) * X i, ?_, ?_⟩
        · refine hP.mul ?_
          refine IsHomogeneous.sum _ _ 1 fun i _ => ?_
          simpa using (isHomogeneous_C (Fin F.r) (c i)).mul (isHomogeneous_X k i)
        · have hL : aeval F.x (∑ i, C (c i) * X i) = ∑ i, c i • F.x i := by
            simp [Algebra.smul_def]
          -- the error `(a - P(x)) b + P(x) (b - ∑ cᵢ xᵢ)` has both terms in `Iⁿ⁺²`
          have hsplit : a * b - aeval F.x (P * ∑ i, C (c i) * X i)
              = (a - aeval F.x P) * b + aeval F.x P * (b - ∑ i, c i • F.x i) := by
            rw [map_mul, hL]; ring
          rw [hsplit]
          refine Ideal.add_mem _ ?_ ?_
          · have : (a - aeval F.x P) * b ∈ (augmentationIdeal k A) ^ (n + 1 + 1) := by
              have := Ideal.mul_mem_mul hPa hb
              rwa [← pow_succ] at this
            exact this
          · have h1 : aeval F.x P ∈ (augmentationIdeal k A) ^ n := F.aeval_mem_pow hP
            have := Ideal.mul_mem_mul h1 hc
            have hle : (augmentationIdeal k A) ^ n * (augmentationIdeal k A) ^ 2
                ≤ (augmentationIdeal k A) ^ (n + 1 + 1) := by
              rw [← pow_add]
            exact hle this
      · -- the approximations of a sum add up
        rintro p q ⟨P, hP, hPp⟩ ⟨Q, hQ, hQq⟩
        refine ⟨P + Q, hP.add hQ, ?_⟩
        have : p + q - aeval F.x (P + Q) = (p - aeval F.x P) + (q - aeval F.x Q) := by
          rw [map_add]; ring
        rw [this]
        exact Ideal.add_mem _ hPp hQq

/-- The leading term of an element of `Iᵃ ∖ Iᵃ⁺¹` is a nonzero homogeneous polynomial. -/
theorem exists_ne_zero_isHomogeneous_approx {a : ℕ} {y : A}
    (hy : y ∈ (augmentationIdeal k A) ^ a) (hy' : y ∉ (augmentationIdeal k A) ^ (a + 1)) :
    ∃ P : MvPolynomial (Fin F.r) k, P ≠ 0 ∧ P.IsHomogeneous a ∧
      y - aeval F.x P ∈ (augmentationIdeal k A) ^ (a + 1) := by
  obtain ⟨P, hP, hPy⟩ := F.exists_isHomogeneous_approx a y hy
  refine ⟨P, ?_, hP, hPy⟩
  rintro rfl
  apply hy'
  have : y = (y - aeval F.x (0 : MvPolynomial (Fin F.r) k)) := by simp
  rw [this]
  exact hPy

variable [CharZero k]

/-- **The associated graded algebra is a domain.**  If `y` has order exactly `a` and `z` order
exactly `b` for the augmentation filtration, then `y * z` has order exactly `a + b`; in
particular it is nonzero. -/
theorem mul_notMem_pow_succ (F : Frame k A) {a b : ℕ} {y z : A}
    (hy : y ∈ (augmentationIdeal k A) ^ a) (hy' : y ∉ (augmentationIdeal k A) ^ (a + 1))
    (hz : z ∈ (augmentationIdeal k A) ^ b) (hz' : z ∉ (augmentationIdeal k A) ^ (b + 1)) :
    y * z ∉ (augmentationIdeal k A) ^ (a + b + 1) := by
  obtain ⟨P, hP0, hP, hPy⟩ := exists_ne_zero_isHomogeneous_approx F hy hy'
  obtain ⟨Q, hQ0, hQ, hQz⟩ := exists_ne_zero_isHomogeneous_approx F hz hz'
  intro hcon
  have hPQ : (P * Q).IsHomogeneous (a + b) := hP.mul hQ
  have happrox : y * z - aeval F.x (P * Q) ∈ (augmentationIdeal k A) ^ (a + b + 1) := by
    have hsplit : y * z - aeval F.x (P * Q)
        = (y - aeval F.x P) * z + aeval F.x P * (z - aeval F.x Q) := by
      rw [map_mul]; ring
    rw [hsplit]
    refine Ideal.add_mem _ ?_ ?_
    · have := Ideal.mul_mem_mul hPy hz
      have hle : (augmentationIdeal k A) ^ (a + 1) * (augmentationIdeal k A) ^ b
          ≤ (augmentationIdeal k A) ^ (a + b + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      exact hle this
    · have := Ideal.mul_mem_mul (F.aeval_mem_pow hP) hQz
      have hle : (augmentationIdeal k A) ^ a * (augmentationIdeal k A) ^ (b + 1)
          ≤ (augmentationIdeal k A) ^ (a + b + 1) := by
        rw [← pow_add]
        exact Ideal.pow_le_pow_right (by omega)
      exact hle this
  have hmem : aeval F.x (P * Q) ∈ (augmentationIdeal k A) ^ (a + b + 1) := by
    have : aeval F.x (P * Q) = y * z - (y * z - aeval F.x (P * Q)) := by ring
    rw [this]
    exact Ideal.sub_mem _ hcon happrox
  have : P * Q = 0 := eq_zero_of_isHomogeneous F.x F.mem F.indep hPQ hmem
  rcases mul_eq_zero.1 this with h | h
  · exact hP0 h
  · exact hQ0 h

end Frame

/-! ## Existence of a tangent frame -/

/-- Every element of a finitely generated augmentation ideal `I` is a `k`-linear combination
of the ideal's generators modulo `I ^ 2`. -/
private lemma augmentationIdeal_mod_sq_mem_span {G : Finset A}
    (hG : Ideal.span (G : Set A) = augmentationIdeal k A) {v : A}
    (hv : v ∈ augmentationIdeal k A) :
    (Ideal.Quotient.mkₐ k (augmentationIdeal k A ^ 2)).toLinearMap v ∈
      Submodule.span k ((Ideal.Quotient.mkₐ k (augmentationIdeal k A ^ 2)).toLinearMap ''
        (G : Set A)) := by
  set I := augmentationIdeal k A
  set mk : A →ₗ[k] (A ⧸ I ^ 2) := (Ideal.Quotient.mkₐ k (I ^ 2)).toLinearMap
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 (hG.symm ▸ hv)
  have hmem : v - ∑ g ∈ G, (counit (R := k) (f g)) • g ∈ I ^ 2 := by
    have hrw : v - ∑ g ∈ G, (counit (R := k) (f g)) • g
        = ∑ g ∈ G, (f g - (counit (R := k) (f g)) • (1 : A)) * g := by
      rw [← hf, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [sub_mul]; simp [Algebra.smul_def]
    rw [hrw, pow_two]
    refine Ideal.sum_mem _ fun g hg => Ideal.mul_mem_mul ?_ (hG ▸ Ideal.subset_span hg)
    simp [I, mem_augmentationIdeal, Algebra.smul_def]
  have h0 : mk (v - ∑ g ∈ G, (counit (R := k) (f g)) • g) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  have hv' : mk v = ∑ g ∈ G, (counit (R := k) (f g)) • mk g := by
    have := sub_eq_zero.1 (by simpa [map_sub, map_sum, map_smul] using h0)
    simpa using this
  rw [hv']
  exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)

/-- If the augmentation ideal is finitely generated — e.g. if `A` is noetherian — then a tangent
frame exists: one may lift a basis of `I/I²`. -/
theorem exists_frame (hfg : (augmentationIdeal k A).FG) : Nonempty (Frame k A) := by
  classical
  set I := augmentationIdeal k A with hI
  set mk : A →ₗ[k] (A ⧸ I ^ 2) := (Ideal.Quotient.mkₐ k (I ^ 2)).toLinearMap with hmk
  obtain ⟨G, hG⟩ := hfg
  -- `S`, the span of the images of the generators in `A / I²`, is finite-dimensional, and each of
  -- its elements lifts to `I`
  set S : Submodule k (A ⧸ I ^ 2) := Submodule.span k (mk '' (G : Set A)) with hS
  have : Module.Finite k S := by
    rw [hS]; exact Module.Finite.span_of_finite k (Set.Finite.image _ G.finite_toSet)
  have himg : ∀ s : S, ∃ v ∈ I, mk v = (s : A ⧸ I ^ 2) := fun s => by
    have hle : S ≤ Submodule.map mk (I.restrictScalars k) := by
      rw [hS]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, by rw [← hG] at *; exact Ideal.subset_span hg, rfl⟩
    exact hle s.2
  -- the frame: lifts `x j ∈ I` of a basis `b` of `S`
  let b := Module.finBasis k S
  choose x hxI hxeq using fun j => himg (b j)
  refine ⟨⟨Module.finrank k S, x, hxI, ?_, ?_⟩⟩
  · -- linearly independent modulo `I²`, since `b` is
    have hbi : LinearIndependent k fun j => ((b j : A ⧸ I ^ 2)) :=
      b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
    have heq : (fun j => Ideal.Quotient.mk (I ^ 2) (x j)) = fun j => ((b j : A ⧸ I ^ 2)) :=
      funext fun j => by
        rw [← hxeq j]
        rfl
    rwa [heq]
  · -- spanning modulo `I²`: expand the image of `v` in the basis `b`
    intro v hv
    set s : S := ⟨mk v, augmentationIdeal_mod_sq_mem_span hG hv⟩
    refine ⟨fun j => b.repr s j, ?_⟩
    have h1 : mk (∑ j, (b.repr s j) • x j) = ∑ j, (b.repr s j) • (b j : A ⧸ I ^ 2) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hxeq j]
    have h2 : (s : A ⧸ I ^ 2) = ∑ j, (b.repr s j) • (b j : A ⧸ I ^ 2) := by
      rw [(b.sum_repr s).symm]; push_cast; simp
    have h3 : mk (v - ∑ j, (b.repr s j) • x j) = 0 := by
      rw [map_sub, h1, ← h2]; simp [s]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact h3

/-! ## Square-zero elements lie in every power of the augmentation ideal -/

variable [CharZero k]

/-- If `z ^ 2 = 0` then `z` lies in every power of the augmentation ideal. -/
theorem mem_pow_of_sq_eq_zero (F : Frame k A) {z : A} (hz : z * z = 0) (n : ℕ) :
    z ∈ (augmentationIdeal k A) ^ n := by
  by_contra hcon
  have hex : ∃ m, z ∉ (augmentationIdeal k A) ^ m := ⟨n, hcon⟩
  classical
  set m₀ := Nat.find hex with hm₀
  have hm₀mem : z ∉ (augmentationIdeal k A) ^ m₀ := Nat.find_spec hex
  have hm₀pos : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h | h
    · exfalso; apply hm₀mem; rw [h]; simp
    · exact h
  obtain ⟨a, ha⟩ : ∃ a, m₀ = a + 1 := ⟨m₀ - 1, by omega⟩
  have hza : z ∈ (augmentationIdeal k A) ^ a := by
    by_contra h
    have hle : m₀ ≤ a := hm₀ ▸ Nat.find_le h
    omega
  have hza' : z ∉ (augmentationIdeal k A) ^ (a + 1) := by rw [← ha]; exact hm₀mem
  have := Frame.mul_notMem_pow_succ F hza hza' hza hza'
  rw [hz] at this
  exact this (Submodule.zero_mem _)

end HopfAlgebra.CharZero
end
