module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# Extension of scalars is a braided monoidal functor

For a ring map `f : R →+* S`, the functor `M ↦ S ⊗_R M` (`ModuleCat.extendScalars f`) is
strong monoidal: `μ : (S ⊗ M) ⊗_S (S ⊗ N) ≅ S ⊗ (M ⊗ N)` is
`AlgebraTensorModule.distribBaseChange` and `ε : S ≅ S ⊗_R R` is
`AlgebraTensorModule.rid`. Mathlib supplies this monoidal structure in
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`; this file proves it is braided.

For a localization `R → R_α` this is the symmetric monoidal functor `L_α` of Lemma 6.10, which
induces the functors of algebras `L_α^T` (Theorem 3.22).

## Main results

* `UlmerBialgebras.Paper.Loc.monoidal`: `ModuleCat.extendScalars f` is a monoidal functor, with
  structure maps `UlmerBialgebras.Paper.Loc.muIso` and `UlmerBialgebras.Paper.Loc.epsIso`.
* `UlmerBialgebras.Paper.Loc.braided`: `ModuleCat.extendScalars f` is a braided monoidal functor.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 3.22 and Lemma 6.10
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory MonoidalCategory ModuleCat ChangeOfRings TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

local notation "E" => ModuleCat.extendScalars f

/-- `μ_{M,N}`: `(S ⊗ M) ⊗_S (S ⊗ N) ≅ S ⊗ (M ⊗ N)`. -/
noncomputable def muIso (M N : ModuleCat.{u} R) : (E).obj M ⊗ (E).obj N ≅ (E).obj (M ⊗ N) :=
  let _ := f.toAlgebra
  LinearEquiv.toModuleIso (AlgebraTensorModule.distribBaseChange R S M N).symm

/-- `μ_{M,N}((s ⊗ m) ⊗ (t ⊗ n)) = (s * t) ⊗ (m ⊗ n)`. -/
lemma muIso_hom_tmul (M N : ModuleCat.{u} R) (s t : S) (m : M) (n : N) :
    (muIso f M N).hom.hom ((s ⊗ₜ[R,f] m) ⊗ₜ (t ⊗ₜ[R,f] n)) = (s * t) ⊗ₜ[R,f] (m ⊗ₜ n) := by
  let _ := f.toAlgebra
  exact AlgebraTensorModule.distribBaseChange_symm_tmul (R := R) (A := S) (n := m) (q := n) s t

/-- `ε : S ≅ S ⊗_R R`. -/
noncomputable def epsIso : 𝟙_ (ModuleCat.{u} S) ≅ (E).obj (𝟙_ (ModuleCat.{u} R)) :=
  let _ := f.toAlgebra
  (LinearEquiv.toModuleIso (AlgebraTensorModule.rid R S S)).symm

/-- Two `S`-linear maps out of `(S ⊗ M) ⊗_S (S ⊗ N)` agree once they agree on the elements
    `(s ⊗ m) ⊗ (t ⊗ n)`. -/
lemma ext₂ {M N : ModuleCat.{u} R} {P : ModuleCat.{u} S} {α β : (E).obj M ⊗ (E).obj N ⟶ P}
    (h : ∀ (s t : S) (m : M) (n : N),
      α.hom ((s ⊗ₜ[R,f] m) ⊗ₜ (t ⊗ₜ[R,f] n)) = β.hom ((s ⊗ₜ[R,f] m) ⊗ₜ (t ⊗ₜ[R,f] n))) :
    α = β := by
  let _ := f.toAlgebra
  let α₀ : (S ⊗[R] M) ⊗[S] (S ⊗[R] N) →ₗ[S] P := α.hom
  let β₀ : (S ⊗[R] M) ⊗[S] (S ⊗[R] N) →ₗ[S] P := β.hom
  refine ModuleCat.hom_ext (TensorProduct.ext' (g := α₀) (h := β₀) fun x y => ?_)
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | tmul t n => exact h s t m n

open ModuleCat.MonoidalCategory

/-- Compatibility name for Mathlib's monoidal extension-of-scalars instance. -/
noncomputable abbrev monoidal : (E).Monoidal := inferInstance

/-- The tensorator of the monoidal structure on `S ⊗_R -` is `μ_{X,Y}`. -/
lemma μ_eq (X Y : ModuleCat.{u} R) : Functor.LaxMonoidal.μ (E) X Y = (muIso f X Y).hom := rfl

/-- Extension of scalars is a braided monoidal functor. -/
noncomputable instance braided : (E).Braided where
  braided X Y := by
    rw [μ_eq, μ_eq]
    refine ext₂ f fun s t m n => ?_
    exact congr(((E).map (β_ X Y).hom).hom $(muIso_hom_tmul f X Y s t m n)).trans
      ((congrArg (fun c : S => c ⊗ₜ[R,f] (n ⊗ₜ[R] m)) (mul_comm s t)).trans
        (muIso_hom_tmul f Y X t s n m).symm)

end UlmerBialgebras.Paper.Loc
