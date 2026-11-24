module

public import UlmerBialgebras.Basic.HomCat
public import UlmerBialgebras.Kan.Kan

/-!
# Kan extensions along an identity in `CAT`

In `CAT`, a right (left) extension of `e` along an identity functor is a right (left) Kan extension
exactly when its counit (unit) is invertible. The trivial extension `(e, 𝟙)` is one, and every
1-cell preserves them. (The proofs use that `𝟭 X ⋙ e` is `e` by definition, which holds in `CAT`
but not in every strict 2-category.)

## Main results

* `UlmerBialgebras.RightExt.isTerminalOfIsIsoCounit`,
  `UlmerBialgebras.LeftExt.isInitialOfIsIsoUnit`: an extension along an identity with invertible
  (co)unit is a Kan extension.
* `UlmerBialgebras.RightExt.isIso_counit_of_isTerminal`,
  `UlmerBialgebras.LeftExt.isIso_unit_of_isInitial`: the converse.
* `UlmerBialgebras.preservesRightKan_id`, `UlmerBialgebras.preservesLeftKan_id`: every 1-cell
  preserves the Kan extensions along an identity.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 4.2–4.4
-/

@[expose] public section

universe u v

namespace UlmerBialgebras

open CategoryTheory Limits

variable {X c : Cat.{v, u}} {e : X ⟶ c}

/-- A right extension along an identity whose counit is invertible is a right Kan extension. -/
noncomputable def RightExt.isTerminalOfIsIsoCounit (R : RightExt (𝟙 X) e) [IsIso R.counit] :
    IsTerminal R :=
  IsTerminal.ofUniqueHom
    -- Along `𝟙 X` the condition on a morphism is a plain composite, up to unfolding.
    (fun R' => RightExt.homMk ((R'.counit : R'.ext ⟶ e) ≫ inv R.counit)
      ((Category.assoc _ _ _).trans (((R'.counit : R'.ext ⟶ e) ≫= IsIso.inv_hom_id R.counit).trans
        (Category.comp_id _))))
    (fun R' m => RightExt.hom_ext (by
      have h : RightExt.homCell m ≫ R.counit = R'.counit := RightExt.w m
      exact (IsIso.eq_comp_inv _).2 h))

/-- A left extension along an identity whose unit is invertible is a left Kan extension. -/
noncomputable def LeftExt.isInitialOfIsIsoUnit (L : LeftExt (𝟙 X) e) [IsIso L.unit] :
    IsInitial L :=
  IsInitial.ofUniqueHom
    (fun L' => LeftExt.homMk (inv L.unit ≫ (L'.unit : e ⟶ L'.ext))
      ((Category.assoc _ _ _).symm.trans ((IsIso.hom_inv_id L.unit =≫ (L'.unit : e ⟶ L'.ext)).trans
        (Category.id_comp _))))
    (fun L' m => LeftExt.hom_ext (by
      have h : L.unit ≫ LeftExt.homCell m = L'.unit := LeftExt.w m
      exact (IsIso.eq_inv_comp _).2 h))

/-- The trivial right extension `(e, 𝟙)` along an identity. -/
def RightExt.idExt (e : X ⟶ c) : RightExt (𝟙 X) e := RightExt.mk e (𝟙 e)

/-- The trivial left extension `(e, 𝟙)` along an identity. -/
def LeftExt.idExt (e : X ⟶ c) : LeftExt (𝟙 X) e := LeftExt.mk e (𝟙 e)

/-- The counit of a right Kan extension along an identity is invertible. -/
lemma RightExt.isIso_counit_of_isTerminal {R : RightExt (𝟙 X) e} (hR : IsTerminal R) :
    IsIso R.counit := by
  have h₀ : IsTerminal (RightExt.idExt e) := by
    have : IsIso (RightExt.idExt e).counit := inferInstanceAs (IsIso (𝟙 e))
    exact RightExt.isTerminalOfIsIsoCounit _
  let i := hR.uniqueUpToIso h₀
  have hom : (RightExt.homCell i.hom) = R.counit :=
      (Category.comp_id _).symm.trans (RightExt.w i.hom)
  have h1 : (RightExt.homCell i.hom) ≫ (RightExt.homCell i.inv) = 𝟙 _ :=
      RightExt.hom_ext_iff.mp i.hom_inv_id
  have h2 : (RightExt.homCell i.inv) ≫ (RightExt.homCell i.hom) = 𝟙 _ :=
      RightExt.hom_ext_iff.mp i.inv_hom_id
  rw [← hom]
  exact ⟨(RightExt.homCell i.inv), h1, h2⟩

/-- The unit of a left Kan extension along an identity is invertible. -/
lemma LeftExt.isIso_unit_of_isInitial {L : LeftExt (𝟙 X) e} (hL : IsInitial L) : IsIso L.unit := by
  have h₀ : IsInitial (LeftExt.idExt e) := by
    have : IsIso (LeftExt.idExt e).unit := inferInstanceAs (IsIso (𝟙 e))
    exact LeftExt.isInitialOfIsIsoUnit _
  let i := h₀.uniqueUpToIso hL
  have hom : (LeftExt.homCell i.hom) = L.unit := (Category.id_comp _).symm.trans (LeftExt.w i.hom)
  have h1 : (LeftExt.homCell i.hom) ≫ (LeftExt.homCell i.inv) = 𝟙 _ :=
      LeftExt.hom_ext_iff.mp i.hom_inv_id
  have h2 : (LeftExt.homCell i.inv) ≫ (LeftExt.homCell i.hom) = 𝟙 _ :=
      LeftExt.hom_ext_iff.mp i.inv_hom_id
  rw [← hom]
  exact ⟨(LeftExt.homCell i.inv), h1, h2⟩

/-- In `CAT`, every 1-cell preserves the right Kan extensions along an identity. -/
lemma preservesRightKan_id {c' : Cat.{v, u}} (g : c ⟶ c') : PreservesRightKan (𝟙 X) e g := by
  rintro R ⟨hR⟩
  have := RightExt.isIso_counit_of_isTerminal hR
  have : IsIso ((RightExt.push (𝟙 X) e g).obj R).counit :=
    inferInstanceAs (IsIso (eqToHom _ ≫ (postcomp X g).map R.counit))
  exact ⟨RightExt.isTerminalOfIsIsoCounit _⟩

/-- In `CAT`, every 1-cell preserves the left Kan extensions along an identity. -/
lemma preservesLeftKan_id {c' : Cat.{v, u}} (f : c ⟶ c') : PreservesLeftKan (𝟙 X) e f := by
  rintro L ⟨hL⟩
  have := LeftExt.isIso_unit_of_isInitial hL
  have : IsIso ((LeftExt.push (𝟙 X) e f).obj L).unit :=
    inferInstanceAs (IsIso ((postcomp X f).map L.unit ≫ eqToHom _))
  exact ⟨LeftExt.isInitialOfIsIsoUnit _⟩

end UlmerBialgebras
