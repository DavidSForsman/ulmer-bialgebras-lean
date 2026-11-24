module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Proofs.Sec4.Sec4
public import UlmerBialgebras.Proofs.Sec6.KernelPairs
public import UlmerBialgebras.Density.ACotensorAdjoint
public import UlmerBialgebras.Density.ATensorAdjoint
public import UlmerBialgebras.Density.CellCompatDense
public import UlmerBialgebras.Monadicity.LPAdjoint
public import UlmerBialgebras.Monadicity.AccAdjoint
public import Foundations.CategoryTheory.Presentable.LPComplete
public import UlmerBialgebras.Density.AComplete
public import UlmerBialgebras.Density.ALocPres
public import UlmerBialgebras.Proofs.Sec5.BialgDatumCo
public import UlmerBialgebras.Proofs.Sec5.CoMonadic
public import UlmerBialgebras.Monadicity.RepresentableMonadicity
public import UlmerBialgebras.Proofs.Sec5.ThmSevenFourRoute

/-!
# Helper lemmas for Section 7: Bi-density, Adjoint Lifting, and Bialgebraic Data

Theorem 7.4 and its dual (lifting of `A`-adjoints along a bi-dense class `A`), together with the
Kan extension, accessibility and (co)completeness properties of `u_B` and the 2-dimensional Beck
criteria used for Corollary 7.5 and Theorems 7.6 and 7.7. Comonadicity of `u_B` is derived from
monadicity of the forgetful 1-cell of the dual datum in `K^co`.

## Main results

* `UlmerBialgebras.Paper.exists_leftAdjoint_of_isARightAdjoint`: for a bi-dense `A`, if `d` has and
  `g : d ⟶ c` preserves right Kan extensions along 1-cells between objects of `A`, and `g` is an
  `A`-right adjoint, then `g` has a left adjoint (Theorem 7.4).
* `UlmerBialgebras.Paper.exists_rightAdjoint_of_isALeftAdjoint`: the dual statement for left Kan
  extensions and `A`-left adjoints: `g` has a right adjoint.
* `UlmerBialgebras.Paper.BialgDatum.uB_isAComplete_and_continuous`: if `B.c` is `A`-complete and
  `B.g`, `B.g'` are `A`-continuous, then `E.pt` is `A`-complete and `u_B` is `A`-continuous.
* `UlmerBialgebras.Paper.BialgDatum.isMonadic2_uB_of_isARightAdjoint`: if `B.g` and `B.g'` are right
  adjoints, `B.c` has right Kan extensions along `A`, `A` is bi-dense and `u_B` is an `A`-right
  adjoint, then `u_B` is monadic.
* `UlmerBialgebras.Paper.BialgDatum.isComonadic2_uB_of_twoAdj`: if `u_B` has a right adjoint, it is
  comonadic.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 7
  (Definition 7.1, Theorem 7.4, Corollary 7.5, Theorems 7.6 and 7.7) and Lemma 5.2
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w w₀

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## 1. Cell-compatibility of adjoint families and Bi-dense Adjoint Lifting -/

/-- Every `ALeftAdjointFamily` is automatically cell-compatible (`PsFamily.nat₂`),
because the mate is uniquely determined by the unit, which satisfies the interchange law. -/
theorem ALeftAdjointFamily.isCellCompatible {A : ObjectProperty Obj} {c d : Obj} {g : d ⟶ c}
    (F : ALeftAdjointFamily A g) : F.toAHomFamily.IsCellCompatible := by
  intro x y hx hy u u' δ m
  refine ((F.adj hx).homEquiv (u ≫ m) (u' ≫ (F.fn hy).obj m)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [postcomp_map, Bicategory.comp_whiskerRight]
  have hnat_u' := F.unit_nat hx hy u' m
  have hnat_u := F.unit_nat hx hy u m
  have hunit_nat : (F.adj hx).unit.app (u ≫ m) ≫ ((F.fn hx).map (δ ▷ m) ▷ g)
      = (δ ▷ m) ≫ (F.adj hx).unit.app (u' ≫ m) := by
    simpa only [Functor.id_map, Functor.comp_map, postcomp_map] using
      ((F.adj hx).unit.naturality (δ ▷ m)).symm
  rw [← Category.assoc, hunit_nat, Category.assoc, hnat_u']
  rw [reassoc_of% hnat_u]
  rw [Bicategory.Strict.whiskerRight_comp' δ ((F.fn hy).obj m) g]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (reassoc_of% (Eq.symm <| Bicategory.whisker_exchange δ ((F.adj hy).unit.app m))) _

/-- Every `ARightAdjointFamily` is automatically cell-compatible (`PsFamily.nat₂`),
because the mate is uniquely determined by the counit, which satisfies the interchange law. -/
theorem ARightAdjointFamily.isCellCompatible {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d}
    (F : ARightAdjointFamily A f) : F.toAHomFamily.IsCellCompatible := by
  intro x y hx hy u u' δ m
  rw [← cancel_epi ((F.nat hx hy u).inv.app m), Iso.inv_hom_id_app_assoc,
    ← cancel_mono ((F.nat hx hy u').inv.app m), Category.assoc, Category.assoc,
    Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, precomp_obj, Category.comp_id]
  refine ((F.adj hx).homEquiv (u ≫ (F.fn hy).obj m) (u' ≫ m)).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [postcomp_map, Bicategory.comp_whiskerRight, Category.assoc]
  have hnat_u' := F.counit_nat hx hy u' m
  have hnat_u := F.counit_nat hx hy u m
  have hcounit_nat : ((F.fn hx).map (δ ▷ m) ▷ f) ≫ (F.adj hx).counit.app (u' ≫ m)
      = (F.adj hx).counit.app (u ≫ m) ≫ (δ ▷ m) := by
    simpa only [Functor.comp_map, Functor.id_map, postcomp_map] using
      (F.adj hx).counit.naturality (δ ▷ m)
  rw [hnat_u', hcounit_nat, reassoc_of% hnat_u, Bicategory.Strict.whiskerRight_comp' δ ((F.fn
    hy).obj m) f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (eqToHom _ ≫= Bicategory.whisker_exchange δ ((F.adj hy).counit.app m))

/-- A compatible family of left adjoints gives a `Paper.PsFamily`. -/
def ALeftAdjointFamily.toPsFamily {A : ObjectProperty Obj} {c d : Obj} {g : d ⟶ c}
    (F : ALeftAdjointFamily A g) : Paper.PsFamily A c d where
  toAHomFamily := F.toAHomFamily
  nat₂ := F.isCellCompatible

/-- A compatible family of right adjoints gives a `Paper.PsFamily`. -/
def ARightAdjointFamily.toPsFamily {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d}
    (F : ARightAdjointFamily A f) : Paper.PsFamily A d c where
  toAHomFamily := F.toAHomFamily
  nat₂ := F.isCellCompatible

/-- Bi-dense version of the `A`-accessible adjoint functor theorem for left adjoints
(`ALeftAdjointFamily.exists_twoAdj_left_of_representation`). -/
theorem exists_twoAdj_left_of_isBiDense {A : ObjectProperty Obj} (hA : Paper.IsBiDense A) {c d :
  Obj}
    {g : d ⟶ c} (F : ALeftAdjointFamily A g) :
    ∃ f : c ⟶ d, Nonempty (TwoAdj f g) := by
  obtain ⟨P⟩ := hA.hom F.toPsFamily
  exact ⟨P.g, F.exists_twoAdj_left_of_representation P hA.cell⟩

/-- Bi-dense version of the `A`-accessible adjoint functor theorem
(`exists_twoAdj_of_isACellDense_of_representation`). -/
theorem exists_twoAdj_of_isBiDense {A : ObjectProperty Obj} (hA : Paper.IsBiDense A) {c d : Obj}
    {f : c ⟶ d} (F : ARightAdjointFamily A f) :
    ∃ g : d ⟶ c, Nonempty (TwoAdj f g) := by
  obtain ⟨P⟩ := hA.hom F.toPsFamily
  exact ⟨P.g, exists_twoAdj_of_isACellDense_of_representation hA.cell F P⟩

/-! ## 2. Bridges between Kan extensions and (Co)tensors -/

/-- Terminal objects in `RightExt r m` are universal cotensor arrows. -/
lemma isCotensorUniv_of_isTerminal {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c}
    (R : RightExt r m) (hR : IsTerminal R) : IsCotensorUniv r R.counit := by
  intro n k
  refine ⟨RightExt.homCell (hR.from (RightExt.mk n k)),
    (RightExt.w (hR.from (RightExt.mk n k))).trans (RightExt.mk_counit _ _), fun β hβ => ?_⟩
  have h := congr(RightExt.homCell
    $(hR.hom_ext (RightExt.homMk (L := RightExt.mk n k) (L' := R) β (by simpa using hβ))
      (hR.from (RightExt.mk n k))))
  simpa using h

/-- Universal cotensor arrows give terminal objects in `RightExt r m`. -/
noncomputable def isTerminalOfIsCotensorUniv {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c}
    {t : y ⟶ c} {ε : r ≫ t ⟶ m} (hε : IsCotensorUniv r ε) :
    IsTerminal (RightExt.mk t ε) :=
  IsTerminal.ofUniqueHom
    (fun S => RightExt.homMk (hε.lift S.counit) (by rw [RightExt.mk_counit]; exact hε.fac S.counit))
    (fun _ μ => RightExt.hom_ext (by simpa using hε.lift_unique (by simpa using RightExt.w μ)))

/-- `HasARightKan` implies `IsACotensored`. -/
lemma isACotensored_of_hasARightKan {A : ObjectProperty Obj} {d : Obj} (hd : Paper.HasARightKan A
  d) :
    IsACotensored A d := by
  intro x y hx hy r m
  obtain ⟨R, ⟨hR⟩⟩ := hd hx hy r m
  exact ⟨R.ext, R.counit, isCotensorUniv_of_isTerminal R hR⟩

/-- Preserving right Kan extensions along 1-cells of `A` gives `RespectsACotensors`. -/
lemma respectsACotensors_of_preservesRightKan {A : ObjectProperty Obj} {c d : Obj} {g : d ⟶ c}
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesRightKan k e g) :
    RespectsACotensors A g := by
  intro x y hx hy r m t ε hε
  obtain ⟨hR'⟩ := hg hx hy r m (RightExt.mk t ε) ⟨isTerminalOfIsCotensorUniv hε⟩
  exact isCotensorUniv_of_isTerminal ((RightExt.push r m g).obj (RightExt.mk t ε)) hR'

/-- Initial objects in `LeftExt r m` are universal tensor arrows. -/
lemma isTensorUniv_of_isInitial {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c}
    (L : LeftExt r m) (hL : IsInitial L) : IsTensorUniv r L.unit := by
  intro n k
  refine ⟨LeftExt.homCell (hL.to (LeftExt.mk n k)),
    (LeftExt.w (hL.to (LeftExt.mk n k))).trans (LeftExt.mk_unit _ _), fun β hβ => ?_⟩
  have h := congr(LeftExt.homCell
    $(hL.hom_ext (LeftExt.homMk (L := L) (L' := LeftExt.mk n k) β (by simpa using hβ))
      (hL.to (LeftExt.mk n k))))
  simpa using h

/-- Universal tensor arrows give initial objects in `LeftExt r m`. -/
noncomputable def isInitialOfIsTensorUniv {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c}
    {t : y ⟶ c} {η : m ⟶ r ≫ t} (hη : IsTensorUniv r η) :
    IsInitial (LeftExt.mk t η) :=
  IsInitial.ofUniqueHom
    (fun S => LeftExt.homMk (hη.desc S.unit) (by rw [LeftExt.mk_unit]; exact hη.fac S.unit))
    (fun _ μ => LeftExt.hom_ext (by simpa using hη.desc_unique (by simpa using LeftExt.w μ)))

/-- `HasALeftKan` implies `IsATensored`. -/
lemma isATensored_of_hasALeftKan {A : ObjectProperty Obj} {d : Obj} (hd : Paper.HasALeftKan A d) :
    IsATensored A d := by
  intro x y hx hy r m
  obtain ⟨L, ⟨hL⟩⟩ := hd hx hy r m
  exact ⟨L.ext, L.unit, isTensorUniv_of_isInitial L hL⟩

/-- Preserving left Kan extensions along 1-cells of `A` gives `RespectsATensors`. -/
lemma respectsATensors_of_preservesLeftKan {A : ObjectProperty Obj} {c d : Obj} {f : d ⟶ c}
    (hf : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesLeftKan k e f) :
    RespectsATensors A f := by
  intro x y hx hy r m t η hη
  obtain ⟨hL'⟩ := hf hx hy r m (LeftExt.mk t η) ⟨isInitialOfIsTensorUniv hη⟩
  exact isTensorUniv_of_isInitial ((LeftExt.push r m f).obj (LeftExt.mk t η)) hL'

/-! ## 3. Right Adjoints Preserve Right Kan Extensions -/

/-- Compatibility of `TwoAdj.postcompAdj` with `RightExt.push`. -/
lemma postcompAdj_rightExt_eq {c d : Obj} {l : c ⟶ d} {r : d ⟶ c} (Adj : TwoAdj l r)
    {I X : Obj} (k : I ⟶ X) {e : I ⟶ d} (R : RightExt k e)
    (s : X ⟶ c) (α : s ≫ l ⟶ R.ext) :
    (k ◁ (Adj.postcompAdj X).homEquiv s R.ext α) ≫
        (eqToHom (Category.assoc k R.ext r).symm ≫ (R.counit ▷ r))
      = (Adj.postcompAdj I).homEquiv (k ≫ s) e
          (eqToHom (Category.assoc k s l) ≫ (k ◁ α) ≫ R.counit) := by
  have hunit : (k ◁ (Adj.postcompAdj X).unit.app s) ≫ eqToHom (Category.assoc k (s ≫ l) r).symm
      = (Adj.postcompAdj I).unit.app (k ≫ s) ≫ (eqToHom (Category.assoc k s l) ▷ r) := by
    simp only [TwoAdj.postcompAdj, TwoAdj.postcompUnit_app, Bicategory.whiskerLeft_comp,
      Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight, Category.assoc]
    rw [Bicategory.Strict.comp_whiskerLeft' k s Adj.unit']
    simp
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [postcomp_map, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Bicategory.eqToHom_whiskerRight,
    Category.assoc]
  rw [Bicategory.Strict.whisker_assoc k α r]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% hunit]
  simp

/-- Right adjoints in a 2-category preserve all right Kan extensions. -/
theorem preservesRightKan_of_twoAdj {c d : Obj} {l : c ⟶ d} {r : d ⟶ c} (Adj : TwoAdj l r)
    {I X : Obj} (k : I ⟶ X) (e : I ⟶ d) : PreservesRightKan k e r := by
  intro R ⟨hR⟩
  -- A right extension along `e ≫ r` gives one along `e` by the adjunction; `R` is terminal.
  let T : ∀ S : RightExt k (e ≫ r), RightExt k e := fun S =>
    RightExt.mk (S.ext ≫ l) (eqToHom (Category.assoc k S.ext l).symm ≫
      ((Adj.postcompAdj I).homEquiv (k ≫ S.ext) e).symm S.counit)
  refine ⟨IsTerminal.ofUniqueHom
    (fun S => RightExt.homMk ((Adj.postcompAdj X).homEquiv S.ext R.ext
      (RightExt.homCell (hR.from (T S)))) ?_)
    (fun S μ => RightExt.hom_ext ?_)⟩
  · simp only [RightExt.push_obj_ext, RightExt.push_obj_counit]
    rw [postcompAdj_rightExt_eq Adj k R S.ext]
    have hfac := (RightExt.w (hR.from (T S))).trans (RightExt.mk_counit _ _)
    rw [hfac, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  -- Uniqueness: transpose along the adjunction and use that `R` is terminal.
  · refine ((Adj.postcompAdj X).homEquiv S.ext R.ext).symm.injective ?_
    dsimp only [RightExt.homCell_homMk]
    rw [Equiv.symm_apply_apply]
    have hμ : (k ◁ (Adj.postcompAdj X).homEquiv S.ext R.ext
        (((Adj.postcompAdj X).homEquiv S.ext R.ext).symm (RightExt.homCell μ))) ≫
        (eqToHom (Category.assoc k R.ext r).symm ≫ (R.counit ▷ r)) = S.counit := by
      rw [Equiv.apply_symm_apply]
      simpa using RightExt.w μ
    rw [postcompAdj_rightExt_eq Adj k R S.ext] at hμ
    have hμ' := congrArg ((Adj.postcompAdj I).homEquiv (k ≫ S.ext) e).symm hμ
    rw [Equiv.symm_apply_apply] at hμ'
    have hα : (k ◁ (((Adj.postcompAdj X).homEquiv S.ext R.ext).symm (RightExt.homCell μ))) ≫
        R.counit = eqToHom (Category.assoc k S.ext l).symm ≫
          ((Adj.postcompAdj I).homEquiv (k ≫ S.ext) e).symm S.counit := by
      rw [← hμ', eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have h := congrArg RightExt.homCell (hR.hom_ext
      (RightExt.homMk (L := T S) (L' := R)
        (((Adj.postcompAdj X).homEquiv S.ext R.ext).symm (RightExt.homCell μ))
        (by simpa [T] using hα))
      (hR.from (T S)))
    simpa using h

/-! ## 4. Theorem 7.4 and its dual -/

namespace Paper

/-- **Theorem 7.4** ([forsman2026syntactic]): if `A` is bi-dense, `d` has and `g` preserves all
right Kan extensions along 1-cells of `𝒜`, and `g` is an `A`-right adjoint, then `g` is a right
adjoint. -/
theorem exists_leftAdjoint_of_isARightAdjoint (A : ObjectProperty Obj) (hA : IsBiDense A) {c d :
  Obj}
    (g : d ⟶ c)
    (hd : HasARightKan A d)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesRightKan k e g)
    (hadj : IsARightAdjoint A g) :
    ∃ f : c ⟶ d, Nonempty (TwoAdj f g) :=
  let ⟨F⟩ := nonempty_aLeftAdjointFamily hadj (isACotensored_of_hasARightKan hd)
    (respectsACotensors_of_preservesRightKan hg)
  exists_twoAdj_left_of_isBiDense hA F

/-- Dual of Theorem 7.4: if `A` is bi-dense, `d` has and `g` preserves all left Kan extensions
along 1-cells of `𝒜`, and `g` is an `A`-left adjoint, then `g` is a left adjoint. -/
theorem exists_rightAdjoint_of_isALeftAdjoint (A : ObjectProperty Obj) (hA : IsBiDense A) {c d :
  Obj}
    (g : d ⟶ c)
    (hd : HasALeftKan A d)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesLeftKan k e g)
    (hadj : IsALeftAdjoint A g) :
    ∃ h : c ⟶ d, Nonempty (TwoAdj g h) :=
  exists_twoAdj_of_isBiDense hA
    (aRightAdjointFamilyOfTensors hadj
      (isATensored_of_hasALeftKan hd)
      (respectsATensors_of_preservesLeftKan hg))

/-! ## 5. Bialgebraic Datum Properties: Kan Extensions, Accessibility, and (Co)completeness -/

namespace BialgDatum

variable (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)

/-- If `B.g` and `B.g'` preserve right Kan extensions along `k`, then `B.uB E` strictly
creates them. -/
theorem uB_strictlyCreatesRightKan_of_preserves {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hg : PreservesRightKan k (d ≫ B.uB E) B.g)
    (hg' : PreservesRightKan k (d ≫ B.uB E) B.g') :
    StrictlyCreatesRightKan k d (B.uB E) :=
  cor_4_8_right B E k d hg (fun R hR => subterminal_of_isTerminal (hg' R hR).some)

/-- If `B.f` and `B.f'` preserve left Kan extensions along `k`, then `B.uB E` strictly
creates them. -/
theorem uB_strictlyCreatesLeftKan_of_preserves {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hf : PreservesLeftKan k (d ≫ B.uB E) B.f)
    (hf' : PreservesLeftKan k (d ≫ B.uB E) B.f') :
    StrictlyCreatesLeftKan k d (B.uB E) :=
  cor_4_8_left B E k d hf (fun L hL => quotientInitial_of_isInitial (hf' L hL).some)

/-- If `B.c` has `HasARightKan A` and `B.g, B.g'` preserve right Kan extensions along 1-cells of
`A`, then `E.pt` has `HasARightKan A` and `B.uB E` preserves them. -/
theorem uB_hasAndPreservesARightKan {A : ObjectProperty Obj} (hc : HasARightKan A B.c)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c), PreservesRightKan k e B.g)
    (hg' : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c), PreservesRightKan k e B.g') :
    HasARightKan A E.pt ∧
      ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ E.pt),
        PreservesRightKan k e (B.uB E) := by
  refine ⟨fun i x hi hx k d => ?_, fun i x hi hx k d => ?_⟩
  · obtain ⟨R₀, hR₀⟩ := hc hi hx k (d ≫ B.uB E)
    have hcr := uB_strictlyCreatesRightKan_of_preserves B E k d
      (hg hi hx k _) (hg' hi hx k _)
    obtain ⟨⟨R, hRR, -⟩, hterm⟩ := hcr R₀ hR₀
    exact ⟨R, hterm R hRR⟩
  · obtain ⟨R₀, hR₀⟩ := hc hi hx k (d ≫ B.uB E)
    have hcr := uB_strictlyCreatesRightKan_of_preserves B E k d
      (hg hi hx k _) (hg' hi hx k _)
    exact preservesTerminal_of_strictlyCreatesTerminal _ hcr hR₀

/-- If `B.c` has `HasALeftKan A` and `B.f, B.f'` preserve left Kan extensions along 1-cells of
`A`, then `E.pt` has `HasALeftKan A` and `B.uB E` preserves them. -/
theorem uB_hasAndPreservesALeftKan {A : ObjectProperty Obj} (hc : HasALeftKan A B.c)
    (hf : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c), PreservesLeftKan k e B.f)
    (hf' : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c), PreservesLeftKan k e B.f') :
    HasALeftKan A E.pt ∧
      ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ E.pt),
        PreservesLeftKan k e (B.uB E) := by
  refine ⟨fun i x hi hx k d => ?_, fun i x hi hx k d => ?_⟩
  · obtain ⟨L₀, hL₀⟩ := hc hi hx k (d ≫ B.uB E)
    have hcr := uB_strictlyCreatesLeftKan_of_preserves B E k d
      (hf hi hx k _) (hf' hi hx k _)
    obtain ⟨⟨L, hLL, -⟩, hinit⟩ := hcr L₀ hL₀
    exact ⟨L, hinit L hLL⟩
  · obtain ⟨L₀, hL₀⟩ := hc hi hx k (d ≫ B.uB E)
    have hcr := uB_strictlyCreatesLeftKan_of_preserves B E k d
      (hf hi hx k _) (hf' hi hx k _)
    exact preservesInitial_of_strictlyCreatesInitial _ hcr hL₀

/-- Accessibility of `E.pt` and `B.uB E` when `f, f', g, g'` are `A`-accessible (only the
hom-category part of `IsAAccessibleMor'` is needed). -/
theorem uB_isAAccessibleMor' {A : ObjectProperty Obj}
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    IsAAccessibleMor'.{w₀} A (B.uB E) ∧ IsAAccessibleObj.{w₀} A E.pt := by
  -- Each represented hom-category is accessible and `postcomp a (uB E)` is accessible.
  have key : ∀ ⦃a : Obj⦄, A a → IsAccessibleCategory.{w₀} (a ⟶ E.pt) ∧
      Functor.IsAccessible.{w₀} (postcomp a (B.uB E)) := by
    intro a ha
    have := (hf ha).1
    have := (hf ha).2.1
    have := (hf ha).2.2
    have := (hg ha).2.2
    have := (hf' ha).2.1
    have := (hf' ha).2.2
    have := (hg' ha).2.2
    have : IsAccessibleCategory.{w₀} (Ins (postcomp a B.f) (postcomp a B.g)) :=
      UlmerBialgebras.Ins.isAccessibleCategory
    have : IsAccessibleCategory.{w₀} (a ⟶ B.ins.pt) :=
      isAccessibleCategory_of_isEquivalence' (Inserter.homFunctor B.ins a)
    have : Functor.IsAccessible.{w₀} (Ins.forget (postcomp a B.f) (postcomp a B.g)) :=
      UlmerBialgebras.Ins.forget_isAccessible
    have : Functor.IsAccessible.{w₀} (Inserter.homFunctor B.ins a ⋙
        Ins.forget (postcomp a B.f) (postcomp a B.g)) := inferInstance
    have hu : Functor.IsAccessible.{w₀} (postcomp a B.ins.u) :=
      isAccessible_of_eq (Inserter.homFunctor_comp_forget B.ins a)
    have : Functor.IsAccessible.{w₀} (postcomp a (B.ins.u ≫ B.f')) :=
      isAccessible_of_eq (postcomp_comp₁ a B.ins.u B.f').symm
    have : Functor.IsAccessible.{w₀} (postcomp a (B.ins.u ≫ B.g')) :=
      isAccessible_of_eq (postcomp_comp₁ a B.ins.u B.g').symm
    have : IsAccessibleCategory.{w₀} (Equif (postcompNat a B.α) (postcompNat a B.β)) :=
      UlmerBialgebras.Equif.isAccessibleCategory
    have : IsAccessibleCategory.{w₀} (a ⟶ E.pt) :=
      isAccessibleCategory_of_isEquivalence' (Equifier.homFunctor E a)
    have : Functor.IsAccessible.{w₀} (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
      UlmerBialgebras.Equif.forget_isAccessible
    have : Functor.IsAccessible.{w₀} (Equifier.homFunctor E a ⋙
        Equif.forget (postcompNat a B.α) (postcompNat a B.β)) := inferInstance
    have : Functor.IsAccessible.{w₀} (postcomp a E.e) :=
      isAccessible_of_eq (Equifier.homFunctor_comp_forget E a)
    exact ⟨inferInstance, isAccessible_of_eq (postcomp_comp₁ a E.e B.ins.u).symm⟩
  exact ⟨fun a ha => ⟨(key ha).1, (hf ha).1, (key ha).2⟩, fun a ha => (key ha).1⟩

/-- `E.pt` is `A`-complete and `B.uB E` is `A`-continuous when `B.c` is `A`-complete and
`B.g, B.g'` are `A`-continuous. -/
theorem uB_isAComplete_and_continuous {A : ObjectProperty Obj}
    (hc : IsAComplete.{w₀} A B.c) (hg : IsAContinuous.{w₀} A B.g)
    (hg' : IsAContinuous.{w₀} A B.g') :
    IsAComplete.{w₀} A E.pt ∧ IsAContinuous.{w₀} A (B.uB E) := by
  -- Limits in the inserter and continuity of its 1-cells, then of the equifier.
  have hins_lim : ∀ ⦃a : Obj⦄, A a → HasLimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) := by
    intro a ha
    have := hc ha
    have := hg ha
    refine ⟨fun J _ => ?_⟩
    have : HasLimitsOfShape J (Ins (postcomp a B.f) (postcomp a B.g)) := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence (Inserter.homFunctor B.ins a)
  have hu_cont : UlmerBialgebras.IsAContinuousMor.{w₀} A B.ins.u := by
    intro a ha
    have := hc ha
    have := hg ha
    refine ⟨fun {J} _ => ?_⟩
    have : PreservesLimitsOfShape J (Ins.forget (postcomp a B.f) (postcomp a B.g)) :=
      inferInstance
    rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  have hug'_cont : UlmerBialgebras.IsAContinuousMor.{w₀} A (B.ins.u ≫ B.g') := hu_cont.comp hg'
  -- The equifier is `A`-complete and `e` is `A`-continuous; compose.
  have hE_lim : IsAComplete.{w₀} A E.pt := by
    intro a ha
    have := hins_lim ha
    have := hug'_cont ha
    refine ⟨fun J _ => ?_⟩
    have : HasLimitsOfShape J (Equif (postcompNat a B.α) (postcompNat a B.β)) := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence (Equifier.homFunctor E a)
  have he_cont : UlmerBialgebras.IsAContinuousMor.{w₀} A E.e := by
    intro a ha
    have := hins_lim ha
    have := hug'_cont ha
    refine ⟨fun {J} _ => ?_⟩
    have : PreservesLimitsOfShape J (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
      inferInstance
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  exact ⟨hE_lim, he_cont.comp hu_cont⟩

/-- `E.pt` is `A`-cocomplete and `B.uB E` is `A`-cocontinuous when `B.c` is `A`-cocomplete and
`B.f, B.f'` are `A`-cocontinuous. -/
theorem uB_isACocomplete_and_cocontinuous {A : ObjectProperty Obj}
    (hc : IsACocomplete.{w₀} A B.c) (hf : IsACocontinuous.{w₀} A B.f)
    (hf' : IsACocontinuous.{w₀} A B.f') :
    IsACocomplete.{w₀} A E.pt ∧ IsACocontinuous.{w₀} A (B.uB E) := by
  -- Colimits in the inserter and cocontinuity of its 1-cells, then of the equifier.
  have hins_colim : ∀ ⦃a : Obj⦄, A a → HasColimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) := by
    intro a ha
    have := hc ha
    have := hf ha
    refine ⟨fun J _ => ?_⟩
    have : HasColimitsOfShape J (Ins (postcomp a B.f) (postcomp a B.g)) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence (Inserter.homFunctor B.ins a)
  have hu_cocont : UlmerBialgebras.IsACocontinuousMor.{w₀} A B.ins.u := by
    intro a ha
    have := hc ha
    have := hf ha
    refine ⟨fun {J} _ => ?_⟩
    have : PreservesColimitsOfShape J (Ins.forget (postcomp a B.f) (postcomp a B.g)) :=
      inferInstance
    rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  have huf'_cocont : UlmerBialgebras.IsACocontinuousMor.{w₀} A (B.ins.u ≫ B.f') :=
    hu_cocont.comp hf'
  -- The equifier is `A`-cocomplete and `e` is `A`-cocontinuous; compose.
  have hE_colim : IsACocomplete.{w₀} A E.pt := by
    intro a ha
    have := hins_colim ha
    have := huf'_cocont ha
    refine ⟨fun J _ => ?_⟩
    have := equifProp_isClosedUnderColimitsOfShape (postcompNat a B.α) (postcompNat a B.β) J
    have : HasColimitsOfShape J (Equif (postcompNat a B.α) (postcompNat a B.β)) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence (Equifier.homFunctor E a)
  have he_cocont : UlmerBialgebras.IsACocontinuousMor.{w₀} A E.e := by
    intro a ha
    have := hins_colim ha
    have := huf'_cocont ha
    refine ⟨fun {J} _ => ?_⟩
    have := equifProp_isClosedUnderColimitsOfShape (postcompNat a B.α) (postcompNat a B.β) J
    have : PreservesColimitsOfShape J (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
      inferInstance
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  exact ⟨hE_colim, he_cocont.comp hu_cocont⟩

/-! ## 6. Beck's Monadicity and Comonadicity Criteria for `B.uB E` -/

/-- The forgetful functor `K(x, u_B)` written as the composite
`postcomp x E.e ⋙ postcomp x B.ins.u`. -/
def uBHomForget (x : Obj) : (x ⟶ E.pt) ⥤ (x ⟶ B.c) :=
  postcomp x E.e ⋙ postcomp x B.ins.u

/-- `uBHomForget E x` is `K(x, u_B) = postcomp x (e ≫ u')`. -/
lemma uBHomForget_eq (x : Obj) : B.uBHomForget E x = postcomp x (B.uB E) :=
  (postcomp_comp₁ x E.e B.ins.u).symm

/-- `K(x, e)` reflects isomorphisms, since it is an equivalence onto the equifier of
`K(x, α), K(x, β)` followed by the (conservative) forgetful functor of the equifier. -/
instance postcompE_reflectsIsomorphisms (x : Obj) :
    (postcomp x E.e).ReflectsIsomorphisms :=
  inferInstanceAs ((Equifier.homFunctor E x ⋙
    Equif.forget (postcompNat x B.α) (postcompNat x B.β)).ReflectsIsomorphisms)

/-- `K(x, u')` reflects isomorphisms, since it is an equivalence onto the inserter of
`K(x, f), K(x, g)` followed by its (conservative) forgetful functor. -/
instance postcompU_reflectsIsomorphisms (x : Obj) :
    (postcomp x B.ins.u).ReflectsIsomorphisms :=
  inferInstanceAs ((Inserter.homFunctor B.ins x ⋙
    Ins.forget (postcomp x B.f) (postcomp x B.g)).ReflectsIsomorphisms)

/-- `K(x, e) ⋙ K(x, u')` reflects isomorphisms, as a composite of conservative functors. -/
instance uBHomForget_reflectsIsomorphisms (x : Obj) :
    (B.uBHomForget E x).ReflectsIsomorphisms :=
  inferInstanceAs ((postcomp x E.e ⋙ postcomp x B.ins.u).ReflectsIsomorphisms)

/-- `K(x, u_B)` reflects isomorphisms. -/
instance postcomp_uB_reflectsIsomorphisms (x : Obj) :
    (postcomp x (B.uB E)).ReflectsIsomorphisms := by
  rw [← B.uBHomForget_eq E x]
  infer_instance

section Split

variable {B E} {x : Obj} {X Y : x ⟶ E.pt} (h₁ h₂ : X ⟶ Y)
variable [HasSplitCoequalizer ((B.uBHomForget E x).map h₁) ((B.uBHomForget E x).map h₂)]

/-- A pair `h₁, h₂` whose image under `K(x, u_B)` has a split coequalizer still has one after
applying `K(x, e)`, the equivalence to the inserter of `K(x, f), K(x, g)` and its forgetful functor.
-/
theorem hasSplitCoequalizer_ins :
    HasSplitCoequalizer
      ((Ins.forget (postcomp x B.f) (postcomp x B.g)).map
        ((Inserter.homFunctor B.ins x).map ((postcomp x E.e).map h₁)))
      ((Ins.forget (postcomp x B.f) (postcomp x B.g)).map
        ((Inserter.homFunctor B.ins x).map ((postcomp x E.e).map h₂))) :=
  inferInstanceAs (HasSplitCoequalizer ((B.uBHomForget E x).map h₁)
    ((B.uBHomForget E x).map h₂))

/-- For a `K(x, u_B)`-split pair `h₁, h₂`, the diagram `(h₁, h₂) ⋙ K(x, e) ⋙ K(x, u')` has a
colimit. -/
theorem hasColimit_uBHomForget_of_homSplit :
    HasColimit ((parallelPair h₁ h₂ ⋙ postcomp x E.e) ⋙ postcomp x B.ins.u) := by
  have : HasColimit (parallelPair ((B.uBHomForget E x).map h₁)
      ((B.uBHomForget E x).map h₂)) := inferInstance
  exact hasColimit_of_iso (parallelPairComp h₁ h₂ (B.uBHomForget E x))

/-- For a `K(x, u_B)`-split pair `h₁, h₂`, `K(x, u')` creates the coequalizer of `K(x, e)(h₁, h₂)`,
via the creation of split coequalizers by the forgetful functor of inserters `Ins(K(x,f), K(x,g))`.
-/
@[instance_reducible]
noncomputable def createsColimitPostcompUOfHomSplit :
    CreatesColimit (parallelPair h₁ h₂ ⋙ postcomp x E.e) (postcomp x B.ins.u) := by
  set ΦI := Inserter.homFunctor B.ins x
  set f' := (postcomp x E.e).map h₁
  set g' := (postcomp x E.e).map h₂
  have := hasSplitCoequalizer_ins h₁ h₂
  have : CreatesColimit (parallelPair (ΦI.map f') (ΦI.map g'))
      (Ins.forget (postcomp x B.f) (postcomp x B.g)) :=
    Ins.createsColimitParallelPair _ _
  have : HasColimit (parallelPair (ΦI.map f') (ΦI.map g') ⋙
      Ins.forget (postcomp x B.f) (postcomp x B.g)) := by
    have : HasColimit (parallelPair
        ((Ins.forget (postcomp x B.f) (postcomp x B.g)).map (ΦI.map f'))
        ((Ins.forget (postcomp x B.f) (postcomp x B.g)).map (ΦI.map g'))) := inferInstance
    exact hasColimit_of_iso (parallelPairComp _ _ _)
  have : HasColimit (parallelPair (ΦI.map f') (ΦI.map g')) :=
    hasColimit_of_created _ (Ins.forget (postcomp x B.f) (postcomp x B.g))
  have : CreatesColimit (parallelPair f' g' ⋙ ΦI)
      (Ins.forget (postcomp x B.f) (postcomp x B.g)) :=
    createsColimitOfIsoDiagram _ (parallelPairComp f' g' ΦI).symm
  have : HasColimit (parallelPair f' g' ⋙ ΦI) :=
    hasColimit_of_iso (parallelPairComp f' g' ΦI)
  have : CreatesColimit (parallelPair f' g') ΦI :=
    createsColimitOfIsEquivalence _ ΦI
  have : CreatesColimit (parallelPair f' g')
      (ΦI ⋙ Ins.forget (postcomp x B.f) (postcomp x B.g)) :=
    inferInstance
  have : CreatesColimit (parallelPair f' g') (postcomp x B.ins.u) := this
  exact createsColimitOfIsoDiagram _ (parallelPairComp h₁ h₂ (postcomp x E.e)).symm

/-- For a `K(x, u_B)`-split pair `h₁, h₂`, the pair `K(x, e)(h₁, h₂)` has a coequalizer. -/
theorem hasColimit_postcompE_of_homSplit :
    HasColimit (parallelPair h₁ h₂ ⋙ postcomp x E.e) := by
  have := createsColimitPostcompUOfHomSplit h₁ h₂
  have := hasColimit_uBHomForget_of_homSplit h₁ h₂
  exact hasColimit_of_created _ (postcomp x B.ins.u)

/-- For a `K(x, u_B)`-split pair `h₁, h₂`, `K(x, u')` preserves the coequalizer of
`K(x, e)(h₁, h₂)`. -/
theorem preservesColimit_postcompU_of_homSplit :
    PreservesColimit (parallelPair h₁ h₂ ⋙ postcomp x E.e) (postcomp x B.ins.u) := by
  have := createsColimitPostcompUOfHomSplit h₁ h₂
  have := hasColimit_uBHomForget_of_homSplit h₁ h₂
  infer_instance

/-- For a `K(x, u_B)`-split pair `h₁, h₂`, `K(x, u' ≫ f')` preserves the coequalizer of
`K(x, e)(h₁, h₂)`: `K(x, u')` preserves it and `K(x, f')` preserves split coequalizers. -/
theorem preservesColimit_homLhs_of_homSplit :
    PreservesColimit (parallelPair h₁ h₂ ⋙ postcomp x E.e)
      (postcomp x (B.ins.u ≫ B.f')) := by
  have := preservesColimit_postcompU_of_homSplit h₁ h₂
  have : HasSplitCoequalizer ((B.uBHomForget E x).map h₁)
      ((B.uBHomForget E x).map h₂) := inferInstance
  have := preservesColimit_parallelPair_of_hasSplitCoequalizer
    ((B.uBHomForget E x).map h₁) ((B.uBHomForget E x).map h₂) (postcomp x B.f')
  have : PreservesColimit
      ((parallelPair h₁ h₂ ⋙ postcomp x E.e) ⋙ postcomp x B.ins.u)
      (postcomp x B.f') :=
    preservesColimit_of_iso_diagram (postcomp x B.f')
      (parallelPairComp h₁ h₂ (B.uBHomForget E x)).symm
  rw [postcomp_comp₁ x B.ins.u B.f']
  infer_instance

/-- For a `K(x, u_B)`-split pair `h₁, h₂`, `K(x, e)` creates its coequalizer, via the equivalence
onto the equifier of `K(x, α), K(x, β)` and creation of colimits by the equifier's forgetful
functor. -/
@[instance_reducible]
noncomputable def createsColimitPostcompEOfHomSplit :
    CreatesColimit (parallelPair h₁ h₂) (postcomp x E.e) := by
  set ΦE := Equifier.homFunctor E x
  set FE := Equif.forget (postcompNat x B.α) (postcompNat x B.β)
  have : HasColimit ((parallelPair h₁ h₂ ⋙ ΦE) ⋙ FE) :=
    hasColimit_postcompE_of_homSplit h₁ h₂
  have : HasColimit (parallelPair (ΦE.map h₁) (ΦE.map h₂) ⋙ FE) :=
    hasColimit_of_iso (Functor.isoWhiskerRight (parallelPairComp h₁ h₂ ΦE) FE).symm
  have : PreservesColimit ((parallelPair h₁ h₂ ⋙ ΦE) ⋙ FE)
      (postcomp x (B.ins.u ≫ B.f')) :=
    preservesColimit_homLhs_of_homSplit h₁ h₂
  have : PreservesColimit (parallelPair (ΦE.map h₁) (ΦE.map h₂) ⋙ FE)
      (postcomp x (B.ins.u ≫ B.f')) :=
    preservesColimit_of_iso_diagram (postcomp x (B.ins.u ≫ B.f'))
      (Functor.isoWhiskerRight (parallelPairComp h₁ h₂ ΦE) FE)
  have : CreatesColimit (parallelPair (ΦE.map h₁) (ΦE.map h₂)) FE :=
    Equif.createsColimit _
  have : HasColimit (parallelPair (ΦE.map h₁) (ΦE.map h₂)) :=
    hasColimit_of_created _ FE
  have : HasColimit (parallelPair h₁ h₂ ⋙ ΦE) :=
    hasColimit_of_iso (parallelPairComp h₁ h₂ ΦE)
  have : CreatesColimit (parallelPair h₁ h₂) ΦE :=
    createsColimitOfIsEquivalence _ ΦE
  have : CreatesColimit (parallelPair h₁ h₂ ⋙ ΦE) FE :=
    createsColimitOfIsoDiagram _ (parallelPairComp h₁ h₂ ΦE).symm
  exact inferInstanceAs (CreatesColimit (parallelPair h₁ h₂) (ΦE ⋙ FE))

/-- `K(x, u_B) = K(x, e) ⋙ K(x, u')` creates coequalizers of `K(x, u_B)`-split pairs (the Beck
condition used for monadicity of `u_B`, Theorem 7.6 of [forsman2026syntactic]). -/
@[instance_reducible]
noncomputable def createsColimitUBHomForgetOfHomSplit :
    CreatesColimit (parallelPair h₁ h₂) (B.uBHomForget E x) := by
  have := createsColimitPostcompEOfHomSplit h₁ h₂
  have := createsColimitPostcompUOfHomSplit h₁ h₂
  exact inferInstanceAs (CreatesColimit (parallelPair h₁ h₂)
    (postcomp x E.e ⋙ postcomp x B.ins.u))

end Split

/-- `K(x, u_B)` creates the coequalizers of `K(x, u_B)`-split pairs. -/
theorem uB_createsColimit_of_isSplitPair (x : Obj) ⦃X Y : x ⟶ E.pt⦄ (h₁ h₂ : X ⟶ Y)
    (hsp : (postcomp x (B.uB E)).IsSplitPair h₁ h₂) :
    Nonempty (CreatesColimit (parallelPair h₁ h₂) (postcomp x (B.uB E))) := by
  rw [← B.uBHomForget_eq E x] at hsp ⊢
  have : HasSplitCoequalizer ((B.uBHomForget E x).map h₁)
      ((B.uBHomForget E x).map h₂) := hsp
  exact ⟨createsColimitUBHomForgetOfHomSplit h₁ h₂⟩

/-- `u_B` is monadic in `K` as soon as it has a left adjoint in `K`. -/
theorem isMonadic2_uB_of_twoAdj (h : ∃ f : B.c ⟶ E.pt, Nonempty (TwoAdj f (B.uB E))) :
    IsMonadic2 (B.uB E) := by
  obtain ⟨f, ⟨A⟩⟩ := h
  refine ⟨f, A, fun x => ?_⟩
  let : Monad.CreatesColimitOfIsSplitPair (postcomp x (B.uB E)) :=
    ⟨fun h₁ h₂ hsp => (B.uB_createsColimit_of_isSplitPair E x h₁ h₂ hsp).some⟩
  exact (Monad.monadicOfCreatesGSplitCoequalizers (A.postcompAdj x)).eqv

/-- If `B.g` and `B.g'` are right adjoints in `K`, `B.c` has `HasARightKan A`, `A` is bi-dense,
and `B.uB E` is an `A`-right adjoint, then `B.uB E` is monadic in `K`. -/
theorem isMonadic2_uB_of_isARightAdjoint {A : ObjectProperty Obj} (hA : IsBiDense A)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hRan : HasARightKan A B.c) (hadj : IsARightAdjoint A (B.uB E)) :
    IsMonadic2 (B.uB E) := by
  obtain ⟨l, ⟨adj_g⟩⟩ := hg
  obtain ⟨l', ⟨adj_g'⟩⟩ := hg'
  obtain ⟨hE_kan, huB_kan⟩ := B.uB_hasAndPreservesARightKan E hRan
    (fun _ _ _ _ k e => preservesRightKan_of_twoAdj adj_g k e)
    (fun _ _ _ _ k e => preservesRightKan_of_twoAdj adj_g' k e)
  exact B.isMonadic2_uB_of_twoAdj E
      (exists_leftAdjoint_of_isARightAdjoint A hA (B.uB E) hE_kan huB_kan hadj)

/-- `u_B` is comonadic in `K` as soon as it has a right adjoint in `K`: this is
`isMonadic2_uB_of_twoAdj` for the dual datum `B^co` in `K^co`, where the right adjoint of `u_B`
becomes a left adjoint and comonadicity becomes monadicity. -/
theorem isComonadic2_uB_of_twoAdj (h : ∃ r : B.c ⟶ E.pt, Nonempty (TwoAdj (B.uB E) r)) :
    IsComonadic2 (B.uB E) := by
  obtain ⟨r, ⟨A⟩⟩ := h
  rw [isComonadic2_iff_monadic_co, ← BialgDatum.uB_co]
  exact B.co.isMonadic2_uB_of_twoAdj (Equifier.co E) ⟨Co.hom r, ⟨Co.adj A⟩⟩

end BialgDatum

end Paper

end UlmerBialgebras
