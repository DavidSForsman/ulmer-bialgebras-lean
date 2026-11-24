module

public import UlmerBialgebras.Proofs.Sec6.Sec6Factorization
public import Foundations.CategoryTheory.Factorization.RegularCharacterization
public import Foundations.CategoryTheory.Category.ThinShape

/-! # Solution: Factorization and exactness of bialgebras

## Main results

* `UlmerBialgebras.Paper.thm_6_6_1`: Theorem 6.6 (1): if `F(E') ⊥ G(M')` and `F'(E') ⊥_! G'(M')`,
  then `(U_B⁻¹E', U_B⁻¹M')` is the unique orthogonal factorization system on `Bialg(B)` preserved by
  `U_B`.
* `UlmerBialgebras.Paper.thm_6_6_2`: Theorem 6.6 (2): under its hypotheses, `Bialg(B)` is regular,
  `U_B` strictly creates pullbacks and `U_B` preserves regular epimorphisms.
* `UlmerBialgebras.Paper.thm_6_6_3`: Theorem 6.6 (3): under its hypotheses, `Bialg(B)` is
  Barr-exact.
* `UlmerBialgebras.Paper.thm_6_6_3_coeq`: Theorem 6.6 (3), creation clause: `U_B` strictly creates
  the coequalizer of each kernel pair in `Bialg(B)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 6.6
-/

@[expose] public section

universe u v w u' v' w₀ u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section BialgOFS

variable (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v)))
  (horth : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal ((B.f).toFunctor.map e) ((B.g).toFunctor.map m))
  (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m))

/-- The OFS on `K(1, Ins(f, g))`. -/
noncomputable def insHomOFS : OFS (One.{v, max u v} ⟶ B.ins.pt) :=
  (insOFS' ((S.toRepOFS).ofs One.{v, max u v}) (postcomp One.{v, max u v} B.f)
      (postcomp One.{v, max u v} B.g)
    (fun _ _ _ _ _ _ he hm => orthogonal_of_map ((catHomEquivalence One B.x).functor ⋙ oneEval B.x)
      (horth _ _ (he One.star) (hm One.star)))).transport (B.ins.homEquiv One.{v, max u v}).symm

include horth in
/-- A 2-cell `α : k ⟹ k'` of `K(1, Ins(f, g))` is in `E` iff `u(α_*)` is in `E` of the OFS
    on `c`. -/
lemma insHomOFS_E {k k' : One.{v, max u v} ⟶ B.ins.pt} (α : k ⟶ k') :
    (insHomOFS B S horth).E α ↔ S.E ((B.ins.u).toFunctor.map (α.toNatTrans.app One.star)) :=
  ⟨fun h => h One.star, fun h x => by cases x; exact h⟩

include horth in
/-- A 2-cell `α : k ⟹ k'` of `K(1, Ins(f, g))` is in `M` iff `u(α_*)` is in `M` of the OFS
    on `c`. -/
lemma insHomOFS_M {k k' : One.{v, max u v} ⟶ B.ins.pt} (α : k ⟶ k') :
    (insHomOFS B S horth).M α ↔ S.M ((B.ins.u).toFunctor.map (α.toNatTrans.app One.star)) :=
  ⟨fun h => h One.star, fun h x => by cases x; exact h⟩

/-- The OFS on `K(1, Bialg(B))`. -/
noncomputable def bialgHomOFS : OFS (One.{v, max u v} ⟶ E.pt) :=
  (equifOFS' (insHomOFS B S horth) (postcompNat One.{v, max u v} B.α)
      (postcompNat One.{v, max u v} B.β)
    (fun _ _ _ _ e m he hm => orthogonalLE1_of_map ((catHomEquivalence One B.y).functor ⋙ oneEval
        B.y)
      (horth' _ _ ((insHomOFS_E B S horth e).1 he) ((insHomOFS_M B S horth m).1 hm)))).transport
    (E.homEquiv One.{v, max u v}).symm

/-- The OFS on `Bialg(B)` of Theorem 6.6 (1). -/
noncomputable def bialgOFS : OFS (E.pt : Type (max u v)) :=
  (bialgHomOFS B E S horth horth').transport ((catHomEquivalence One E.pt).trans (oneEquiv E.pt))

include horth horth' in
/-- A morphism `f` of `Bialg(B)` is in `E` of the lifted OFS iff `U_B f` is in `E` of the OFS on
    `c` (Theorem 6.6 (1)). -/
lemma bialgOFS_E ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y) :
    (bialgOFS B E S horth horth').E f ↔ S.E ((B.uB E).toFunctor.map f) := by
  have h : (bialgOFS B E S horth horth').E f ↔
      S.E ((B.uB E).toFunctor.map
        (((catHomEquivalence One E.pt).functor ⋙ oneEval E.pt).map (((catHomEquivalence One
            E.pt).trans (oneEquiv E.pt)).inverse.map f))) :=
    insHomOFS_E B S horth _
  rw [h]
  have h2 : ((catHomEquivalence One E.pt).functor ⋙ oneEval E.pt).map (((catHomEquivalence One
      E.pt).trans (oneEquiv E.pt)).inverse.map f) =
      ((catHomEquivalence One E.pt).trans (oneEquiv E.pt)).counit.app x ≫ f ≫ ((catHomEquivalence
          One E.pt).trans (oneEquiv E.pt)).counitInv.app y :=
    Equivalence.fun_inv_map ((catHomEquivalence One E.pt).trans (oneEquiv E.pt)) x y f
  rw [h2]
  refine (iff_of_eq (congrArg (fun g => S.E g) (((B.uB E).toFunctor.map_comp _ _).trans
    (congrArg (_ ≫ ·) ((B.uB E).toFunctor.map_comp _ _))))).trans ?_
  let EQ := (catHomEquivalence One E.pt).trans (oneEquiv E.pt)
  exact @OFS.e_conj_iff _ _ S _ _ _ _ _
    ((B.uB E).toFunctor.mapIso (EQ.counitIso.app x)).isIso_hom _ _
    ((B.uB E).toFunctor.mapIso (EQ.counitIso.app y)).isIso_inv

include horth horth' in
/-- A morphism `f` of `Bialg(B)` is in `M` of the lifted OFS iff `U_B f` is in `M` of the OFS on
    `c` (Theorem 6.6 (1)). -/
lemma bialgOFS_M ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y) :
    (bialgOFS B E S horth horth').M f ↔ S.M ((B.uB E).toFunctor.map f) := by
  have h : (bialgOFS B E S horth horth').M f ↔
      S.M ((B.uB E).toFunctor.map
        (((catHomEquivalence One E.pt).functor ⋙ oneEval E.pt).map (((catHomEquivalence One
            E.pt).trans (oneEquiv E.pt)).inverse.map f))) :=
    insHomOFS_M B S horth _
  rw [h]
  have h2 : ((catHomEquivalence One E.pt).functor ⋙ oneEval E.pt).map (((catHomEquivalence One
      E.pt).trans (oneEquiv E.pt)).inverse.map f) =
      ((catHomEquivalence One E.pt).trans (oneEquiv E.pt)).counit.app x ≫ f ≫ ((catHomEquivalence
          One E.pt).trans (oneEquiv E.pt)).counitInv.app y :=
    Equivalence.fun_inv_map ((catHomEquivalence One E.pt).trans (oneEquiv E.pt)) x y f
  rw [h2]
  refine (iff_of_eq (congrArg (fun g => S.M g) (((B.uB E).toFunctor.map_comp _ _).trans
    (congrArg (_ ≫ ·) ((B.uB E).toFunctor.map_comp _ _))))).trans ?_
  let EQ := (catHomEquivalence One E.pt).trans (oneEquiv E.pt)
  exact @OFS.m_conj_iff _ _ S _ _ _ _ _
    ((B.uB E).toFunctor.mapIso (EQ.counitIso.app x)).isIso_hom _ _
    ((B.uB E).toFunctor.mapIso (EQ.counitIso.app y)).isIso_inv

end BialgOFS

/-- **Theorem 6.6 (1)** ([forsman2026syntactic]): if `F(E') ⊥ G(M')` and `F'(E') ⊥_! G'(M')`, then
`(U_B⁻¹E', U_B⁻¹M')` is the unique orthogonal factorization system on `Bialg(B)` preserved
by `U_B`. -/
theorem thm_6_6_1 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v)))
    (horth : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal ((B.f).toFunctor.map e) ((B.g).toFunctor.map m))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m)) :
    ∃ P : OFS (E.pt : Type (max u v)),
      (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
        P.E f ↔ S.E ((B.uB E).toFunctor.map f)) ∧
      (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
        P.M f ↔ S.M ((B.uB E).toFunctor.map f)) ∧
      ∀ P' : OFS (E.pt : Type (max u v)),
        (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
          P'.E f → S.E ((B.uB E).toFunctor.map f)) →
        (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
          P'.M f → S.M ((B.uB E).toFunctor.map f)) → P' = P :=
  ⟨bialgOFS B E S horth horth', bialgOFS_E B E S horth horth', bialgOFS_M B E S horth horth',
    fun _ hE hM => OFS.ext_of_le (fun _ _ f h => (bialgOFS_E B E S horth horth' f).2 (hE f h))
      (fun _ _ f h => (bialgOFS_M B E S horth horth' f).2 (hM f h))⟩

/-- In a regular category every morphism left orthogonal to all monos is a regular epi: it is
the coequalizer of its kernel pair. -/
theorem regularEpi_of_extremalEpi_of_isRegularCat {C : Type (max u v)} [Category.{v} C]
    (hC : IsRegularCat C) {X I : C} {e : X ⟶ I} (he : extremalEpi C e) :
    Nonempty (RegularEpi e) := by
  have := hC.hasFiniteLimits
  have : Regular C := regular_of_isRegularCat hC
  have h : IsRegularEpi e :=
    (isRegularEpi_iff_isExtremalEpi e).2 ((extremalEpi_iff e).1 he)
  exact h.regularEpi

/-- The forgetful functor of an equifier in `Cat` is faithful. -/
lemma Equifier.faithful_functor {a b : Cat.{v, max u v}} {f g : a ⟶ b} {η θ : f ⟶ g}
    (E : Equifier η θ) : E.e.toFunctor.Faithful where
  map_injective {x y} p q h := by
    have := E.faithful (x := One.{v, max u v}) ((Functor.const One.{v, max u v}).map p).toCatHom₂
          ((Functor.const One.{v, max u v}).map q).toCatHom₂
              (Cat.Hom₂.ext (NatTrans.ext (funext fun z =>
              by cases z; exact h)))
    exact congr_app (congrArg Cat.Hom₂.toNatTrans this) One.star

/-- The forgetful functor of an inserter in `Cat` is faithful. -/
lemma Inserter.faithful_functor {a b : Cat.{v, max u v}} {f g : a ⟶ b} (I : Inserter f g) :
    I.u.toFunctor.Faithful where
  map_injective {x y} p q h := by
    have := I.lift₂_uniq (x := One.{v, max u v}) ((Functor.const One.{v, max u v}).map p).toCatHom₂
          ((Functor.const One.{v, max u v}).map q).toCatHom₂
              (Cat.Hom₂.ext (NatTrans.ext (funext fun z =>
              by cases z; exact h)))
    exact congr_app (congrArg Cat.Hom₂.toNatTrans this) One.star

/-- The forgetful functor `U_B : Bialg(B) ⥤ c` is faithful, as a composite of the faithful
    projections of an equifier and an inserter in `Cat`. -/
lemma uB_faithful (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β) :
    (B.uB E).toFunctor.Faithful := by
  have := Equifier.faithful_functor E
  have := Inserter.faithful_functor B.ins
  exact (inferInstance : (E.e.toFunctor ⋙
    (B.ins.u).toFunctor).Faithful)

section Pullbacks

variable (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
  [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
  (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)

include hG' in
/-- `U_B` strictly creates the right Kan extensions along `J ⟶ 1` for any `J` equivalent to
the walking cospan (Corollary 4.8). -/
theorem uB_strictlyCreates_of_equiv (J : Cat.{v, max u v})
    (eqv : WalkingCospan ≌ (J : Type (max u v)))
    (d : J ⟶ E.pt) : StrictlyCreatesRightKan (toOne J) d (B.uB E) := by
  have : PreservesLimitsOfShape (J : Type (max u v)) (B.g).toFunctor :=
    preservesLimitsOfShape_of_equiv eqv _
  refine cor_4_8_right B E (toOne J) d
    (preservesRightKan_of_preservesLimitsOfShape B.g (d ≫ B.uB E)) ?_
  intro R hR
  refine subterminal_of_jointlyMono _ ?_
  intro w p q hpq
  exact hG' _ _ ((isLimitConeOfRightExt hR.some).whiskerEquivalence eqv) p q
    (fun j => by
      have h := hpq (eqv.functor.obj j)
      simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, RightExt.push_obj_ext,
        RightExt.push_obj_counit, eqToHom_refl, Category.id_comp, Cat.whiskerRight_toNatTrans,
        Functor.whiskerRight_app] at h
      exact h)

/-- A 1-cell strictly creating the right Kan extensions of `d` along `I ⟶ 1` reflects the
existence of the limit of `d`. -/
theorem hasLimit_of_strictlyCreatesRightKan {I X Y : Cat.{v, max u v}} (d : I ⟶ X) (F : X ⟶ Y)
    (hcr : StrictlyCreatesRightKan (toOne I) d F)
    [HasLimit (d ≫ F).toFunctor] :
    HasLimit (d).toFunctor := by
  obtain ⟨⟨R, hRR, -⟩, hterm⟩ := hcr
    (rightExtOfCone (limit.cone (d ≫ F).toFunctor))
    ⟨isTerminalRightExtOfIsLimit (limit.isLimit _)⟩
  exact ⟨⟨⟨_, isLimitConeOfRightExt (hterm R hRR).some⟩⟩⟩

include hG' in
/-- `Bialg(B)` has pullbacks when `c` does. -/
theorem uB_hasPullbacks [HasPullbacks (B.c : Type (max u v))] : HasPullbacks
    (E.pt : Type (max u v)) := by
  have h : ∀ {X Y Z : (E.pt : Type (max u v))} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) := by
    intro X Y Z f g
    let J : Cat.{v, max u v} := cospanShapeCat
    let dC : J ⟶ E.pt :=
      (cospanShapeCat.equivalence.symm.functor ⋙ cospan f g).toCatHom
    have : HasLimitsOfShape (J : Type (max u v)) (B.c : Type (max u v)) :=
      hasLimitsOfShape_of_equivalence cospanShapeCat.equivalence
    have : HasLimit (dC).toFunctor :=
      hasLimit_of_strictlyCreatesRightKan dC (B.uB E)
        (uB_strictlyCreates_of_equiv B E hG' cospanShapeCat cospanShapeCat.equivalence dC)
    have : HasLimit (cospanShapeCat.equivalence.symm.functor ⋙ cospan f g) :=
      inferInstanceAs (HasLimit dC.toFunctor)
    exact hasLimit_of_equivalence_comp cospanShapeCat.equivalence.symm
  exact @hasPullbacks_of_hasLimit_cospan _ _ h

include hG' in
/-- `U_B` preserves pullbacks. -/
theorem uB_preservesPullbacks [HasPullbacks (B.c : Type (max u v))] :
    PreservesLimitsOfShape WalkingCospan (B.uB E).toFunctor :=
  ⟨fun {K} => by
    have := uB_preservesLimit_cospan B E hG' (K.map WalkingCospan.Hom.inl)
      (K.map WalkingCospan.Hom.inr)
    exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm⟩

end Pullbacks

/-- Working form of `thm_6_6_2`, with the OFS-based notions (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`, `UlmerBialgebras.IsEquivRel`, `UlmerBialgebras.extremalEpi`).
**Theorem 6.6 (2)** ([forsman2026syntactic]): over a regular category with `M'` the
monomorphisms, if `Bialg(B)` has a terminal object, `F` preserves regular epis, `F'(E') ⊥_! G'(M')`,
`G` preserves pullbacks and `G'` the joint monicness of pullback projections, then `Bialg(B)` is
regular, `U_B` strictly creates pullbacks (limits of the two-legged wide pullback shape) and
preserves regular epimorphisms. -/
theorem isRegularCat_and_creates_pullbacks_uB (B : BialgDatum (Obj := Cat.{v, max u v}))
    (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v))) (hreg : IsRegularCat (B.c : Type (max u v)))
    (hM : S.M = MorphismProperty.monomorphisms (B.c : Type (max u v)))
    (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Nonempty (RegularEpi ((B.f).toFunctor.map e)))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    IsRegularCat (E.pt : Type (max u v)) ∧
      (∀ (J : Cat.{v, max u v}) (_ : WalkingCospan ≌ (J : Type (max u v)))
        (d : J ⟶ E.pt), StrictlyCreatesRightKan (toOne J) d (B.uB E)) ∧
      ∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y), Nonempty (RegularEpi f) →
        Nonempty (RegularEpi ((B.uB E).toFunctor.map f)) := by
  have : HasFiniteLimits (B.c : Type (max u v)) := hreg.hasFiniteLimits
  have := uB_faithful B E
  have := uB_preservesPullbacks B E hG'
  have := uB_hasPullbacks B E hG'
  have := hterm
  have : HasFiniteLimits (E.pt : Type (max u v)) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hSE : S.E = extremalEpi (B.c : Type (max u v)) := S.e_eq_extremalEpi hM
  have horth : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal ((B.f).toFunctor.map e) ((B.g).toFunctor.map m) := by
    intro a b c d e m he hm
    rw [hSE] at he
    rw [hM] at hm
    have : Mono m := hm
    obtain ⟨hr⟩ := regularEpi_of_extremalEpi_of_isRegularCat hreg he
    obtain ⟨hFr⟩ := hF e ⟨hr⟩
    exact extremalEpi_of_regularEpi' hFr _ (by
      rw [MorphismProperty.monomorphisms.iff]; infer_instance)
  obtain ⟨P, hPE, hPM, -⟩ := thm_6_6_1 B E S horth horth'
  have hPE' : ∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
      P.E f ↔ extremalEpi (B.c : Type (max u v)) ((B.uB E).toFunctor.map f) :=
    fun _ _ f => (hPE f).trans (by rw [hSE])
  have hPM' : ∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
      P.M f ↔ Mono ((B.uB E).toFunctor.map f) :=
    fun _ _ f => (hPM f).trans (by rw [hM])
  have hreg' : IsRegularCat (E.pt : Type (max u v)) :=
    (regular_exact_transfer_of_preservesPullbacks (B.uB E).toFunctor
      (fun _ _ _ h => Functor.mono_of_mono_map _ h)).1 ⟨P, hPE', hPM'⟩ hreg.stable
  have hPmono : P.M = MorphismProperty.monomorphisms (E.pt : Type (max u v)) := by
    ext x y f
    rw [hPM' f, MorphismProperty.monomorphisms.iff]
    exact ⟨fun h => Functor.mono_of_mono_map _ h, fun _ => inferInstance⟩
  refine ⟨hreg', fun J e d => uB_strictlyCreates_of_equiv B E hG' J e d, ?_⟩
  rintro x y f ⟨hf⟩
  have h1 : P.E f := by
    rw [P.e_eq_extremalEpi hPmono]
    exact extremalEpi_of_regularEpi' hf
  exact regularEpi_of_extremalEpi_of_isRegularCat hreg ((hPE' f).1 h1)

/-- **Theorem 6.6 (2)** ([forsman2026syntactic]): over a regular category with `M'` the
monomorphisms, if `Bialg(B)` has a terminal object, `F` preserves regular epis, `F'(E') ⊥_! G'(M')`,
`G` preserves pullbacks and `G'` the joint monicness of pullback projections, then `Bialg(B)` is
regular, `U_B` strictly creates pullbacks (limits of the two-legged wide pullback shape) and
preserves regular epimorphisms. -/
theorem thm_6_6_2 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v))) [Regular (B.c : Type (max u v))]
    (hM : S.M = MorphismProperty.monomorphisms (B.c : Type (max u v)))
    (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Nonempty (RegularEpi ((B.f).toFunctor.map e)))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    Regular (E.pt : Type (max u v)) ∧
      (∀ (J : Cat.{v, max u v}) (_ : WalkingCospan ≌ (J : Type (max u v)))
        (d : J ⟶ E.pt), StrictlyCreatesRightKan (toOne J) d (B.uB E)) ∧
      ∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y), Nonempty (RegularEpi f) →
        Nonempty (RegularEpi ((B.uB E).toFunctor.map f)) := by
  obtain ⟨h1, h2, h3⟩ :=
    isRegularCat_and_creates_pullbacks_uB B E S (isRegularCat_iff_regular.2 inferInstance) hM hterm
        hF horth' hG'
  exact ⟨isRegularCat_iff_regular.1 h1, h2, h3⟩

/-- The creation argument of Theorem 6.6 (3) for any parallel pair whose image under `U_B` is
an equivalence relation. -/
theorem uB_strictlyCreates_coeq (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (hex : IsExactCat (B.c : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    ⦃R a : (E.pt : Type (max u v))⦄ (r s : R ⟶ a)
    (hUeq : IsEquivRel ((B.uB E).toFunctor.map r)
      ((B.uB E).toFunctor.map s))
    (J : Cat.{v, max u v}) (e : WalkingParallelPair ≌ (J : Type (max u v))) :
    StrictlyCreatesLeftKan (toOne J) (e.inverse ⋙ parallelPair r s).toCatHom (B.uB E) := by
  let U : (E.pt : Type (max u v)) ⥤ (B.c : Type (max u v)) := (B.uB E).toFunctor
  let dC : J ⟶ E.pt :=
      (e.inverse ⋙ parallelPair r s).toCatHom
  obtain ⟨d, q, hkq, ⟨hq⟩⟩ := hex.effective _ _ hUeq
  -- `F` preserves the coequalizer `q`
  have hFq := hF _ _ q hkq hq
  have : PreservesColimit (parallelPair (U.map r) (U.map s)) (B.f).toFunctor :=
    preservesColimit_of_preserves_colimit_cocone hq hFq.some
  have : PreservesColimit (parallelPair ((parallelPair r s ⋙ U).map WalkingParallelPairHom.left)
      ((parallelPair r s ⋙ U).map WalkingParallelPairHom.right)) (B.f).toFunctor :=
    (inferInstance : PreservesColimit (parallelPair (U.map r) (U.map s)) _)
  have : PreservesColimit (parallelPair r s ⋙ U) (B.f).toFunctor :=
    preservesColimit_of_iso_diagram _ (diagramIsoParallelPair (parallelPair r s ⋙ U)).symm
  have : PreservesColimit
      (e.inverse ⋙ parallelPair r s ⋙ U) (B.f).toFunctor :=
    inferInstance
  have : PreservesColimit (dC ≫ B.uB E).toFunctor
      (B.f).toFunctor :=
    (inferInstance : PreservesColimit
        (e.inverse ⋙ parallelPair r s ⋙ U) (B.f).toFunctor)
  refine cor_4_8_left B E (toOne J) dC (preservesLeftKan_of_preservesColimit B.f _) ?_
  intro L hL
  let one' : (J : Type (max u v)) := e.functor.obj WalkingParallelPair.one
  -- the leg of the colimit at `one` is a regular epi in `C`, so `F'` maps it to an epi
  have hc := (isColimitCoconeOfLeftExt hL.some).whiskerEquivalence e
  have hreg := regularEpi_of_isColimit_walkingParallelPair _ _ hc
  have hepi : Epi ((B.f').toFunctor.map (L.unit.toNatTrans.app one')) := hF' _ hreg
  have heq : ((LeftExt.push (toOne J) (dC ≫ B.uB E) B.f').obj L).unit.toNatTrans.app one' =
      (B.f').toFunctor.map (L.unit.toNatTrans.app one') := by
    simp
  have : Epi (((LeftExt.push (toOne J) (dC ≫ B.uB E) B.f').obj L).unit.toNatTrans.app one') := by
    rw [heq]; exact hepi
  exact quotientInitial_of_epi_unit _ one'





/-- A functor preserving the coequalizers of kernel pairs preserves regular epimorphisms: a
regular epimorphism is the coequalizer of its kernel pair. -/
theorem nonempty_regularEpi_map_of_preserves {C D : Type*} [Category C] [Category D]
    [HasPullbacks C] (F : C ⥤ D) (hF : PreservesCoequalizersOfKernelPairs F) ⦃a b : C⦄
    (e : a ⟶ b) : Nonempty (RegularEpi e) → Nonempty (RegularEpi (F.map e)) := by
  rintro ⟨he⟩
  have : EffectiveEpi e := he.effectiveEpi
  have hcol : IsColimit (Cofork.ofπ e (pullback.condition (f := e) (g := e))) :=
    isColimitCoforkOfEffectiveEpi e _ (limit.isLimit _)
  have hk : IsKernelPair e (pullback.fst e e) (pullback.snd e e) :=
    IsPullback.of_hasPullback e e
  obtain ⟨hFc⟩ := hF _ _ e hk hcol
  exact ⟨⟨_, _, _, _, isColimitMapCoconeCoforkEquiv _ _ hFc⟩⟩

/-- Under the hypotheses of Theorem 6.6 (3), the coequalizer of an equivalence relation in
`Bialg(B)` exists and `U_B` preserves it. -/
theorem coeq_equivRel_uB (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (hex : IsExactCat (B.c : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)
    [HasFiniteLimits (E.pt : Type (max u v))]
    {R x : (E.pt : Type (max u v))} (r s : R ⟶ x) (hrs : IsEquivRel r s) :
    HasColimit (parallelPair r s) ∧ PreservesColimit (parallelPair r s) (B.uB E).toFunctor := by
  have : HasFiniteLimits (B.c : Type (max u v)) := hex.regular.hasFiniteLimits
  have := uB_preservesPullbacks B E hG'
  have := uB_hasPullbacks B E hG'
  let U : (E.pt : Type (max u v)) ⥤ (B.c : Type (max u v)) := (B.uB E).toFunctor
  have hUeq : IsEquivRel (U.map r) (U.map s) := IsEquivRel.map_of_preservesPullbacks U hrs
  have hcr := uB_strictlyCreates_coeq B E hex hF hF' r s hUeq parallelPairShapeCat
      parallelPairShapeCat.equivalence
  obtain ⟨d, q, hkq, ⟨hq⟩⟩ := hex.effective _ _ hUeq
  have : HasColimit (parallelPair (U.map r) (U.map s)) := ⟨⟨⟨_, hq⟩⟩⟩
  have : HasColimit (parallelPair ((parallelPair r s ⋙ U).map WalkingParallelPairHom.left)
      ((parallelPair r s ⋙ U).map WalkingParallelPairHom.right)) :=
    (inferInstance : HasColimit (parallelPair (U.map r) (U.map s)))
  have : HasColimit (parallelPair r s ⋙ U) :=
    hasColimit_of_iso (diagramIsoParallelPair (parallelPair r s ⋙ U))
  let dC : parallelPairShapeCat ⟶ E.pt :=
    (parallelPairShapeCat.equivalence.symm.functor ⋙ parallelPair r s).toCatHom
  have : HasColimit (parallelPairShapeCat.equivalence.symm.functor ⋙ parallelPair r s ⋙ U) :=
    hasColimit_equivalence_comp (parallelPairShapeCat.equivalence.symm) (F := parallelPair r s ⋙ U)
  have : HasColimit (dC ≫ B.uB E).toFunctor :=
    inferInstanceAs (HasColimit
        (parallelPairShapeCat.equivalence.symm.functor ⋙ parallelPair r s ⋙ U))
  have : HasColimit dC.toFunctor :=
    hasColimit_of_strictlyCreatesLeftKan dC (B.uB E) hcr
  have : PreservesColimit dC.toFunctor (B.uB E).toFunctor :=
    preservesColimit_of_strictlyCreatesLeftKan dC (B.uB E) hcr
  have : HasColimit (parallelPairShapeCat.equivalence.symm.functor ⋙ parallelPair r s) :=
    inferInstanceAs (HasColimit dC.toFunctor)
  have : PreservesColimit (parallelPairShapeCat.equivalence.symm.functor ⋙ parallelPair r s) U :=
    inferInstanceAs (PreservesColimit dC.toFunctor (B.uB E).toFunctor)
  exact ⟨hasColimit_of_equivalence_comp parallelPairShapeCat.equivalence.symm,
    preservesColimit_of_equiv parallelPairShapeCat.equivalence.symm (parallelPair r s) U⟩

/-- Working form of `thm_6_6_3`, with the OFS-based notions (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`, `UlmerBialgebras.IsEquivRel`, `UlmerBialgebras.extremalEpi`).
**Theorem 6.6 (3)** ([forsman2026syntactic]): over an exact category, if `Bialg(B)` has a
terminal object, `F` preserves coequalizers of kernel pairs, `F'` maps regular epis to epis, `G`
preserves pullbacks and `G'` the joint monicness of pullback projections, then `Bialg(B)` is exact.
(The clause that `U_B` strictly creates coequalizers of kernel pairs is `thm_6_6_3_coeq`.) -/
theorem isExactCat_bialg_of_isExactCat (B : BialgDatum (Obj := Cat.{v, max u v}))
    (E : Equifier B.α B.β)
    (hex : IsExactCat (B.c : Type (max u v))) (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    IsExactCat (E.pt : Type (max u v)) := by
  have : HasFiniteLimits (B.c : Type (max u v)) := hex.regular.hasFiniteLimits
  have := uB_faithful B E
  have := uB_preservesPullbacks B E hG'
  have := uB_hasPullbacks B E hG'
  have := hterm
  have : HasFiniteLimits (E.pt : Type (max u v)) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨S, hSM⟩ := hex.regular.exists_ofs
  have hSE : S.E = extremalEpi (B.c : Type (max u v)) := S.e_eq_extremalEpi hSM
  have hFreg := nonempty_regularEpi_map_of_preserves (B.f).toFunctor hF
  have horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m) := by
    intro a b c d e m he _ _ _ _ k k' h1 _ h1' _
    rw [hSE] at he
    have := hF' e (regularEpi_of_extremalEpi_of_isRegularCat hex.regular he)
    exact (cancel_epi _).1 (h1.trans h1'.symm)
  have hreg' :=
      (isRegularCat_and_creates_pullbacks_uB B E S hex.regular hSM hterm hFreg horth' hG').1
  -- `U` is conservative, via the lifted factorization system of Theorem 6.6 (1)
  have horth : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal ((B.f).toFunctor.map e) ((B.g).toFunctor.map m) := by
    intro a b c d e m he hm
    rw [hSE] at he
    rw [hSM] at hm
    have : Mono m := hm
    obtain ⟨hr⟩ := regularEpi_of_extremalEpi_of_isRegularCat hex.regular he
    obtain ⟨hFr⟩ := hFreg e ⟨hr⟩
    exact extremalEpi_of_regularEpi' hFr _ (by
      rw [MorphismProperty.monomorphisms.iff]; infer_instance)
  obtain ⟨P, hPE, hPM, -⟩ := thm_6_6_1 B E S horth horth'
  have hPmono : P.M = MorphismProperty.monomorphisms (E.pt : Type (max u v)) := by
    ext x y f
    rw [hPM f, hSM, MorphismProperty.monomorphisms.iff, MorphismProperty.monomorphisms.iff]
    exact ⟨fun h => Functor.mono_of_mono_map _ h, fun _ => inferInstance⟩
  have hcons : (B.uB E).toFunctor.ReflectsIsomorphisms := by
    constructor
    intro x y f hf
    have h1 : P.E f := (hPE f).2 (by rw [hSE]; exact extremalEpi_of_isIso _)
    rw [P.e_eq_extremalEpi hPmono] at h1
    have := hf
    exact isIso_of_extremalEpi_of_mono h1
      ((B.uB E).toFunctor.mono_of_mono_map inferInstance)
  refine (regular_exact_transfer_of_preservesPullbacks (B.uB E).toFunctor
    (fun _ _ _ h => Functor.mono_of_mono_map _ h)).2.2 ?_ hcons hex
  exact fun R x r s hrs => coeq_equivRel_uB B E hex hF hF' hG' r s hrs

/-- **Theorem 6.6 (3)** ([forsman2026syntactic]): over an exact category, if `Bialg(B)` has a
terminal object, `F` preserves coequalizers of kernel pairs, `F'` maps regular epis to epis, `G`
preserves pullbacks and `G'` the joint monicness of pullback projections, then `Bialg(B)` is exact.
(The clause that `U_B` strictly creates coequalizers of kernel pairs is `thm_6_6_3_coeq`.) -/
theorem thm_6_6_3 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))] (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    BarrExact (E.pt : Type (max u v)) :=
  isExactCat_iff_barrExact.1
    (isExactCat_bialg_of_isExactCat B E (isExactCat_iff_barrExact.2 inferInstance) hterm hF hF' hG')

/-- Working form of `thm_6_6_3_coeq`, with the OFS-based notions (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`, `UlmerBialgebras.IsEquivRel`, `UlmerBialgebras.extremalEpi`).
**Theorem 6.6 (3)** ([forsman2026syntactic]), creation clause: over an exact category, if `F`
preserves coequalizers of kernel pairs, `F'` maps regular epis to epis, `G` preserves pullbacks and
`G'` the joint monicness of pullback projections, then `U_B` strictly creates the coequalizer of
each kernel pair `r, s : R ⇉ a` in `Bialg(B)`, that is, the left Kan extension of the diagram `r, s`
along `I ⟶ 1`, where `I` is the walking parallel pair made `u`-small by `AsSmall`. (This clause
does not need the terminal object of `Bialg(B)`.) -/
theorem strictlyCreatesLeftKan_kernelPair_uB (B : BialgDatum (Obj := Cat.{v, max u v}))
    (E : Equifier B.α B.β)
    (hex : IsExactCat (B.c : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)
    ⦃R a b : (E.pt : Type (max u v))⦄ (f : a ⟶ b) (r s : R ⟶ a) (hk : IsKernelPair f r s)
    (J : Cat.{v, max u v}) (e : WalkingParallelPair ≌ (J : Type (max u v))) :
    StrictlyCreatesLeftKan (toOne J) (e.inverse ⋙ parallelPair r s).toCatHom (B.uB E) := by
  let U : (E.pt : Type (max u v)) ⥤ (B.c : Type (max u v)) := (B.uB E).toFunctor
  have : HasFiniteLimits (B.c : Type (max u v)) := hex.regular.hasFiniteLimits
  have : PreservesLimit (cospan f f) U := uB_preservesLimit_cospan B E hG' f f
  have hkU : IsKernelPair (U.map f) (U.map r) (U.map s) := hk.map U
  exact uB_strictlyCreates_coeq B E hex hF hF' r s (IsKernelPair.isEquivRel hkU) J e

/-- **Theorem 6.6 (3), creation clause** ([forsman2026syntactic], §6): under the hypotheses of
Theorem 6.6 (3) without the terminal object, `U_B` strictly creates the coequalizer of every
kernel pair, for each presentation `J` of the walking parallel pair. -/
theorem thm_6_6_3_coeq (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))]
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)
    ⦃R a b : (E.pt : Type (max u v))⦄ (f : a ⟶ b) (r s : R ⟶ a) (hk : IsKernelPair f r s) :
    ∀ (J : Cat.{v, max u v}) (e : WalkingParallelPair ≌ (J : Type (max u v))),
      StrictlyCreatesLeftKan (toOne J) (e.inverse ⋙ parallelPair r s).toCatHom (B.uB E) :=
  fun J e => strictlyCreatesLeftKan_kernelPair_uB B E (isExactCat_iff_barrExact.2 inferInstance)
    hF hF' hG' f r s hk J e

end UlmerBialgebras.Paper
