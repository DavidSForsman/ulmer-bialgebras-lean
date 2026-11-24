module

public import UlmerBialgebras.Proofs.Sec5.Sec5Proofs

/-! # Solution: Section 6

Proofs on factorization systems, regularity and exactness.

## Main results

* `UlmerBialgebras.Paper.rem_6_2`: Remark 6.2: a pair of classes `(E, M)` is an orthogonal
  factorization system iff every morphism has an `(E, M)`-factorization, `E ⊥ M`, and both classes
  are closed under retracts.
* `UlmerBialgebras.Paper.thm_6_3_1`: Theorem 6.3 (1): the componentwise classes form the unique
  orthogonal factorization system on a product of categories preserved by the projections.
* `UlmerBialgebras.Paper.thm_6_3_2`, `UlmerBialgebras.Paper.thm_6_3_3`: Theorem 6.3 (2) and (3): if
  `F(E') ⊥ G(M')` (resp. `F(E') ⊥_! G(M')`), the inverse images of `E'` and `M'` form the unique
  orthogonal factorization system on the inserter `Ins(F, G)` (resp. the equifier `Eq(η, θ)`)
  preserved by the forgetful functor.
* `UlmerBialgebras.Paper.def_6_4_regular`, `UlmerBialgebras.Paper.def_6_4_exact`: Definition 6.4:
  Mathlib's regular and Barr-exact categories are the paper's regular and exact categories.
* `UlmerBialgebras.Paper.lem_6_5`: Lemma 6.5: transfer of regularity and exactness along a pullback
  preserving functor reflecting monomorphisms out of a finitely complete category.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 6.2,
  Theorem 6.3, Definition 6.4 and Lemma 6.5
-/

@[expose] public section

universe u v w u' v' w₀ u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Section 6: factorization systems, regularity, exactness -/

section Sec6

variable {C : Type u} [Category.{v} C]

/-- **Remark 6.2** ([forsman2026syntactic]): an orthogonal factorization system is equivalently a
pair `(E, M)` of classes such that every morphism has an `(E, M)`-factorization, `E ⊥ M`, and both
classes are closed under retracts in the arrow category. -/
theorem rem_6_2 (E M : MorphismProperty C) :
    (∃ S : OFS C, S.E = E ∧ S.M = M) ↔
      ((∀ ⦃x y : C⦄ (f : x ⟶ y), ∃ (z : C) (e : x ⟶ z) (m : z ⟶ y), E e ∧ M m ∧ e ≫ m = f) ∧
        (∀ ⦃x y z w : C⦄ (e : x ⟶ y) (m : z ⟶ w), E e → M m → Orthogonal e m) ∧
        E.IsStableUnderRetracts ∧ M.IsStableUnderRetracts) :=
  ⟨fun ⟨S, hE, hM⟩ => hE ▸ hM ▸ ⟨S.fact, fun _ _ _ _ _ _ he hm => S.orth he hm,
      S.e_isStableUnderRetracts, S.m_isStableUnderRetracts⟩,
    fun ⟨fact, orth, hE, hM⟩ => ⟨OFS.mk' E M fact orth hE hM, rfl, rfl⟩⟩

/-- **Theorem 6.3 (1)** ([forsman2026syntactic]): the product factorization system is the unique one
preserved by the projections. -/
theorem thm_6_3_1 {ι : Type w} {Ci : ι → Type u} [∀ i, Category.{v} (Ci i)] (S : ∀ i, OFS (Ci i)) :
    ∃ P : OFS (∀ i, Ci i),
      (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P.E f ↔ ∀ i, (S i).E (f i)) ∧
      (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P.M f ↔ ∀ i, (S i).M (f i)) ∧
      ∀ P' : OFS (∀ i, Ci i),
        (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P'.E f → ∀ i, (S i).E (f i)) →
        (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P'.M f → ∀ i, (S i).M (f i)) → P' = P :=
  ⟨prodOFS S, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    fun P' hE hM => prodOFS_unique S P' hE hM⟩

variable {D : Type u'} [Category.{v'} D]

/-- The factorization system of Theorem 6.3 (2) on `Ins(F, G)`, assuming only `F(E') ⊥ G(M')`. -/
def insOFS' (S : OFS C) (F G : C ⥤ D)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal (F.map e) (G.map m)) : OFS (Ins F G) :=
  OFS.mk' (S.E.inverseImage (Ins.forget F G)) (S.M.inverseImage (Ins.forget F G))
    (by
      rintro x z f
      obtain ⟨y, e, m, he, hm, hfac⟩ := S.fact f.base
      have hfw : x.cell ≫ G.map f.base = F.map f.base ≫ z.cell := f.w
      obtain ⟨cy, ⟨hcy₁, hcy₂⟩, -⟩ :=
        horth e m he hm (x.cell ≫ G.map e) (F.map m ≫ z.cell) (by
          rw [Category.assoc, ← G.map_comp, hfac, hfw, ← Category.assoc, ← F.map_comp, hfac])
      refine ⟨⟨y, cy⟩, ⟨e, hcy₁.symm⟩, ⟨m, hcy₂⟩, he, hm, ?_⟩
      exact Ins.hom_ext (by simpa using hfac))
    (by
      rintro x v y w e m he hm f g hsq
      have hb : f.base ≫ m.base = e.base ≫ g.base := congrArg Ins.Hom.base hsq
      have he' : S.E e.base := he
      have hm' : S.M m.base := hm
      obtain ⟨θ, ⟨hθ₁, hθ₂⟩, hθuniq⟩ := S.orth he' hm' f.base g.base hb
      have hθ₁' : e.base ≫ θ = f.base := hθ₁
      have hθ₂' : θ ≫ m.base = g.base := hθ₂
      have hsq' : (x.cell ≫ G.map f.base) ≫ G.map m.base
          = F.map e.base ≫ (v.cell ≫ G.map g.base) :=
        calc (x.cell ≫ G.map f.base) ≫ G.map m.base
            = x.cell ≫ G.map (f.base ≫ m.base) := by rw [G.map_comp, Category.assoc]
          _ = x.cell ≫ G.map (e.base ≫ g.base) := by rw [hb]
          _ = (x.cell ≫ G.map e.base) ≫ G.map g.base := by rw [G.map_comp, Category.assoc]
          _ = F.map e.base ≫ v.cell ≫ G.map g.base := by rw [e.w, Category.assoc]
      obtain ⟨_, _, huniq⟩ :=
        horth _ _ he' hm' (x.cell ≫ G.map f.base) (v.cell ≫ G.map g.base) hsq'
      have key : v.cell ≫ G.map θ = F.map θ ≫ y.cell := by
        have hA : F.map e.base ≫ (v.cell ≫ G.map θ) = x.cell ≫ G.map f.base := by
          rw [← Category.assoc, ← e.w, Category.assoc, ← G.map_comp, hθ₁']
        have hA' : (v.cell ≫ G.map θ) ≫ G.map m.base = v.cell ≫ G.map g.base := by
          rw [Category.assoc, ← G.map_comp, hθ₂']
        have hB : F.map e.base ≫ (F.map θ ≫ y.cell) = x.cell ≫ G.map f.base := by
          rw [← Category.assoc, ← F.map_comp, hθ₁', f.w]
        have hB' : (F.map θ ≫ y.cell) ≫ G.map m.base = v.cell ≫ G.map g.base := by
          rw [Category.assoc, m.w, ← Category.assoc, ← F.map_comp, hθ₂', ← g.w]
        rw [huniq _ ⟨hA, hA'⟩, huniq _ ⟨hB, hB'⟩]
      refine ⟨⟨θ, key⟩, ⟨Ins.hom_ext hθ₁', Ins.hom_ext hθ₂'⟩, ?_⟩
      rintro k ⟨k1, k2⟩
      exact Ins.hom_ext (hθuniq k.base ⟨congrArg Ins.Hom.base k1, congrArg Ins.Hom.base k2⟩))
    (by
      have := S.e_isStableUnderRetracts
      infer_instance)
    (by
      have := S.m_isStableUnderRetracts
      infer_instance)

/-- **Theorem 6.3 (2)** ([forsman2026syntactic]): if `F(E') ⊥ G(M')`, then `(U⁻¹E', U⁻¹M')` is the
unique OFS on `Ins(F, G)` preserved by `U`. -/
theorem thm_6_3_2 (S : OFS C) (F G : C ⥤ D)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal (F.map e) (G.map m)) :
    ∃ P : OFS (Ins F G),
      (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P.E f ↔ S.E f.base) ∧
      (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P.M f ↔ S.M f.base) ∧
      ∀ P' : OFS (Ins F G),
        (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P'.E f → S.E f.base) →
        (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P'.M f → S.M f.base) → P' = P :=
  ⟨insOFS' S F G horth, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    fun _ hE hM => OFS.ext_of_le (fun _ _ _ h => hE _ h) (fun _ _ _ h => hM _ h)⟩

/-- The factorization system of Theorem 6.3 (3) on `Eq(η, θ)`, assuming only `F(E') ⊥_! G(M')`. -/
def equifOFS' (S : OFS C) {F G : C ⥤ D} (η θ : F ⟶ G)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 (F.map e) (G.map m)) : OFS (Equif η θ) :=
  OFS.mk' (S.E.inverseImage (Equif.forget η θ)) (S.M.inverseImage (Equif.forget η θ))
    (by
      rintro x z f
      obtain ⟨y, e, m, he, hm, hfac⟩ := S.fact f.hom
      have hx : η.app x.obj = θ.app x.obj := x.property
      have hz : η.app z.obj = θ.app z.obj := z.property
      have hsq : (η.app x.obj ≫ G.map e) ≫ G.map m = F.map e ≫ (F.map m ≫ η.app z.obj) := by
        rw [Category.assoc, ← G.map_comp, hfac, ← Category.assoc, ← F.map_comp, hfac,
          η.naturality]
      have hy : η.app y = θ.app y :=
        horth e m he hm _ _ hsq (η.app y) (θ.app y) (η.naturality e) (η.naturality m).symm
          (by rw [hx]; exact θ.naturality e) (by rw [hz]; exact (θ.naturality m).symm)
      refine ⟨⟨y, hy⟩, ObjectProperty.homMk e, ObjectProperty.homMk m, he, hm, ?_⟩
      ext
      simpa using hfac)
    (by
      rintro x v y w e m he hm f g hsq
      have hb : f.hom ≫ m.hom = e.hom ≫ g.hom := congrArg (Equif.forget η θ).map hsq
      obtain ⟨δ, ⟨hδ₁, hδ₂⟩, hδuniq⟩ := S.orth he hm f.hom g.hom hb
      have hδ₁' : e.hom ≫ δ = f.hom := hδ₁
      have hδ₂' : δ ≫ m.hom = g.hom := hδ₂
      refine ⟨ObjectProperty.homMk δ, ⟨?_, ?_⟩, ?_⟩
      · ext; simpa using hδ₁'
      · ext; simpa using hδ₂'
      rintro k ⟨k1, k2⟩
      have k1' : e.hom ≫ k.hom = f.hom := congrArg (Equif.forget η θ).map k1
      have k2' : k.hom ≫ m.hom = g.hom := congrArg (Equif.forget η θ).map k2
      ext
      simpa using hδuniq k.hom ⟨k1', k2'⟩)
    (by
      have := S.e_isStableUnderRetracts
      infer_instance)
    (by
      have := S.m_isStableUnderRetracts
      infer_instance)

/-- **Theorem 6.3 (3)** ([forsman2026syntactic]): if `F(E') ⊥_! G(M')`, the equifier carries a
unique OFS `(E⁻¹E', E⁻¹M')` preserved by its inclusion. -/
theorem thm_6_3_3 (S : OFS C) {F G : C ⥤ D} (η θ : F ⟶ G)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 (F.map e) (G.map m)) :
    ∃ P : OFS (Equif η θ),
      (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P.E f ↔ S.E f.hom) ∧
      (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P.M f ↔ S.M f.hom) ∧
      ∀ P' : OFS (Equif η θ),
        (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P'.E f → S.E f.hom) →
        (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P'.M f → S.M f.hom) → P' = P :=
  ⟨equifOFS' S η θ horth, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    fun _ hE hM => OFS.ext_of_le (fun _ _ _ h => hE _ h) (fun _ _ _ h => hM _ h)⟩

/-- Clause (1) of `regular_exact_transfer_of_preservesPullbacks`: an OFS on `Dc` lifted from
(extremal epis, monos) of `C`, with pullback-stable extremal epis, makes `Dc` regular. -/
theorem regular_transfer_of_ofs
    {Dc : Type u'} [Category.{v'} Dc] [HasFiniteLimits Dc] (U : Dc ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U]
    (hmono : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) → Mono f) :
    (∃ S : OFS Dc, (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.E f ↔ extremalEpi C (U.map f)) ∧
        (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.M f ↔ Mono (U.map f))) →
      (extremalEpi C).IsStableUnderBaseChange → IsRegularCat Dc := by
  have hmono_iff : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) ↔ Mono f :=
    fun _ _ f => ⟨hmono f, fun _ => inferInstance⟩
  rintro ⟨S, hE, hM⟩ hst
  have hSM : S.M = MorphismProperty.monomorphisms Dc := by
    ext x y f
    rw [hM f, hmono_iff f, MorphismProperty.monomorphisms.iff]
  refine ⟨inferInstance, ⟨S, hSM⟩, ?_⟩
  rw [← S.e_eq_extremalEpi hSM]
  constructor
  intro X Y Y' T f g f' g' sq hg
  exact (hE g').2 (hst.of_isPullback (sq.map U) ((hE g).1 hg))

/-- Clause (2) of `regular_exact_transfer_of_preservesPullbacks`: regularity transfers along a
conservative functor preserving regular epis, when `Dc` has coequalizers of kernel pairs. -/
theorem regular_transfer_of_preservesPullbacks
    {Dc : Type u'} [Category.{v'} Dc] [HasFiniteLimits Dc] (U : Dc ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U]
    (hmono : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) → Mono f) :
    HasCoequalizersOfKernelPairs Dc → U.ReflectsIsomorphisms →
      (∀ ⦃x y : Dc⦄ (f : x ⟶ y), Nonempty (RegularEpi f) → Nonempty (RegularEpi (U.map f))) →
      IsRegularCat C → IsRegularCat Dc := by
  have hmono_iff : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) ↔ Mono f :=
    fun _ _ f => ⟨hmono f, fun _ => inferInstance⟩
  intro hcoeq hcons hreg hC
  -- the factorization through the coequalizer of the kernel pair
  have canon : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), ∃ (Q : Dc) (e : x ⟶ Q) (m : Q ⟶ y),
      Nonempty (RegularEpi e) ∧ Mono m ∧ e ≫ m = f := by
    intro x y f
    have hk : IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
      IsPullback.of_hasPullback f f
    have := hcoeq f _ _ hk
    have he : RegularEpi (coequalizer.π (pullback.fst f f) (pullback.snd f f)) :=
      ⟨_, _, _, coequalizer.condition _ _, coequalizerIsCoequalizer _ _⟩
    refine ⟨_, _, coequalizer.desc f pullback.condition, ⟨he⟩, ?_, coequalizer.π_desc _ _⟩
    apply hmono
    obtain ⟨hUe⟩ := hreg _ ⟨he⟩
    exact mono_map_of_isKernelPair hC U (hk.map U) (coequalizer.condition _ _)
      (coequalizer.π_desc _ _) (extremalEpi_of_regularEpi' hUe)
  let S : OFS Dc := OFS.mk' (extremalEpi Dc) (MorphismProperty.monomorphisms Dc)
    (fun _ _ f => by
      obtain ⟨Q, e, m, ⟨he⟩, hm, hfac⟩ := canon f
      exact ⟨Q, e, m, extremalEpi_of_regularEpi' he, hm, hfac⟩)
    (fun _ _ _ _ _ m he hm => he m hm)
    (leftOrth_isStableUnderRetracts _) inferInstance
  refine regular_transfer_of_ofs U hmono
    ⟨S, fun x y f => ⟨fun hf => ?_, fun hf => ?_⟩, fun x y f => ?_⟩ hC.stable
  · -- an extremal epi of `Dc` is regular, so `U` maps it to a regular epi
    obtain ⟨Q, e, m, ⟨he⟩, hm, hfac⟩ := canon f
    have hfm : Orthogonal f m := hf m hm
    obtain ⟨k, ⟨-, hk2⟩, -⟩ := hfm e (𝟙 _) (by rw [hfac, Category.comp_id])
    have : IsSplitEpi m := ⟨⟨⟨k, hk2⟩⟩⟩
    have : IsIso m := isIso_of_mono_of_isSplitEpi m
    have hreg_f : RegularEpi f := by
      rw [← hfac]
      exact RegularEpi.ofArrowIso
        (Arrow.isoMk (Iso.refl x) (asIso m) (by simp) : Arrow.mk e ≅ Arrow.mk (e ≫ m)) he
    obtain ⟨hUf⟩ := hreg f ⟨hreg_f⟩
    exact extremalEpi_of_regularEpi' hUf
  · have := hcons
    exact extremalEpi_of_map_extremalEpi U hf
  · exact (MorphismProperty.monomorphisms.iff f).trans (hmono_iff f).symm

/-- The exactness clause (3) of `regular_exact_transfer_of_preservesPullbacks`, stated on its own
so that applying it does not unfold the conjunction. -/
theorem regular_exact_transfer_of_preservesPullbacks_exact
    {Dc : Type u'} [Category.{v'} Dc] [HasFiniteLimits Dc] (U : Dc ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U]
    (hmono : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) → Mono f) :
    (∀ ⦃R x : Dc⦄ (r s : R ⟶ x), IsEquivRel r s →
        HasCoequalizer r s ∧ PreservesColimit (parallelPair r s) U) →
      U.ReflectsIsomorphisms → IsExactCat C → IsExactCat Dc := by
  intro hce hcons hC
  have := hcons
  have hDreg : IsRegularCat Dc := by
    refine regular_transfer_of_preservesPullbacks U hmono
      (fun R x y f r s hk => (hce r s (IsKernelPair.isEquivRel hk)).1) hcons ?_
      hC.regular
    -- `U` preserves regular epis: a regular epi is the coequalizer of its kernel pair
    rintro x y f ⟨hf⟩
    have : EffectiveEpi f := hf.effectiveEpi
    have hcol : IsColimit (Cofork.ofπ f (pullback.condition (f := f) (g := f))) :=
      isColimitCoforkOfEffectiveEpi f _ (limit.isLimit _)
    have hk : IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
      IsPullback.of_hasPullback f f
    have := (hce _ _ (IsKernelPair.isEquivRel hk)).2
    exact ⟨⟨_, _, _, _, isColimitMapCoconeCoforkEquiv U _ (isColimitOfPreserves U hcol)⟩⟩
  refine ⟨hDreg, ?_⟩
  intro R c r s hrs
  obtain ⟨hcq, hpres⟩ := hce r s hrs
  have := hcq
  have := hpres
  have w : r ≫ coequalizer.π r s = s ≫ coequalizer.π r s := coequalizer.condition r s
  have hcol : IsColimit (Cofork.ofπ (coequalizer.π r s) w) := coequalizerIsCoequalizer r s
  have hUrs : IsEquivRel (U.map r) (U.map s) := IsEquivRel.map_of_preservesPullbacks U hrs
  obtain ⟨q, f₁, hk₁, ⟨hcol₁⟩⟩ := hC.effective _ _ hUrs
  have hcolU' : IsColimit (Cofork.ofπ (U.map (coequalizer.π r s))
      (show U.map r ≫ U.map (coequalizer.π r s) = U.map s ≫ U.map (coequalizer.π r s) by
        rw [← U.map_comp, ← U.map_comp, w])) :=
    isColimitMapCoconeCoforkEquiv U w (isColimitOfPreserves U hcol)
  have hfac : U.map (coequalizer.π r s) ≫ (hcolU'.coconePointUniqueUpToIso hcol₁).hom = f₁ := by
    have := IsColimit.comp_coconePointUniqueUpToIso_hom hcolU' hcol₁ WalkingParallelPair.one
    simpa using this
  have hkU : IsKernelPair (U.map (coequalizer.π r s)) (U.map r) (U.map s) := by
    have h2 : IsKernelPair (U.map (coequalizer.π r s) ≫
        (hcolU'.coconePointUniqueUpToIso hcol₁).hom) (U.map r) (U.map s) := by
      rw [hfac]; exact hk₁
    exact h2.cancel_right_of_mono
  have : ReflectsLimitsOfShape WalkingCospan U := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact ⟨_, _, isKernelPair_of_map U w hkU, ⟨hcol⟩⟩


/-- Working form of `lem_6_5`, with the OFS-based notions (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`, `UlmerBialgebras.IsEquivRel`, `UlmerBialgebras.extremalEpi`).
**Lemma 6.5** ([forsman2026syntactic]): transfer of regularity and exactness along a pullback
preserving functor reflecting monomorphisms out of a finitely complete category. -/
theorem regular_exact_transfer_of_preservesPullbacks {Dc : Type u'} [Category.{v'} Dc]
    [HasFiniteLimits Dc] (U : Dc ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U]
    (hmono : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) → Mono f) :
    -- (1)
    ((∃ S : OFS Dc, (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.E f ↔ extremalEpi C (U.map f)) ∧
        (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.M f ↔ Mono (U.map f))) →
      (extremalEpi C).IsStableUnderBaseChange → IsRegularCat Dc) ∧
    -- (2)
    (HasCoequalizersOfKernelPairs Dc → U.ReflectsIsomorphisms →
      (∀ ⦃x y : Dc⦄ (f : x ⟶ y), Nonempty (RegularEpi f) → Nonempty (RegularEpi (U.map f))) →
      IsRegularCat C → IsRegularCat Dc) ∧
    -- (3)
    ((∀ ⦃R x : Dc⦄ (r s : R ⟶ x), IsEquivRel r s →
        HasCoequalizer r s ∧ PreservesColimit (parallelPair r s) U) →
      U.ReflectsIsomorphisms → IsExactCat C → IsExactCat Dc) :=
  ⟨regular_transfer_of_ofs U hmono, regular_transfer_of_preservesPullbacks U hmono,
    regular_exact_transfer_of_preservesPullbacks_exact U hmono⟩


/-- **Definition 6.4, regularity** ([forsman2026syntactic]): Mathlib's regular categories
(`CategoryTheory.Regular`: finite limits, coequalizers of kernel pairs, and regular epimorphisms
stable under pullback) are the paper's: categories with finite limits and an orthogonal
factorization system `(E, M)` with `M` the monomorphisms and `E` stable under pullback. -/
theorem def_6_4_regular :
    Regular C ↔ HasFiniteLimits C ∧ ∃ S : OFS C,
      S.M = MorphismProperty.monomorphisms C ∧ S.E.IsStableUnderBaseChange := by
  rw [← isRegularCat_iff_regular]
  constructor
  · rintro ⟨hl, ⟨S, hS⟩, hst⟩
    exact ⟨hl, S, hS, by rwa [S.e_eq_extremalEpi hS]⟩
  · rintro ⟨hl, S, hS, hst⟩
    exact ⟨hl, ⟨S, hS⟩, by rwa [← S.e_eq_extremalEpi hS]⟩

/-- **Definition 6.4, exactness** ([forsman2026syntactic]): Barr-exact categories
(`CategoryTheory.BarrExact`: regular, with every Mathlib equivalence relation effective) are the
paper's exact categories: regular categories in which every internal equivalence relation (a
jointly monomorphic pair `r, s : R ⇉ c` inducing an equivalence relation on each `Hom(x, c)`,
`UlmerBialgebras.IsEquivRel`) is the kernel pair of some morphism. -/
theorem def_6_4_exact :
    BarrExact C ↔ Regular C ∧ ∀ ⦃R c : C⦄ (r s : R ⟶ c), IsEquivRel r s →
      ∃ (d : C) (f : c ⟶ d), IsKernelPair f r s := by
  constructor
  · intro h
    exact ⟨h.toRegular, fun _ _ _ _ hrs => BarrExact.exists_isKernelPair_of_isEquivRel hrs⟩
  · rintro ⟨_, h⟩
    exact BarrExact.mk' fun p₁ p₂ _ =>
      h p₁ p₂ ((isEquivRel_iff_isEquivalenceRelation p₁ p₂).2 inferInstance)

/-- **Lemma 6.5** ([forsman2026syntactic]): transfer of regularity and exactness along a pullback
preserving functor reflecting monomorphisms out of a finitely complete category. As in the paper,
`E'` is the class of extremal epimorphisms of `C` (Mathlib's `ExtremalEpi`) and `M'` the class of
monomorphisms; `C` is not assumed to have pullbacks. -/
theorem lem_6_5 {Dc : Type u'} [Category.{v'} Dc] [HasFiniteLimits Dc] (U : Dc ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U]
    (hmono : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) → Mono f) :
    -- (1)
    ((∃ S : OFS Dc, (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.E f ↔ ExtremalEpi (U.map f)) ∧
        (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.M f ↔ Mono (U.map f))) →
      MorphismProperty.IsStableUnderBaseChange
        (fun _ _ f => ExtremalEpi f : MorphismProperty C) →
      Regular Dc) ∧
    -- (2)
    (HasCoequalizersOfKernelPairs Dc → U.ReflectsIsomorphisms →
      (∀ ⦃x y : Dc⦄ (f : x ⟶ y), Nonempty (RegularEpi f) → Nonempty (RegularEpi (U.map f))) →
      Regular C → Regular Dc) ∧
    -- (3)
    ((∀ ⦃R x : Dc⦄ (r s : R ⟶ x), IsEquivalenceRelation r s →
        HasCoequalizer r s ∧ PreservesColimit (parallelPair r s) U) →
      U.ReflectsIsomorphisms → BarrExact C → BarrExact Dc) := by
  obtain ⟨-, h2, h3⟩ := regular_exact_transfer_of_preservesPullbacks U hmono
  refine ⟨?_, fun hc hcons hreg hC => isRegularCat_iff_regular.1
      (h2 hc hcons hreg (isRegularCat_iff_regular.2 hC)), fun hce hcons hC =>
    isExactCat_iff_barrExact.1 (h3 (fun _ _ r s hrs =>
      hce r s ((isEquivRel_iff_isEquivalenceRelation r s).1 hrs)) hcons
      (isExactCat_iff_barrExact.2 hC))⟩
  rintro ⟨S, hE, hM⟩ hst
  have hSM : S.M = MorphismProperty.monomorphisms Dc := by
    ext x y f
    rw [hM f, MorphismProperty.monomorphisms.iff]
    exact ⟨hmono f, fun _ => inferInstance⟩
  refine isRegularCat_iff_regular.1 ⟨inferInstance, ⟨S, hSM⟩, ?_⟩
  rw [← S.e_eq_extremalEpi hSM]
  constructor
  intro X Y Y' T f g f' g' sq hg
  exact (hE g').2 (hst.of_isPullback (sq.map U) ((hE g).1 hg))

end Sec6




end UlmerBialgebras.Paper
