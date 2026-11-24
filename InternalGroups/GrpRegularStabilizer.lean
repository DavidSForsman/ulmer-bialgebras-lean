module

public import InternalGroups.GrpKernelImage
public import InternalGroups.GrpStabilizerOps
public import Foundations.CategoryTheory.Grp.GrpReflexiveCoeq
public import Foundations.CategoryTheory.Grp.GrpLimits
public import Foundations.CategoryTheory.Limits.MapRegularEpi
public import Foundations.CategoryTheory.Factorization.RegularCharacterization

/-!
# Regular epimorphisms of `Grp C` are stably stabilizer-extremal

Under condition (S′)
(`InternalGroups.RegularEpiCosetCompHom C`), with no assumption that coset relations are
effective, the base change of a regular epimorphism `f : X ⟶ Y` of `Grp C` along a stabilizer
`n : N ⟶ Y` is stabilizer-extremal, in the form needed for the graph reduction: a factorization
`p₂ = k ≫ s` with `s ≫ n` a stabilizer of `Y` has `s` invertible.

The proof is that of `InternalGroups.le_grpImage_of_isPullback` and
`InternalGroups.isExtremalEpi_of_isPullback_of_mono`, with the effectivity of coset relations
replaced by `InternalGroups.stab_quot_le_of_grpIsStabilizer`, which holds for stabilizers.

These results are due to D. Forsman. They were announced by the author and will appear in a
forthcoming preprint.

## Main results

* `InternalGroups.grpImage_le_of_grpIsStabilizer`: the image of a morphism is contained in every
  stabilizer through which it factors;
* `InternalGroups.le_grpImage_of_isPullback_of_grpIsStabilizer`;
* `InternalGroups.isIso_of_isPullback_of_grpIsStabilizer`;
* `InternalGroups.regularEpiStablySEpi_stabilizers`: under (S′), regular epimorphisms of `Grp C`
  are stably stabilizer-extremal;
* `InternalGroups.regular_grp_of_monos_are_stabilizers`,
  `InternalGroups.isBarrExact_grp_of_monos_are_stabilizers`: under (S′), if every monomorphism of
  `Grp C` is a stabilizer, then `Grp C` is regular, and, with effective coset relations, Barr
  exact.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory CategoryTheory.LiftedOFS

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteLimits C]

/-! ## The class of stabilizers -/

variable (C) in
/-- **The class of stabilizers** of `Grp C` (`InternalGroups.GrpIsStabilizer`). -/
def stabilizers : MorphismProperty (Grp C) := fun _ _ m => GrpIsStabilizer m

/-- **The stabilizers contain the sections**: a split monomorphism is a regular monomorphism, and
regular monomorphisms of `Grp C` are stabilizers. -/
theorem containsSections_stabilizers :
    UlmerBialgebras.ClassEpi.ContainsSections (stabilizers C) := fun _ _ m hm => by
  have : IsSplitMono m := hm
  exact grpIsStabilizer_of_regularMono m (RegularMono.ofIsSplitMono m)

variable [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

variable {X Y : Grp C}

/-- **The image of a morphism of group objects is contained in every stabilizer through which the
morphism factors** (`grpImage_le` without the effectivity of coset relations). -/
theorem grpImage_le_of_grpIsStabilizer (f : X ⟶ Y) (s : SubGrp Y.X)
    (hs : GrpIsStabilizer s.inclGrp) (g : X.X ⟶ s.N) (hg : g ≫ s.i = f.hom.hom) :
    grpImage f ≤ s :=
  le_trans (galoisConnection_quot_stab.monotone_u
    (homQuot_le (isTerminalTensorUnit (C := C)) g hg)) (stab_quot_le_of_grpIsStabilizer s hs)

variable [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-- **The base change of a regular epimorphism along a stabilizer of the codomain**: the
stabilizer `N` is contained in the image of `p₁ ≫ f` (`le_grpImage_of_isPullback`, without the
effectivity of coset relations). -/
theorem le_grpImage_of_isPullback_of_grpIsStabilizer (hcomp : RegularEpiCosetCompHom C)
    {X Y N P : Grp C} {f : X ⟶ Y} {n : N ⟶ Y} {p₁ : P ⟶ X} {p₂ : P ⟶ N}
    (hf : IsRegularEpi f) [Mono n] (hn : GrpIsStabilizer n) (hsq : IsPullback p₁ p₂ f n) :
    ∃ w : N.X ⟶ (grpImage (p₁ ≫ f)).N, w ≫ (grpImage (p₁ ≫ f)).i = n.hom.hom := by
  have := hf
  have : Mono n.hom.hom := mono_hom_of_mono n
  -- the coset quotient of the subgroup object `N ≤ Y`, packaged by the three properties used
  obtain ⟨q, hqreg, hqn, hqfac⟩ : ∃ q : QuotMod Y.X, IsRegularEpi (f.hom.hom ≫ q.p.hom) ∧
      Kills q n.hom.hom ∧
      ∀ {T : C} {g : T ⟶ Y.X}, Kills q g → ∃ k : T ⟶ N.X, k ≫ n.hom.hom = g :=
    ⟨(⟨N.X, n.hom.hom⟩ : SubGrp Y.X).quot,
      hcomp hf _, kills_quot_i _,
      fun {_T _g} hg => factors_of_kills_quot _
        (stab_quot_le_of_grpIsStabilizer _ (hn.of_iso (Iso.refl _) (Category.id_comp _))) hg⟩
  -- the quotient of `Y` by the image of `p₁ ≫ f`
  obtain ⟨q', hq'kill, hq'fac⟩ : ∃ q' : QuotMod Y.X, Kills q' (p₁ ≫ f).hom.hom ∧
      ∀ {T : C} {g : T ⟶ Y.X}, Kills q' g →
        ∃ k : T ⟶ (grpImage (p₁ ≫ f)).N, k ≫ (grpImage (p₁ ≫ f)).i = g :=
    ⟨homQuot isTerminalTensorUnit (p₁ ≫ f).hom.hom, kills_grpImage (p₁ ≫ f),
      fun {_T g} hg => (kills_iff_factors _ g).1 hg⟩
  -- `U f ≫ p` is a regular epimorphism of `C`, hence the coequalizer of its kernel pair
  have hv : IsRegularEpi (f.hom.hom ≫ q.p.hom) := hqreg
  obtain ⟨R, a, b, hkp⟩ : ∃ (R : C) (a b : R ⟶ X.X), IsKernelPair (f.hom.hom ≫ q.p.hom) a b :=
    ⟨_, _, _, IsKernelPair.of_hasPullback _⟩
  have hcolim : IsColimit (Cofork.ofπ (f.hom.hom ≫ q.p.hom) hkp.w) := hkp.toCoequalizer'
  have halbe : (a ≫ f.hom.hom) ≫ q.p.hom = (b ≫ f.hom.hom) ≫ q.p.hom := by
    rw [Category.assoc, Category.assoc]; exact hkp.w
  -- the difference of the two legs is killed by the coset quotient, so it factors through `N`
  obtain ⟨psi, hpsi⟩ := hqfac ((kills_inv_mul_iff q _ _).2 halbe)
  have hdeX : (a⁻¹ * b : R ⟶ X.X) ≫ f.hom.hom = (a ≫ f.hom.hom)⁻¹ * (b ≫ f.hom.hom) := by
    rw [MonObj.mul_comp, GrpObj.inv_comp]
  have hsqC : IsPullback p₁.hom.hom p₂.hom.hom f.hom.hom n.hom.hom := hsq.map (Grp.forget C)
  obtain ⟨d, hd₁⟩ : ∃ d : R ⟶ P.X, d ≫ p₁.hom.hom = a⁻¹ * b :=
    ⟨hsqC.lift (a⁻¹ * b) psi (hdeX.trans hpsi.symm), hsqC.lift_fst _ _ _⟩
  -- hence it is also killed by the quotient by the image of `p₁ ≫ f`
  have hdeq' : Kills q' ((a ≫ f.hom.hom)⁻¹ * (b ≫ f.hom.hom)) := by
    have hk := hq'kill.comp d
    have hdd : d ≫ (p₁ ≫ f).hom.hom = (a ≫ f.hom.hom)⁻¹ * (b ≫ f.hom.hom) := by
      rw [show (p₁ ≫ f).hom.hom = p₁.hom.hom ≫ f.hom.hom from rfl, ← Category.assoc, hd₁, hdeX]
    rwa [hdd] at hk
  have hab : a ≫ (f.hom.hom ≫ q'.p.hom) = b ≫ (f.hom.hom ≫ q'.p.hom) := by
    rw [← Category.assoc, ← Category.assoc]
    exact (kills_inv_mul_iff q' _ _).1 hdeq'
  -- descend along the coequalizer
  have hdesc : (f.hom.hom ≫ q.p.hom) ≫ hcolim.desc (Cofork.ofπ (f.hom.hom ≫ q'.p.hom) hab)
      = f.hom.hom ≫ q'.p.hom := Cofork.IsColimit.π_desc hcolim
  have := isRegularEpi_hom_of_isRegularEpi f hf
  have : Epi f.hom.hom := inferInstance
  have hpp : q.p.hom ≫ hcolim.desc (Cofork.ofπ (f.hom.hom ≫ q'.p.hom) hab) = q'.p.hom := by
    refine (cancel_epi f.hom.hom).1 ?_
    rw [← Category.assoc]
    exact hdesc
  -- so `n` is killed by the quotient by the image of `p₁ ≫ f`
  have hqn' : n.hom.hom ≫ q.p.hom = pt q N.X := hqn
  refine hq'fac (?_ : n.hom.hom ≫ q'.p.hom = pt q' N.X)
  rw [← hpp, ← Category.assoc, hqn', pt, pt, Category.assoc]
  congr 1
  rw [QuotMod.basePoint, QuotMod.basePoint, Category.assoc, hpp]


/-- **The base change of a regular epimorphism along a stabilizer is stabilizer-extremal**, in
the form used by the graph reduction: if `p₂ = k ≫ s` and `s ≫ n` is a stabilizer of `Y`, then `s`
is an isomorphism. -/
theorem isIso_of_isPullback_of_grpIsStabilizer (hcomp : RegularEpiCosetCompHom C)
    {N P M : Grp C} {f : X ⟶ Y} {n : N ⟶ Y} {p₁ : P ⟶ X} {p₂ : P ⟶ N}
    (hf : IsRegularEpi f) (hn : GrpIsStabilizer n) (hsq : IsPullback p₁ p₂ f n)
    {k : P ⟶ M} {s : M ⟶ N} (hks : k ≫ s = p₂) (hsn : GrpIsStabilizer (s ≫ n)) : IsIso s := by
  have : Mono n.hom.hom := hn.mono_hom
  have : Mono n := (Grp.forget C).mono_of_mono_map this
  have hmsn : Mono (s ≫ n).hom.hom := hsn.mono_hom
  have : Mono s.hom.hom := by
    have : Mono (s.hom.hom ≫ n.hom.hom) := hmsn
    exact mono_of_mono s.hom.hom n.hom.hom
  -- `N` is contained in the image of `p₁ ≫ f`
  obtain ⟨w, hw⟩ := le_grpImage_of_isPullback_of_grpIsStabilizer hcomp hf hn hsq
  -- and the image is contained in the stabilizer `s ≫ n`, through which `p₁ ≫ f` factors
  let t : SubGrp Y.X := ⟨M.X, (s ≫ n).hom.hom⟩
  have ht : GrpIsStabilizer t.inclGrp := hsn.of_iso (Iso.refl _) (Category.id_comp _)
  have hfac : k.hom.hom ≫ s.hom.hom ≫ n.hom.hom = (p₁ ≫ f).hom.hom := by
    rw [hsq.w, ← hks]
    simp
  obtain ⟨u, hu⟩ := grpImage_le_of_grpIsStabilizer (p₁ ≫ f) t ht k.hom.hom hfac
  -- so `n` factors through `s ≫ n`, and `s` is a split epimorphism
  let u' : (grpImage (p₁ ≫ f)).N ⟶ M.X := u
  have hu' : u' ≫ s.hom.hom ≫ n.hom.hom = (grpImage (p₁ ≫ f)).i := hu
  let v : N.X ⟶ M.X := w ≫ u'
  have hv : v ≫ s.hom.hom = 𝟙 _ := by
    refine (cancel_mono n.hom.hom).1 ?_
    rw [Category.assoc, Category.id_comp]
    exact (Category.assoc w u' _).trans ((w ≫= hu').trans hw)
  have : IsSplitEpi s.hom.hom := ⟨⟨v, hv⟩⟩
  have : IsIso s.hom.hom := isIso_of_mono_of_isSplitEpi _
  exact isIso_of_isIso_hom s this
/-! ## `f × Z` is a regular epimorphism -/

section Braided

variable [BraidedCategory C]

omit [HasFiniteLimits C] in
/-- **`- ⊗ Z` preserves reflexive coequalizers in `Grp C`**: they are computed in `C`
(`CategoryTheory.GrpReflexiveCoeq`), where `- ⊗ Z.X` preserves them. -/
theorem preservesReflexiveCoeq_tensorRight_grp (Z : Grp C) :
    PreservesReflexiveCoeq (tensorRight Z) where
  preserves {M N} u v h := by
    have hu : IsReflexivePair u.hom.hom v.hom.hom :=
      CategoryTheory.isReflexivePair_map (Grp.forget C) h
    have hZ : IsReflexivePair (u ▷ Z) (v ▷ Z) := isReflexivePair_map (tensorRight Z) h
    have : PreservesColimit (parallelPair u v) (Grp.forget C) :=
      PreservesReflexiveCoeq.preserves (F := Grp.forget C) u v h
    have hP₁ : PreservesColimit (parallelPair (u ▷ Z) (v ▷ Z)) (Grp.forget C) :=
      PreservesReflexiveCoeq.preserves (F := Grp.forget C) _ _ hZ
    have hH : HasColimit (parallelPair (u ▷ Z) (v ▷ Z)) := inferInstance
    let K := parallelPair u v ⋙ tensorRight Z
    have : HasColimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) := hH
    have : HasColimit K := hasColimit_of_iso (diagramIsoParallelPair K)
    have : PreservesColimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) (Grp.forget C) := hP₁
    have : PreservesColimit K (Grp.forget C) :=
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair K).symm
    have : ReflectsColimit K (Grp.forget C) := reflectsColimit_of_reflectsIsomorphisms _ _
    refine ⟨fun {c} hc => ⟨isColimitOfReflects (Grp.forget C) ?_⟩⟩
    have h₁ := isColimitOfPreserves (Grp.forget C) hc
    let L := parallelPair u v ⋙ Grp.forget C
    have : PreservesColimit (parallelPair (L.map WalkingParallelPairHom.left)
        (L.map WalkingParallelPairHom.right)) (tensorRight Z.X) :=
      PreservesReflexiveCoeq.preserves (F := tensorRight Z.X) _ _ hu
    have : PreservesColimit L (tensorRight Z.X) :=
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair L).symm
    exact isColimitOfPreserves (tensorRight Z.X) h₁

/-- **`f ⊗ Z` is a regular epimorphism of `Grp C`** when `f` is. -/
theorem isRegularEpi_whiskerRight (Z : Grp C) {X Y : Grp C} (f : X ⟶ Y) (hf : IsRegularEpi f) :
    IsRegularEpi (f ▷ Z) := by
  have := preservesReflexiveCoeq_tensorRight_grp Z
  have := hf
  exact isRegularEpi_map_of_preservesReflexiveCoeq (tensorRight Z) f

end Braided

/-! ## The graph reduction -/

section Graph

variable {D : Type*} [Category D] [CartesianMonoidalCategory D]

/-- **The pullback of `f` along `g` is the pullback of `f ⊗ Z` along the graph `⟨g, 𝟙⟩`**
(`CategoryTheory.isPullback_prodMap_graph`, for the cartesian product). -/
theorem isPullback_whiskerRight_graph {A B Z P : D} {f : A ⟶ B} {g : Z ⟶ B} {p₁ : P ⟶ A}
    {p₂ : P ⟶ Z} (h : IsPullback p₁ p₂ f g) :
    IsPullback (lift p₁ p₂) p₂ (f ▷ Z) (lift g (𝟙 Z)) := by
  have hcomm : lift p₁ p₂ ≫ f ▷ Z = p₂ ≫ lift g (𝟙 Z) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;> simp [h.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm
    (fun c => h.lift (c.fst ≫ fst A Z) c.snd ?_) ?_ ?_ ?_)
  · have := c.condition =≫ fst B Z
    simpa using this
  · intro c
    have h2 : c.fst ≫ snd A Z = c.snd := by
      have := c.condition =≫ snd B Z
      simpa using this
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [h.lift_fst]
    · simp [h.lift_snd, h2]
  · intro c
    simp [h.lift_snd]
  · intro c m hm₁ hm₂
    refine h.hom_ext ?_ ?_
    · have := hm₁ =≫ fst A Z
      simpa using this
    · simpa using hm₂

end Graph

/-! ## Regular epimorphisms of `Grp C` are stably stabilizer-extremal -/

/-- **Under (S′), the regular epimorphisms of `Grp C` are stably stabilizer-extremal.** The base
change along `g : Z ⟶ Y` is the base change of `f ⊗ Z`, again a regular epimorphism, along the
graph `⟨g, 𝟙⟩`, a section and hence a stabilizer; a stabilizer of `Z` along the graph is a
stabilizer of `Y ⊗ Z` (`grpIsStabilizer_comp_section`), so
`isIso_of_isPullback_of_grpIsStabilizer` applies. -/
theorem regularEpiStablySEpi_stabilizers (hcomp : RegularEpiCosetCompHom C) :
    UlmerBialgebras.ClassEpi.RegularEpiStablySEpi (stabilizers C) := by
  let := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  intro X Y f hf P Z fst' snd' g hsq M k s hs hks
  have hsq' := isPullback_whiskerRight_graph hsq
  have hfZ := isRegularEpi_whiskerRight Z f hf
  have : IsSplitMono (lift g (𝟙 Z)) := IsSplitMono.mk' ⟨snd Y Z, lift_snd _ _⟩
  have hσ : GrpIsStabilizer (lift g (𝟙 Z)) := containsSections_stabilizers _ this
  have hsσ : GrpIsStabilizer (s ≫ lift g (𝟙 Z)) :=
    grpIsStabilizer_comp_section (tensorProductIsBinaryProduct Y Z) (lift_fst _ _) (lift_snd _ _)
      hs
  exact isIso_of_isPullback_of_grpIsStabilizer hcomp hfZ hσ hsq' hks hsσ

/-- **`Grp C` has a regular epi–mono factorization under (S′)**: regular epimorphisms are stably
stabilizer-extremal, and the stabilizers contain the sections. -/
theorem exists_regularEpi_mono_factorization_grp (hcomp : RegularEpiCosetCompHom C)
    [HasFiniteLimits (Grp C)] (hkc : UlmerBialgebras.HasCoequalizersOfKernelPairs (Grp C))
    {X Y : Grp C} (f : X ⟶ Y) :
    ∃ (I : Grp C) (e : X ⟶ I) (m : I ⟶ Y), IsRegularEpi e ∧ Mono m ∧ e ≫ m = f :=
  UlmerBialgebras.ClassEpi.exists_regularEpi_mono_factorization hkc containsSections_stabilizers
    (regularEpiStablySEpi_stabilizers hcomp) f

/-- **`Grp C` is regular under (S′) when every monomorphism of `Grp C` is a stabilizer**: then
the regular epimorphisms are stably extremal (`UlmerBialgebras.regular_iff_classEpi`). -/
theorem regular_grp_of_monos_are_stabilizers (hcomp : RegularEpiCosetCompHom C)
    [HasFiniteLimits (Grp C)] (hkc : UlmerBialgebras.HasCoequalizersOfKernelPairs (Grp C))
    (hmono : ∀ {A B : Grp C} (m : A ⟶ B), Mono m → GrpIsStabilizer m) : Regular (Grp C) :=
  UlmerBialgebras.regular_iff_classEpi.2 ⟨hkc, fun _ _ f hf =>
    (regularEpiStablySEpi_stabilizers hcomp f hf).anti (fun _ _ m hm => hmono m hm)⟩

/-- **`Grp C` has coequalizers of kernel pairs**: a kernel pair is a reflexive pair. -/
theorem hasCoequalizersOfKernelPairs_grp :
    UlmerBialgebras.HasCoequalizersOfKernelPairs (Grp C) := fun _ _ f =>
  Internal.hasCoequalizer_of_isKernelPair_of_hasReflexiveCoequalizers
    (IsPullback.of_hasPullback f f)

/-- **`Grp C` is Barr exact under (S′) when every monomorphism of `Grp C` is a stabilizer and the
coset relations are effective**: `Grp C` is regular (`regular_grp_of_monos_are_stabilizers`), and
`CosetInjective` makes the internal equivalence relations effective. The two hypotheses on
monomorphisms and coset relations are equivalent
(`InternalGroups.cosetInjective_iff_monos_are_stabilizers`), which gives the form without
`CosetInjective`, `InternalGroups.isBarrExact_grp_of_regularEpiCosetCompHom_of_monos`. -/
theorem isBarrExact_grp_of_monos_are_stabilizers (hinj : CosetInjective C)
    (hcomp : RegularEpiCosetCompHom C)
    (hmono : ∀ {A B : Grp C} (m : A ⟶ B), Mono m → GrpIsStabilizer m) : IsBarrExact (Grp C) :=
  isBarrExact_grp_of_cosetInjective_of_stableRegularEpi
    (regular_grp_of_monos_are_stabilizers hcomp hasCoequalizersOfKernelPairs_grp
      hmono).regularEpiIsStableUnderBaseChange hinj

end InternalGroups
