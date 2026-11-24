module

public import UlmerBialgebras.Proofs.Sec6.CocommStructure
public import UlmerBialgebras.Proofs.Sec6.GrpDescent
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Descent of exactness for cocommutative Hopf monoids

Let `V` be a symmetric monoidal category with reflexive coequalizers and coreflexive equalizers,
both preserved by the tensor product in each variable. No abelian or finite-limit hypothesis is
made on `V`. A braided strong monoidal functor `L : V ⥤ W` induces a functor
`CommComon V ⥤ CommComon W` on cocommutative comonoids. If `L` preserves reflexive coequalizers
and coreflexive equalizers, the induced functor preserves finite limits and reflexive
coequalizers. Descent along a jointly conservative family of such functors then follows from
`GrpDescent.isBarrExact_grp`.

## Main results

* `UlmerBialgebras.Paper.ComonDescent.mapCC`: the functor `CommComon V ⥤ CommComon W` induced by
  `L`.
* `UlmerBialgebras.Paper.ComonDescent.commComonEquiv`: a braided monoidal equivalence `V ≌ W` whose
  unit and counit are monoidal induces `CommComon V ≌ CommComon W`.
* `UlmerBialgebras.Paper.ComonDescent.mapCC_preservesFiniteLimits`: if `L` preserves coreflexive
  equalizers, `mapCC L` preserves finite limits.
* `UlmerBialgebras.Paper.ComonDescent.mapCC_preservesReflexiveCoeq`: if `L` preserves reflexive
  coequalizers, so does `mapCC L`.
* `UlmerBialgebras.Paper.ComonDescent.isBarrExact_cocommHopf`: for a jointly conservative family of
  braided functors `L i : V ⥤ W i` preserving coreflexive equalizers and reflexive coequalizers, if
  every `Grp (CommComon (W i))` is Barr-exact, so is `Grp (CommComon V)` (the descent step in the
  proof of Corollary 6.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.10 and Corollary 6.11 (case `A = Mod_R`)
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Lemma 4.1
-/

@[expose] public section

universe v u v' u'

namespace UlmerBialgebras.Paper.ComonDescent

open CategoryTheory Limits MonoidalCategory ComonObj Functor.OplaxMonoidal Functor.LaxMonoidal

attribute [local instance] Functor.obj.instComonObj

variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [SymmetricCategory V]
  {W : Type u'} [Category.{v'} W] [MonoidalCategory W] [SymmetricCategory W]
  (L : V ⥤ W) [L.Braided]

/-- A braided strong monoidal functor `L` sends a cocommutative comonoid `X` to a cocommutative
comonoid `L X` (with comultiplication `L(Δ) ≫ δ`). -/
instance isCommComonObj_obj (X : V) [ComonObj X] [IsCommComonObj X] :
    IsCommComonObj (L.obj X) where
  comul_comm := by
    have h : L.map (β_ X X).hom = δ L X X ≫ (β_ (L.obj X) (L.obj X)).hom ≫ μ L X X :=
      L.map_braiding X X
    have h2 : δ L X X ≫ (β_ (L.obj X) (L.obj X)).hom = L.map (β_ X X).hom ≫ δ L X X := by
      rw [h]; simp
    rw [Functor.obj.Δ_def, Category.assoc, h2, ← L.map_comp_assoc, IsCommComonObj.comul_comm]

/-- The functor induced on cocommutative comonoids. -/
noncomputable def mapCC : CategoryTheory.CommComon V ⥤ CategoryTheory.CommComon W where
  obj A := ⟨L.obj A.X⟩
  map f := ⟨(L.mapComon.map f.hom)⟩
  map_id A := by ext; exact L.map_id _
  map_comp f g := by ext; exact L.map_comp _ _

/-- `mapCC L` lifts `L` along the forgetful functors: `mapCC L ⋙ forget = forget ⋙ L`
(definitionally). -/
lemma mapCC_forget : mapCC L ⋙ CommComon.forgetV W = CommComon.forgetV V ⋙ L := rfl

/-! ## Equivalences of cocommutative comonoids -/

section Equiv

variable {V₁ : Type*} [Category V₁] [MonoidalCategory V₁] {W₁ : Type*} [Category W₁]
  [MonoidalCategory W₁]

section NatTrans

variable {F G : V₁ ⥤ W₁} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G) [NatTrans.IsMonoidal τ]
  (X : V₁) [ComonObj X]

/-- A monoidal natural transformation commutes with the induced counits. -/
lemma app_comp_map_counit :
    τ.app X ≫ G.map ε[X] ≫ Functor.OplaxMonoidal.η G = F.map ε[X] ≫ Functor.OplaxMonoidal.η F := by
  have h : τ.app (𝟙_ V₁) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
    rw [← cancel_epi (Functor.LaxMonoidal.ε F), ← Category.assoc, NatTrans.IsMonoidal.unit,
      Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  rw [← τ.naturality_assoc, h]

/-- A monoidal natural transformation commutes with the induced comultiplications. -/
lemma app_comp_map_comul :
    τ.app X ≫ G.map Δ[X] ≫ Functor.OplaxMonoidal.δ G X X =
      (F.map Δ[X] ≫ Functor.OplaxMonoidal.δ F X X) ≫ (τ.app X ⊗ₘ τ.app X) := by
  have h : τ.app (X ⊗ X) ≫ Functor.OplaxMonoidal.δ G X X =
      Functor.OplaxMonoidal.δ F X X ≫ (τ.app X ⊗ₘ τ.app X) := by
    rw [← cancel_epi (Functor.LaxMonoidal.μ F X X), ← Category.assoc, NatTrans.IsMonoidal.tensor,
      Category.assoc, Functor.Monoidal.μ_δ, Functor.Monoidal.μ_δ_assoc, Category.comp_id]
  rw [← τ.naturality_assoc, h, Category.assoc]

end NatTrans

variable [SymmetricCategory V₁] [SymmetricCategory W₁]

/-- An isomorphism of cocommutative comonoids from an isomorphism of the underlying objects
that is compatible with the counits and comultiplications. -/
@[simps]
noncomputable def commComonIsoMk {A B : CategoryTheory.CommComon V₁} (f : A.X ≅ B.X)
    (f_counit : f.hom ≫ ε[B.X] = ε[A.X]) (f_comul : f.hom ≫ Δ[B.X] = Δ[A.X] ≫ (f.hom ⊗ₘ f.hom)) :
    A ≅ B where
  hom := InducedCategory.homMk (Comon.mkIso f f_counit f_comul).hom
  inv := InducedCategory.homMk (Comon.mkIso f f_counit f_comul).inv
  hom_inv_id := by ext; exact f.hom_inv_id
  inv_hom_id := by ext; exact f.inv_hom_id

/-- The underlying morphism of `commComonIsoMk f _ _` is `f.hom`. -/
@[simp] lemma commComonIsoMk_hom_hom_hom {A B : CategoryTheory.CommComon V₁} (f : A.X ≅ B.X)
    (f_counit : f.hom ≫ ε[B.X] = ε[A.X]) (f_comul : f.hom ≫ Δ[B.X] = Δ[A.X] ≫ (f.hom ⊗ₘ f.hom)) :
    (commComonIsoMk f f_counit f_comul).hom.hom.hom = f.hom := rfl

/-- The counit of `mapCC G (mapCC F A)`. -/
lemma counit_mapCC_comp_obj {U₁ : Type*} [Category U₁] [MonoidalCategory U₁] [SymmetricCategory U₁]
    (F : V₁ ⥤ W₁) [F.Braided] (G : W₁ ⥤ U₁) [G.Braided] (A : CategoryTheory.CommComon V₁) :
    @ComonObj.counit U₁ _ _ ((mapCC F ⋙ mapCC G).obj A).X ((mapCC F ⋙ mapCC G).obj A).comon =
      G.map (F.map ε[A.X] ≫ Functor.OplaxMonoidal.η F) ≫ Functor.OplaxMonoidal.η G := rfl

/-- The comultiplication of `mapCC G (mapCC F A)`. -/
lemma comul_mapCC_comp_obj {U₁ : Type*} [Category U₁] [MonoidalCategory U₁] [SymmetricCategory U₁]
    (F : V₁ ⥤ W₁) [F.Braided] (G : W₁ ⥤ U₁) [G.Braided] (A : CategoryTheory.CommComon V₁) :
    @ComonObj.comul U₁ _ _ ((mapCC F ⋙ mapCC G).obj A).X ((mapCC F ⋙ mapCC G).obj A).comon =
      G.map (F.map Δ[A.X] ≫ Functor.OplaxMonoidal.δ F A.X A.X) ≫
        Functor.OplaxMonoidal.δ G (F.obj A.X) (F.obj A.X) := rfl

variable (e : V₁ ≌ W₁) [e.functor.Braided] [e.inverse.Braided]

section

include e

/-- The unit of `e` is compatible with the counits of `A` and of
`mapCC e.inverse (mapCC e.functor A)`. -/
lemma unitIso_app_hom_comp_counit [NatTrans.IsMonoidal e.unit] (A : CategoryTheory.CommComon V₁) :
    (e.unitIso.app A.X).hom ≫
        @ComonObj.counit V₁ _ _ ((mapCC e.functor ⋙ mapCC e.inverse).obj A).X
          ((mapCC e.functor ⋙ mapCC e.inverse).obj A).comon = ε[A.X] := by
  have h := app_comp_map_counit e.unit A.X
  simp only [Functor.comp_map, Functor.id_map, Functor.OplaxMonoidal.comp_η,
    Functor.OplaxMonoidal.id_η, Category.comp_id] at h
  rw [counit_mapCC_comp_obj, Functor.map_comp, Category.assoc]
  exact h

/-- The unit of `e` is compatible with the comultiplications of `A` and of
`mapCC e.inverse (mapCC e.functor A)`. -/
lemma unitIso_app_hom_comp_comul [NatTrans.IsMonoidal e.unit] (A : CategoryTheory.CommComon V₁) :
    (e.unitIso.app A.X).hom ≫
        @ComonObj.comul V₁ _ _ ((mapCC e.functor ⋙ mapCC e.inverse).obj A).X
          ((mapCC e.functor ⋙ mapCC e.inverse).obj A).comon =
      Δ[A.X] ≫ ((e.unitIso.app A.X).hom ⊗ₘ (e.unitIso.app A.X).hom) := by
  have h := app_comp_map_comul e.unit A.X
  simp only [Functor.comp_map, Functor.id_map, Functor.OplaxMonoidal.comp_δ,
    Functor.OplaxMonoidal.id_δ, Category.comp_id] at h
  rw [comul_mapCC_comp_obj, Functor.map_comp, Category.assoc]
  exact h

/-- The counit of `e` is compatible with the counits of `mapCC e.functor (mapCC e.inverse B)`
and of `B`. -/
lemma counitIso_app_hom_comp_counit [NatTrans.IsMonoidal e.counit]
    (B : CategoryTheory.CommComon W₁) :
    (e.counitIso.app B.X).hom ≫ ε[B.X] =
      @ComonObj.counit W₁ _ _ ((mapCC e.inverse ⋙ mapCC e.functor).obj B).X
        ((mapCC e.inverse ⋙ mapCC e.functor).obj B).comon := by
  have h := app_comp_map_counit e.counit B.X
  simp only [Functor.comp_map, Functor.id_map, Functor.OplaxMonoidal.comp_η,
    Functor.OplaxMonoidal.id_η, Category.comp_id] at h
  rw [counit_mapCC_comp_obj, Functor.map_comp, Category.assoc]
  exact h

/-- The counit of `e` is compatible with the comultiplications of
`mapCC e.functor (mapCC e.inverse B)` and of `B`. -/
lemma counitIso_app_hom_comp_comul [NatTrans.IsMonoidal e.counit]
    (B : CategoryTheory.CommComon W₁) :
    (e.counitIso.app B.X).hom ≫ Δ[B.X] =
      @ComonObj.comul W₁ _ _ ((mapCC e.inverse ⋙ mapCC e.functor).obj B).X
          ((mapCC e.inverse ⋙ mapCC e.functor).obj B).comon ≫
        ((e.counitIso.app B.X).hom ⊗ₘ (e.counitIso.app B.X).hom) := by
  have h := app_comp_map_comul e.counit B.X
  simp only [Functor.comp_map, Functor.id_map, Functor.OplaxMonoidal.comp_δ,
    Functor.OplaxMonoidal.id_δ, Category.comp_id] at h
  rw [comul_mapCC_comp_obj, Functor.map_comp, Category.assoc]
  exact h

end

/-- **A braided monoidal equivalence `V₁ ≌ W₁` whose unit and counit are monoidal induces an
equivalence of cocommutative comonoids** `CommComon V₁ ≌ CommComon W₁`. -/
noncomputable def commComonEquiv [NatTrans.IsMonoidal e.unit] [NatTrans.IsMonoidal e.counit] :
    CategoryTheory.CommComon V₁ ≌ CategoryTheory.CommComon W₁ where
  functor := mapCC e.functor
  inverse := mapCC e.inverse
  unitIso := NatIso.ofComponents (fun A => commComonIsoMk (e.unitIso.app A.X)
    (unitIso_app_hom_comp_counit e A) (unitIso_app_hom_comp_comul e A))
    fun f => by ext; exact e.unit.naturality f.hom.hom
  counitIso := NatIso.ofComponents (fun B => commComonIsoMk (e.counitIso.app B.X)
    (counitIso_app_hom_comp_counit e B) (counitIso_app_hom_comp_comul e B))
    fun f => by ext; exact e.counit.naturality f.hom.hom
  functor_unitIso_comp A := by
    ext
    exact e.functor_unitIso_comp A.X

end Equiv

/-! ## Limits in `CommComon` -/

section Lim

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- A cocommutative comonoid whose counit is invertible is terminal. -/
noncomputable def isTerminalOfIsIsoCounit (T : CategoryTheory.CommComon C)
    [IsIso ε[T.X]] : IsTerminal T := by
  let f : T ⟶ CategoryTheory.CommComon.trivial C := CommComon.trivialIsTerminal.from T
  have hf : f.hom.hom = ε[T.X] := by
    have := IsComonHom.hom_counit (f := f.hom.hom)
    exact (Category.comp_id _).symm.trans this
  have hiso : IsIso f.hom.hom := by rw [hf]; exact ‹IsIso ε[T.X]›
  haveI : IsIso ((CommComon.forgetV C).map f) := hiso
  haveI : IsIso f := isIso_of_reflects_iso f (CommComon.forgetV C)
  exact CommComon.trivialIsTerminal.ofIso (asIso f).symm

/-- A binary fan of cocommutative comonoids is a product as soon as its canonical comparison
`Δ ≫ (p ⊗ q)` with the tensor product is invertible. -/
noncomputable def isLimitOfIsIsoLift {X Y P : CategoryTheory.CommComon C} (p : P ⟶ X)
    (q : P ⟶ Y) (hiso : IsIso (Δ[P.X] ≫ (p.hom.hom ⊗ₘ q.hom.hom))) :
    IsLimit (BinaryFan.mk p q) := by
  let lim := CommComon.binaryFanIsLimit X Y
  let ℓ : P ⟶ (CommComon.binaryFan X Y).pt := lim.lift (BinaryFan.mk p q)
  haveI : IsIso ((CommComon.forgetV C).map ℓ) := hiso
  haveI : IsIso ℓ := isIso_of_reflects_iso ℓ (CommComon.forgetV C)
  have h₁ : ℓ ≫ (CommComon.binaryFan X Y).fst = p := lim.fac _ ⟨.left⟩
  have h₂ : ℓ ≫ (CommComon.binaryFan X Y).snd = q := lim.fac _ ⟨.right⟩
  refine BinaryFan.isLimitMk (fun s => lim.lift s ≫ inv ℓ) (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_)
  · simp only [Category.assoc]
    rw [← h₁, IsIso.inv_hom_id_assoc]; exact lim.fac s ⟨.left⟩
  · simp only [Category.assoc]
    rw [← h₂, IsIso.inv_hom_id_assoc]; exact lim.fac s ⟨.right⟩
  · rw [IsIso.eq_comp_inv]
    refine BinaryFan.IsLimit.hom_ext lim ?_ ?_
    · rw [Category.assoc, h₁, hm₁]; exact (lim.fac s ⟨.left⟩).symm
    · rw [Category.assoc, h₂, hm₂]; exact (lim.fac s ⟨.right⟩).symm

end Lim

/-! ## Equalizers from binary products and coreflexive equalizers -/

section Gen

variable {C : Type*} [Category C] [HasBinaryProducts C] [HasEqualizers C] {D : Type*}
  [Category D]

/-- A functor preserving binary products and coreflexive equalizers preserves equalizers. -/
theorem preservesEqualizers_of_coreflexive (F : C ⥤ D)
    [PreservesLimitsOfShape (Discrete WalkingPair) F] [PreservesCoreflexiveEq F] :
    PreservesLimitsOfShape WalkingParallelPair F where
  preservesLimit {K} := by
    suffices h : ∀ {X Y : C} (f g : X ⟶ Y), PreservesLimit (parallelPair f g) F from
      preservesLimit_of_iso_diagram F (diagramIsoParallelPair K).symm
    intro X Y f g
    let u : X ⟶ X ⨯ Y := prod.lift (𝟙 X) f
    let v : X ⟶ X ⨯ Y := prod.lift (𝟙 X) g
    have : IsCoreflexivePair u v :=
      IsCoreflexivePair.mk' prod.fst (by simp [u]) (by simp [v])
    have : PreservesLimit (parallelPair u v) F := PreservesCoreflexiveEq.preserves u v ‹_›
    have hP : IsLimit (BinaryFan.mk (F.map (prod.fst : X ⨯ Y ⟶ X))
        (F.map (prod.snd : X ⨯ Y ⟶ Y))) :=
      (isLimitMapConeBinaryFanEquiv F _ _) (isLimitOfPreserves F (prodIsProd X Y))
    have key : ∀ {T : C} (e : T ⟶ X), e ≫ f = e ≫ g ↔ e ≫ u = e ≫ v := by
      intro T e
      constructor
      · intro h; ext <;> simp [u, v, h]
      · intro h; simpa [u, v] using (h =≫ prod.snd)
    have keyF : ∀ {T : D} (e : T ⟶ F.obj X), e ≫ F.map f = e ≫ F.map g ↔
        e ≫ F.map u = e ≫ F.map v := by
      intro T e
      constructor
      · intro h
        refine BinaryFan.IsLimit.hom_ext hP ?_ ?_
        · simp only [BinaryFan.mk_fst, Category.assoc, ← F.map_comp, u, v, prod.lift_fst]
        · simp only [BinaryFan.mk_snd, Category.assoc, ← F.map_comp, u, v, prod.lift_snd, h]
      · intro h
        have := (h =≫ F.map (prod.snd : X ⨯ Y ⟶ Y))
        simpa only [Category.assoc, ← F.map_comp, u, v, prod.lift_snd] using this
    let e := equalizer.ι f g
    have hc := equalizerIsEqualizer f g
    -- `e` is also an equalizer of the coreflexive pair `u, v`
    have hc' : IsLimit (Fork.ofι e ((key e).1 (equalizer.condition f g))) :=
      Fork.IsLimit.mk _ (fun s => equalizer.lift s.ι ((key s.ι).2 s.condition))
        (fun s => equalizer.lift_ι (f := f) (g := g) _ _)
        (fun s m hm => equalizer.hom_ext (f := f) (g := g) (by rw [equalizer.lift_ι]; exact hm))
    have hFw : F.map e ≫ F.map u = F.map e ≫ F.map v := by
      rw [← F.map_comp, ← F.map_comp, (key e).1 (equalizer.condition f g)]
    have hF' : IsLimit (Fork.ofι (F.map e) hFw) :=
      (isLimitMapConeForkEquiv F _) (isLimitOfPreserves F hc')
    refine preservesLimit_of_preserves_limit_cone hc
      ((isLimitMapConeForkEquiv F (equalizer.condition f g)).symm ?_)
    refine Fork.IsLimit.mk _ (fun s => hF'.lift (Fork.ofι s.ι ((keyF s.ι).1 s.condition)))
      (fun s => hF'.fac _ .zero)
      (fun s m hm => Fork.IsLimit.hom_ext hF'
        ((show m ≫ F.map e = s.ι from hm).trans
          (hF'.fac (Fork.ofι s.ι ((keyF s.ι).1 s.condition)) .zero).symm))

end Gen

/-! ## The induced functor preserves finite products -/

attribute [local instance] ComonObj.instTensorUnit in
/-- `L` sends the trivial cocommutative comonoid `𝟙_ V` to a terminal object of `CommComon W`, since
its counit `L(𝟙) ≫ η` is invertible. -/
noncomputable def isTerminalMapCCTrivial :
    IsTerminal ((mapCC L).obj (CategoryTheory.CommComon.trivial V)) := by
  have hiso : IsIso (L.map (𝟙 (𝟙_ V)) ≫ η L) := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]; infer_instance
  haveI : IsIso ε[((mapCC L).obj (CategoryTheory.CommComon.trivial V)).X] := hiso
  exact isTerminalOfIsIsoCounit _

/-- `mapCC L` preserves terminal objects. -/
instance mapCC_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (CategoryTheory.CommComon V)) (mapCC L) :=
  preservesLimit_of_preserves_limit_cone CommComon.trivialIsTerminal
    ((isLimitMapConeEmptyConeEquiv _ _).symm (isTerminalMapCCTrivial L))

/-- The comparison `Δ ≫ (L p₁ ⊗ L p₂)` of `L` applied to the product `A ⊗ B` of cocommutative
comonoids (with its counit projections) is the oplax structure map `δ L A B`. -/
lemma mapCC_lift (A B : CategoryTheory.CommComon V) :
    Δ[((mapCC L).obj (CommComon.tensorObj A B)).X] ≫
        (((mapCC L).map (CommComon.binaryFan A B).fst).hom.hom ⊗ₘ
          ((mapCC L).map (CommComon.binaryFan A B).snd).hom.hom) = δ L A.X B.X := by
  change (L.map Δ[A.X ⊗ B.X] ≫ δ L _ _) ≫
      (L.map (CocommComon.fst A.X B.X) ⊗ₘ L.map (CocommComon.snd A.X B.X)) = _
  rw [Category.assoc, δ_natural, ← L.map_comp_assoc, CocommComon.lift_fst_snd,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- `mapCC L` preserves the binary product `A ⊗ B` of cocommutative comonoids, because the
comparison `δ L A B` is invertible (`mapCC_lift`). -/
instance mapCC_preservesPair (A B : CategoryTheory.CommComon V) :
    PreservesLimit (pair A B) (mapCC L) := by
  have hiso : IsIso (Δ[((mapCC L).obj (CommComon.tensorObj A B)).X] ≫
      (((mapCC L).map (CommComon.binaryFan A B).fst).hom.hom ⊗ₘ
        ((mapCC L).map (CommComon.binaryFan A B).snd).hom.hom)) := by
    rw [mapCC_lift]; exact (inferInstance : IsIso (δ L A.X B.X))
  exact preservesLimit_of_preserves_limit_cone (CommComon.binaryFanIsLimit A B)
    ((isLimitMapConeBinaryFanEquiv _ _ _).symm (isLimitOfIsIsoLift _ _ hiso))

/-- `mapCC L` preserves binary products. -/
instance mapCC_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (mapCC L) where
  preservesLimit {K} := preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

/-- `mapCC L` preserves finite products (binary products and the terminal object). -/
instance mapCC_preservesFiniteProducts : PreservesFiniteProducts (mapCC L) :=
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) (mapCC L) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-! ## Coreflexive equalizers, finite limits, reflexive coequalizers -/

section Pres

variable [HasCoreflexiveEqualizers V] [∀ Z : V, PreservesCoreflexiveEq (tensorLeft Z)]
  [∀ Z : V, PreservesCoreflexiveEq (tensorRight Z)]
  [HasCoreflexiveEqualizers W] [∀ Z : W, PreservesCoreflexiveEq (tensorLeft Z)]
  [∀ Z : W, PreservesCoreflexiveEq (tensorRight Z)]

/-- If `L` preserves coreflexive equalizers, so does `mapCC L`: the forgetful functors
`CommComon ⥤ V, W` preserve them (given the hypotheses on `⊗`) and reflect them. -/
theorem mapCC_preservesCoreflexiveEq [PreservesCoreflexiveEq L] :
    PreservesCoreflexiveEq (mapCC L) where
  preserves {X Y} u v h := by
    -- The forgetful functors create coreflexive equalizers and `L` preserves them, so
    -- `mapCC L ⋙ forget = forget ⋙ L` preserves the equalizer, and `forget` reflects it.
    have : PreservesCoreflexiveEq (CommComon.forgetV V) :=
      ComonCoreflexiveEq.preservesCoreflexiveEq_commComonForget V
    have : PreservesCoreflexiveEq (CommComon.forgetV W) :=
      ComonCoreflexiveEq.preservesCoreflexiveEq_commComonForget W
    have hu : IsCoreflexivePair ((CommComon.forgetV V).map u) ((CommComon.forgetV V).map v) :=
      isCoreflexivePair_map _ h
    have hΦ : IsCoreflexivePair ((mapCC L).map u) ((mapCC L).map v) := isCoreflexivePair_map _ h
    -- `forget ⋙ L` preserves the equalizer
    have : PreservesLimit (parallelPair u v) (CommComon.forgetV V) :=
      PreservesCoreflexiveEq.preserves u v h
    have : PreservesLimit (parallelPair ((parallelPair u v ⋙ CommComon.forgetV V).map
        WalkingParallelPairHom.left) ((parallelPair u v ⋙ CommComon.forgetV V).map
          WalkingParallelPairHom.right)) L := PreservesCoreflexiveEq.preserves _ _ hu
    have : PreservesLimit (parallelPair u v ⋙ CommComon.forgetV V) L :=
      preservesLimit_of_iso_diagram L (diagramIsoParallelPair _).symm
    have : PreservesLimit (parallelPair u v) (mapCC L ⋙ CommComon.forgetV W) := by
      rw [mapCC_forget]; infer_instance
    -- the image pair has an equalizer, which `forget` preserves and reflects
    have : HasLimit (parallelPair ((parallelPair u v ⋙ mapCC L).map
        WalkingParallelPairHom.left) ((parallelPair u v ⋙ mapCC L).map
          WalkingParallelPairHom.right)) := by
      have : IsCoreflexivePair ((parallelPair u v ⋙ mapCC L).map WalkingParallelPairHom.left)
          ((parallelPair u v ⋙ mapCC L).map WalkingParallelPairHom.right) := hΦ
      exact HasCoreflexiveEqualizers.has_eq _ _
    have : HasLimit (parallelPair u v ⋙ mapCC L) := hasLimit_of_iso (diagramIsoParallelPair _).symm
    have : PreservesLimit (parallelPair ((parallelPair u v ⋙ mapCC L).map
        WalkingParallelPairHom.left) ((parallelPair u v ⋙ mapCC L).map
          WalkingParallelPairHom.right)) (CommComon.forgetV W) :=
      PreservesCoreflexiveEq.preserves _ _ hΦ
    have : PreservesLimit (parallelPair u v ⋙ mapCC L) (CommComon.forgetV W) :=
      preservesLimit_of_iso_diagram _ (diagramIsoParallelPair _).symm
    have : ReflectsLimit (parallelPair u v ⋙ mapCC L) (CommComon.forgetV W) :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    exact preservesLimit_of_reflects_of_preserves (mapCC L) (CommComon.forgetV W)

/-- **The induced functor preserves finite limits.** -/
theorem mapCC_preservesFiniteLimits [PreservesCoreflexiveEq L] :
    PreservesFiniteLimits (mapCC L) := by
  have := Cor611.cocomm_hasFiniteLimits V
  have : HasEqualizers (CategoryTheory.CommComon V) := hasEqualizers_of_coreflexive
  have := mapCC_preservesCoreflexiveEq L
  have := preservesEqualizers_of_coreflexive (mapCC L)
  exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (mapCC L)

end Pres

/-- If `L` preserves reflexive coequalizers, so does `mapCC L`, since the forgetful functors
`CommComon ⥤ V, W` preserve and reflect them. -/
theorem mapCC_preservesReflexiveCoeq [HasReflexiveCoequalizers V] [HasReflexiveCoequalizers W]
    (hL : CategoryTheory.PreservesReflexiveCoeq L) : CategoryTheory.PreservesReflexiveCoeq
        (mapCC L) where
  preserves {X Y} u v h := by
    -- The forgetful functors create reflexive coequalizers and `L` preserves them, so
    -- `mapCC L ⋙ forget = forget ⋙ L` preserves the coequalizer, and `forget` reflects it.
    have := UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := W)
    have hfV := UlmerBialgebras.CommComon.forgetV_preservesReflexiveCoeq (V := V)
    have hfW := UlmerBialgebras.CommComon.forgetV_preservesReflexiveCoeq (V := W)
    have hu : IsReflexivePair ((CommComon.forgetV V).map u) ((CommComon.forgetV V).map v) := by
      obtain ⟨s, hs₁, hs₂⟩ := h.common_section
      exact IsReflexivePair.mk' ((CommComon.forgetV V).map s)
        (by rw [← Functor.map_comp, hs₁, CategoryTheory.Functor.map_id])
        (by rw [← Functor.map_comp, hs₂, CategoryTheory.Functor.map_id])
    have hΦ : IsReflexivePair ((mapCC L).map u) ((mapCC L).map v) := by
      obtain ⟨s, hs₁, hs₂⟩ := h.common_section
      exact IsReflexivePair.mk' ((mapCC L).map s)
        (by rw [← Functor.map_comp, hs₁, CategoryTheory.Functor.map_id])
        (by rw [← Functor.map_comp, hs₂, CategoryTheory.Functor.map_id])
    -- `forget ⋙ L` preserves the coequalizer
    have : PreservesColimit (parallelPair u v) (CommComon.forgetV V) := hfV.preserves u v h
    have : PreservesColimit (parallelPair ((parallelPair u v ⋙ CommComon.forgetV V).map
        WalkingParallelPairHom.left) ((parallelPair u v ⋙ CommComon.forgetV V).map
          WalkingParallelPairHom.right)) L := hL.preserves _ _ hu
    have : PreservesColimit (parallelPair u v ⋙ CommComon.forgetV V) L :=
      preservesColimit_of_iso_diagram L (diagramIsoParallelPair _).symm
    have : PreservesColimit (parallelPair u v) (mapCC L ⋙ CommComon.forgetV W) := by
      rw [mapCC_forget]; infer_instance
    -- the image pair has a coequalizer, which `forget` preserves and reflects
    have : HasColimit (parallelPair ((parallelPair u v ⋙ mapCC L).map
        WalkingParallelPairHom.left) ((parallelPair u v ⋙ mapCC L).map
          WalkingParallelPairHom.right)) := by
      have : IsReflexivePair ((parallelPair u v ⋙ mapCC L).map WalkingParallelPairHom.left)
          ((parallelPair u v ⋙ mapCC L).map WalkingParallelPairHom.right) := hΦ
      infer_instance
    have : HasColimit (parallelPair u v ⋙ mapCC L) :=
      hasColimit_of_iso (diagramIsoParallelPair _)
    have : PreservesColimit (parallelPair ((parallelPair u v ⋙ mapCC L).map
        WalkingParallelPairHom.left) ((parallelPair u v ⋙ mapCC L).map
          WalkingParallelPairHom.right)) (CommComon.forgetV W) := hfW.preserves _ _ hΦ
    have : PreservesColimit (parallelPair u v ⋙ mapCC L) (CommComon.forgetV W) :=
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair _).symm
    have : ReflectsColimit (parallelPair u v ⋙ mapCC L) (CommComon.forgetV W) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    exact preservesColimit_of_reflects_of_preserves (mapCC L) (CommComon.forgetV W)

/-! ## Descent for cocommutative Hopf monoids -/

section Main

/-- The standing hypothesis transported to `Comon^coc`: finite limits, reflexive coequalizers,
and the product preserving the latter in each variable. -/
theorem cocomm_standing (X : Type u) [Category.{v} X] [MonoidalCategory X] [SymmetricCategory X]
    [HasReflexiveCoequalizers X] [∀ Z : X, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    (A : CategoryTheory.CommComon X) :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft A) ∧
      CategoryTheory.PreservesReflexiveCoeq (tensorRight A) := by
  have := UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := X)
  have := Cor611.cocomm_productRight_preservesWalkingReflexivePair X A
  refine ⟨Cor611.cocomm_product_preservesReflexiveCoeq X A, ⟨fun _ _ u v h => ?_⟩⟩
  have := h
  exact preservesColimit_parallelPair_of_reflexive _ u v

/-- **Exactness of cocommutative Hopf monoids descends along a jointly conservative family of
braided strong monoidal functors preserving reflexive coequalizers and coreflexive
equalizers.** The bases need only reflexive coequalizers and coreflexive equalizers preserved
by the tensor product in each variable. -/
theorem isBarrExact_cocommHopf (V : Type u) [Category.{v} V] [MonoidalCategory V]
    [SymmetricCategory V] [HasCoreflexiveEqualizers V] [HasReflexiveCoequalizers V]
    [∀ Z : V, PreservesCoreflexiveEq (tensorLeft Z)]
    [∀ Z : V, PreservesCoreflexiveEq (tensorRight Z)]
    [∀ Z : V, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    {I : Type*} (W : I → Type u') [∀ i, Category.{v'} (W i)] [∀ i, MonoidalCategory (W i)]
    [∀ i, SymmetricCategory (W i)] [∀ i, HasCoreflexiveEqualizers (W i)]
    [∀ i, HasReflexiveCoequalizers (W i)]
    [∀ i (Z : W i), PreservesCoreflexiveEq (tensorLeft Z)]
    [∀ i (Z : W i), PreservesCoreflexiveEq (tensorRight Z)]
    [∀ i (Z : W i), CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    (L : ∀ i, V ⥤ W i) [∀ i, (L i).Braided] [∀ i, PreservesCoreflexiveEq (L i)]
    (hL : ∀ i,
        CategoryTheory.PreservesReflexiveCoeq (L i)) (hcons : CategoryTheory.JointlyConservative L)
    [∀ i, CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (W i)))] :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon V)) := by
  have := Cor611.cocomm_hasFiniteLimits V
  have := UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := V)
  have := fun i => Cor611.cocomm_hasFiniteLimits (W i)
  have := fun i => UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := W i)
  have := fun A => (cocomm_standing V A).1
  have := fun A => (cocomm_standing V A).2
  have := fun i (A : CategoryTheory.CommComon (W i)) => (cocomm_standing (W i) A).1
  have := fun i (A : CategoryTheory.CommComon (W i)) => (cocomm_standing (W i) A).2
  have := fun i => mapCC_preservesFiniteLimits (L i)
  refine GrpDescent.isBarrExact_grp (D := fun i => CategoryTheory.CommComon (W i))
    (fun i => mapCC (L i)) (fun i => mapCC_preservesReflexiveCoeq (L i) (hL i)) ?_
  refine ⟨?_⟩
  intro X Y f hf
  have : IsIso ((CommComon.forgetV V).map f) := by
    refine hcons.isIso_of_forall _ (fun i => ?_)
    have := hf i
    exact (inferInstance : IsIso ((CommComon.forgetV (W i)).map ((mapCC (L i)).map f)))
  exact isIso_of_reflects_iso f (CommComon.forgetV V)

end Main

end UlmerBialgebras.Paper.ComonDescent
