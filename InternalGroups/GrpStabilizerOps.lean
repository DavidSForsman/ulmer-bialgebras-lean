module

public import InternalGroups.GrpStabilizerCoset
public import InternalGroups.GrpObjSubgroupCorrespondenceExact
public import Foundations.CategoryTheory.Monoidal.ModObjPullbacks
public import InternalGroups.GrpStabilizerTwisted

/-!
# Stabilizers by their generalized elements

A monomorphism `m : X ⟶ G` of `Grp C` is a stabilizer (`InternalGroups.GrpIsStabilizer`) as soon
as the generalized elements of `G` that factor through `m` are exactly those killed by a module
map `q : G ⟶ V` (`InternalGroups.KillsOf`). This characterization is what the constructions on
stabilizers (intersections, preimages, the graph of a homomorphism) rest on.

## Main results

* `InternalGroups.grpIsStabilizer_of_factors_iff_killsOf`;
* `InternalGroups.restrictUnder`, `InternalGroups.killsOf_restrictUnder`: a module map restricted
  along a homomorphism `φ` kills `g` iff the original one kills `g ≫ φ` (preimages of
  stabilizers);
* `InternalGroups.pairUnder`, `InternalGroups.killsOf_pairUnder`: the pairing of two module maps
  kills `g` iff both do (intersections of stabilizers);
* `InternalGroups.GrpIsStabilizer.exists_factors_iff_killsOf`: conversely, a stabilizer factors
  exactly the generalized elements killed by its module map;
* `InternalGroups.grpIsStabilizer_comp_section`: for a product `P` of `Y` and `Z` in `Grp C` and
  the section `γ : Z ⟶ P` with components `g` and `𝟙` (the graph of `g`), `s ≫ γ` is a
  stabilizer of `P` for every stabilizer `s` of `Z`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj
open scoped MonObj
open CartesianMonoidalCategory

attribute [local instance] CategoryTheory.ModObj.regular

namespace InternalGroups

open AugMon

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## Restriction along a homomorphism -/

/-- **The restriction of a module map along a homomorphism** `φ : H ⟶ G`: the `H`-module map
`H ⟶ φ^* V`, `h ↦ q (φ h)`. -/
noncomputable def restrictUnder {H G : Grp C} (φ : H ⟶ G)
    (q : Under (selfMod (grpToAugMon.obj G).X)) : Under (selfMod (grpToAugMon.obj H).X) :=
  haveI : IsMonHom φ.hom.hom := φ.hom.isMonHom_hom
  Under.mk (selfModComap φ.hom.hom ≫ (CategoryTheory.Mod.comap φ.hom.hom).map q.hom)

/-- The underlying morphism of the restricted module map is `φ ≫ q`. -/
lemma restrictUnder_hom_hom {H G : Grp C} (φ : H ⟶ G)
    (q : Under (selfMod (grpToAugMon.obj G).X)) :
    (restrictUnder φ q).hom.hom = φ.hom.hom ≫ q.hom.hom := rfl

/-- **The restricted module map kills `g` iff the original one kills `g ≫ φ`.** -/
lemma killsOf_restrictUnder {H G : Grp C} (φ : H ⟶ G)
    (q : Under (selfMod (grpToAugMon.obj G).X)) {T : C} (g : T ⟶ H.X) :
    KillsOf (G := H.X) (V := (restrictUnder φ q).right.X) (restrictUnder φ q).hom.hom g ↔
      KillsOf (G := G.X) (V := q.right.X) q.hom.hom (g ≫ φ.hom.hom) := by
  have : IsMonHom φ.hom.hom := φ.hom.isMonHom_hom
  have h1 : (η[H.X] : 𝟙_ C ⟶ H.X) ≫ φ.hom.hom = η[G.X] := IsMonHom.one_hom φ.hom.hom
  change (g ≫ φ.hom.hom ≫ q.hom.hom : T ⟶ q.right.X) =
      toUnit T ≫ (η[H.X] ≫ φ.hom.hom ≫ q.hom.hom : 𝟙_ C ⟶ q.right.X) ↔
    (g ≫ φ.hom.hom) ≫ q.hom.hom = toUnit T ≫ (η[G.X] ≫ q.hom.hom : 𝟙_ C ⟶ q.right.X)
  rw [reassoc_of% h1, Category.assoc]

/-! ## The twisted module map -/

/-- **The twisted module map** of two homomorphisms `f g : H ⟶ K`: the orbit map `h ↦ f h · (g h)⁻¹`
of the identity for the twisted action of `H` on `K`. It kills exactly the generalized elements on
which `f` and `g` agree (`killsOf_twistedUnder`). -/
noncomputable def twistedUnder {H K : C} [GrpObj H] [GrpObj K] (f g : H ⟶ K) [IsMonHom f]
    [IsMonHom g] : Under (selfMod H) :=
  letI := twistedModObj f g
  Under.mk (CategoryTheory.Mod.Hom.mk' (M := selfMod H) (N := ⟨K⟩) (twistedOrbit f g)
    (isModHom_twistedOrbit f g).smul_hom)

/-- **The twisted module map kills `x` iff `x ≫ f = x ≫ g`.** -/
lemma killsOf_twistedUnder {H K : C} [GrpObj H] [GrpObj K] (f g : H ⟶ K) [IsMonHom f]
    [IsMonHom g] {T : C} (x : T ⟶ H) :
    KillsOf (G := H) (V := (twistedUnder f g).right.X) (twistedUnder f g).hom.hom x ↔
      x ≫ f = x ≫ g := by
  change KillsOf (G := H) (V := K) (twistedOrbit f g) x ↔ _
  rw [KillsOf, twistedOrbit_basePoint]
  exact twistedOrbit_eq_one_iff f g x

variable [HasPullbacks C]

/-- **A monomorphism of `Grp C` is a stabilizer** if the generalized elements of its codomain that
factor through it are exactly those killed by a module map. -/
theorem grpIsStabilizer_of_factors_iff_killsOf {G X : Grp C} (m : X ⟶ G) [Mono m.hom.hom]
    (q : Under (selfMod (grpToAugMon.obj G).X))
    (h : ∀ {T : C} (g : T ⟶ G.X),
      (∃ k : T ⟶ X.X, k ≫ m.hom.hom = g) ↔ KillsOf (G := G.X) (V := q.right.X) q.hom.hom g) :
    GrpIsStabilizer m := by
  let s := InternalGroups.stabOf (G := G.X) (V := q.right.X) q.hom.hom
  let := s.grpObj
  have := s.isMonHom_i
  obtain ⟨a₀, ha₀⟩ := (killsOf_iff_factors (G := G.X) (V := q.right.X) q.hom.hom m.hom.hom).1
    ((h m.hom.hom).1 ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨b₀, hb₀⟩ := (h (stabSubIncl (G := G.X) (V := q.right.X) q.hom.hom)).2
    (killsOf_stabSubIncl (G := G.X) (V := q.right.X) q.hom.hom)
  let a : X.X ⟶ s.N := a₀
  let b : s.N ⟶ X.X := b₀
  have ha : a ≫ s.i = m.hom.hom := ha₀
  have hb : b ≫ m.hom.hom = s.i := hb₀
  have hab : a ≫ b = 𝟙 _ := (cancel_mono m.hom.hom).1 (by
    rw [Category.assoc, hb, ha, Category.id_comp])
  have hba : b ≫ a = 𝟙 _ := (cancel_mono s.i).1 (by
    rw [Category.assoc, ha, hb, Category.id_comp])
  have haMon : IsMonHom a := by
    have : IsMonHom (a ≫ s.i) := by rw [ha]; infer_instance
    exact Internal.isMonHom_of_comp_mono a s.i
  have hbMon : IsMonHom b := by
    have : IsMonHom (b ≫ m.hom.hom) := by rw [hb]; exact s.isMonHom_i
    exact Internal.isMonHom_of_comp_mono b m.hom.hom
  let e : X ≅ s.toGrp :=
    { hom := Grp.homMk' (A := X) (B := s.toGrp) { hom := a, isMonHom_hom := haMon }
      inv := Grp.homMk' (A := s.toGrp) (B := X) { hom := b, isMonHom_hom := hbMon }
      hom_inv_id := by ext; exact hab
      inv_hom_id := by ext; exact hba }
  exact ⟨q, e, by ext; exact ha⟩

/-! ## Pairing two module maps -/

section Pair

variable {A : C} [MonObj A]

/-- The **trivial module** on the unit object: every element acts as the identity. -/
@[instance_reducible]
noncomputable def trivialModObj : ModObj A (𝟙_ C) where
  smul := toUnit _
  one_smul := toUnit_unique _ _
  mul_smul := toUnit_unique _ _

/-- The trivial module on the unit object, as an object of `Mod C A`. -/
noncomputable def trivialMod : CategoryTheory.Mod C A :=
  letI := trivialModObj (C := C) (A := A)
  ⟨𝟙_ C⟩

/-- The morphism of modules from any module to the trivial module. -/
noncomputable def toTrivialMod (M : CategoryTheory.Mod C A) : M ⟶ trivialMod (C := C) (A := A) :=
  letI := trivialModObj (C := C) (A := A)
  CategoryTheory.Mod.Hom.mk'' (toUnit M.X) (toUnit_unique _ _)

/-- **The pairing of two module maps** `q₁ : A ⟶ V₁` and `q₂ : A ⟶ V₂`, into the product
`V₁ × V₂` with the diagonal action (the pullback of modules over the trivial module). -/
noncomputable def pairUnder (q₁ q₂ : Under (selfMod A)) : Under (selfMod A) :=
  Under.mk ((Mod_.pullbackConeIsLimit (toTrivialMod q₁.right) (toTrivialMod q₂.right)).lift
    (PullbackCone.mk q₁.hom q₂.hom (by ext; exact toUnit_unique _ _)))

/-- The underlying morphism of the pairing, followed by the first projection, is `q₁`. -/
lemma pairUnder_hom_fst (q₁ q₂ : Under (selfMod A)) :
    (pairUnder q₁ q₂).hom.hom ≫ (pullback.fst (toTrivialMod q₁.right).hom
      (toTrivialMod q₂.right).hom : (pairUnder q₁ q₂).right.X ⟶ q₁.right.X) = q₁.hom.hom :=
  congr(($(PullbackCone.IsLimit.lift_fst
    (Mod_.pullbackConeIsLimit (toTrivialMod q₁.right) (toTrivialMod q₂.right)) _ _ _)).hom)

/-- The underlying morphism of the pairing, followed by the second projection, is `q₂`. -/
lemma pairUnder_hom_snd (q₁ q₂ : Under (selfMod A)) :
    (pairUnder q₁ q₂).hom.hom ≫ (pullback.snd (toTrivialMod q₁.right).hom
      (toTrivialMod q₂.right).hom : (pairUnder q₁ q₂).right.X ⟶ q₂.right.X) = q₂.hom.hom :=
  congr(($(PullbackCone.IsLimit.lift_snd
    (Mod_.pullbackConeIsLimit (toTrivialMod q₁.right) (toTrivialMod q₂.right)) _ _ _)).hom)

end Pair

/-- **The pairing of two module maps kills `g` iff both do.** -/
lemma killsOf_pairUnder {G : C} [GrpObj G] (q₁ q₂ : Under (selfMod G)) {T : C} (g : T ⟶ G) :
    KillsOf (G := G) (V := (pairUnder q₁ q₂).right.X) (pairUnder q₁ q₂).hom.hom g ↔
      KillsOf (G := G) (V := q₁.right.X) q₁.hom.hom g ∧
        KillsOf (G := G) (V := q₂.right.X) q₂.hom.hom g := by
  have h₁ := pairUnder_hom_fst q₁ q₂
  have h₂ := pairUnder_hom_snd q₁ q₂
  set L := (pairUnder q₁ q₂).hom.hom
  set p₁ : (pairUnder q₁ q₂).right.X ⟶ q₁.right.X :=
    pullback.fst (toTrivialMod q₁.right).hom (toTrivialMod q₂.right).hom
  set p₂ : (pairUnder q₁ q₂).right.X ⟶ q₂.right.X :=
    pullback.snd (toTrivialMod q₁.right).hom (toTrivialMod q₂.right).hom
  rw [KillsOf, KillsOf, KillsOf, stabBasePoint, stabBasePoint, stabBasePoint]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Category.assoc, h₁] using h =≫ p₁
    · simpa only [Category.assoc, h₂] using h =≫ p₂
  · rintro ⟨ha, hb⟩
    apply pullback.hom_ext
    · change (g ≫ L) ≫ p₁ = (toUnit T ≫ η[G] ≫ L) ≫ p₁
      simpa only [Category.assoc, h₁] using ha
    · change (g ≫ L) ≫ p₂ = (toUnit T ≫ η[G] ≫ L) ≫ p₂
      simpa only [Category.assoc, h₂] using hb

/-! ## Stabilizers factor exactly what their module map kills -/

/-- **A stabilizer factors exactly the generalized elements killed by its module map.** -/
theorem GrpIsStabilizer.exists_factors_iff_killsOf {G X : Grp C} {m : X ⟶ G}
    (hm : GrpIsStabilizer m) :
    ∃ q : Under (selfMod (grpToAugMon.obj G).X), ∀ {T : C} (g : T ⟶ G.X),
      (∃ k : T ⟶ X.X, k ≫ m.hom.hom = g) ↔ KillsOf (G := G.X) (V := q.right.X) q.hom.hom g := by
  obtain ⟨q, e, he⟩ := hm
  refine ⟨q, fun {T} g => ?_⟩
  let i : stabSubObj (G := G.X) (V := q.right.X) q.hom.hom ⟶ G.X :=
    stabSubIncl (G := G.X) (V := q.right.X) q.hom.hom
  let E : X.X ⟶ stabSubObj (G := G.X) (V := q.right.X) q.hom.hom := e.hom.hom.hom
  let F : stabSubObj (G := G.X) (V := q.right.X) q.hom.hom ⟶ X.X := e.inv.hom.hom
  have he' : E ≫ i = m.hom.hom := congr(($he).hom.hom)
  have hFE : F ≫ E = 𝟙 _ := congr(($e.inv_hom_id).hom.hom)
  rw [killsOf_iff_factors]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k ≫ E, by rw [Category.assoc, he']⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h ≫ F, ?_⟩
    rw [← he', Category.assoc, ← Category.assoc F, hFE, Category.id_comp]

/-! ## Stabilizers along the graph of a homomorphism -/

/-- The underlying morphism of a stabilizer is a monomorphism. -/
theorem GrpIsStabilizer.mono_hom {G X : Grp C} {m : X ⟶ G} (hm : GrpIsStabilizer m) :
    Mono m.hom.hom := by
  obtain ⟨q', e, he⟩ := hm
  let i : stabSubObj (G := G.X) (V := q'.right.X) q'.hom.hom ⟶ G.X :=
    stabSubIncl (G := G.X) (V := q'.right.X) q'.hom.hom
  let E : X.X ⟶ stabSubObj (G := G.X) (V := q'.right.X) q'.hom.hom := e.hom.hom.hom
  have he' : E ≫ i = m.hom.hom := congr(($he).hom.hom)
  have : IsIso E :=
    ⟨e.inv.hom.hom, congr(($e.hom_inv_id).hom.hom),
      congr(($e.inv_hom_id).hom.hom)⟩
  have : Mono i := by unfold i stabSubIncl; infer_instance
  rw [← he']
  infer_instance

/-- **A stabilizer of `Z` along the graph of `g : Z ⟶ Y` is a stabilizer of the product.** Let
`(π₁, π₂)` be a product of `Y` and `Z` in `Grp C` and `σ : Z ⟶ P` the section with `σ ≫ π₁ = g`
and `σ ≫ π₂ = 𝟙`. If `s : M ⟶ Z` is a stabilizer, so is `s ≫ σ`: it is the stabilizer of the
pairing of the module map of `s` restricted along `π₂` with the twisted module map of `π₁` and
`π₂ ≫ g`. -/
theorem grpIsStabilizer_comp_section {Y Z P M : Grp C} {π₁ : P ⟶ Y} {π₂ : P ⟶ Z}
    (hP : IsLimit (BinaryFan.mk π₁ π₂)) {g : Z ⟶ Y} {σ : Z ⟶ P} (hσ₁ : σ ≫ π₁ = g)
    (hσ₂ : σ ≫ π₂ = 𝟙 Z) {s : M ⟶ Z} (hs : GrpIsStabilizer s) : GrpIsStabilizer (s ≫ σ) := by
  obtain ⟨q, hq⟩ := hs.exists_factors_iff_killsOf
  have hσ₁' : σ.hom.hom ≫ π₁.hom.hom = g.hom.hom := congr(($hσ₁).hom.hom)
  have hσ₂' : σ.hom.hom ≫ π₂.hom.hom = 𝟙 _ := congr(($hσ₂).hom.hom)
  -- the projections are jointly monic in `C`
  have hPC := isLimitOfPreserves (Grp.forget C) hP
  have hjoint : ∀ {T : C} (a b : T ⟶ P.X), a ≫ π₁.hom.hom = b ≫ π₁.hom.hom →
      a ≫ π₂.hom.hom = b ≫ π₂.hom.hom → a = b := by
    intro T a b h₁ h₂
    refine hPC.hom_ext ?_
    rintro ⟨⟨⟩⟩
    · exact h₁
    · exact h₂
  have : Mono s.hom.hom := hs.mono_hom
  have : Mono (s ≫ σ).hom.hom := by
    have : Mono σ.hom.hom := ⟨fun a b h => by
      simpa [hσ₂'] using h =≫ π₂.hom.hom⟩
    rw [Grp.comp_hom_hom]; infer_instance
  have : IsMonHom π₁.hom.hom := π₁.hom.isMonHom_hom
  have : IsMonHom (π₂.hom.hom ≫ g.hom.hom) := by
    have := π₂.hom.isMonHom_hom; have := g.hom.isMonHom_hom; infer_instance
  refine grpIsStabilizer_of_factors_iff_killsOf (s ≫ σ)
    (pairUnder (restrictUnder π₂ q) (twistedUnder π₁.hom.hom (π₂.hom.hom ≫ g.hom.hom)))
    (fun {T} k => ?_)
  rw [killsOf_pairUnder, killsOf_restrictUnder, killsOf_twistedUnder, ← hq]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨⟨t, ?_⟩, ?_⟩
    · simp only [Grp.comp_hom_hom, Category.assoc, hσ₂', Category.comp_id]
    · simp only [Grp.comp_hom_hom, Category.assoc, hσ₁', reassoc_of% hσ₂']
  · rintro ⟨⟨t, ht⟩, hk⟩
    refine ⟨t, hjoint _ _ ?_ ?_⟩
    · rw [Grp.comp_hom_hom, hk, ← Category.assoc k, ← ht]
      simp only [Category.assoc, hσ₁']
    · rw [Grp.comp_hom_hom, ← ht]
      simp only [Category.assoc, hσ₂', Category.comp_id]

/-! ## Regular monomorphisms are stabilizers -/

/-- A regular monomorphism of group objects is a stabilizer of an equivariant module map. -/
theorem grpIsStabilizer_of_regularMono {I H : Grp C} (m : I ⟶ H) (hm : RegularMono m) :
    GrpIsStabilizer m := by
  -- `m` equalizes `f` and `g`; the twisted orbit map of `f` and `g` kills exactly what they
  -- agree on, so its stabilizer `s` contains `m` (`a`), and `s` factors through `m` (`b`)
  let f := hm.left.hom.hom
  let g := hm.right.hom.hom
  let := InternalGroups.twistedModObj f g
  let := InternalGroups.isModHom_twistedOrbit f g
  let q : Under (selfMod H.X) :=
    Under.mk (CategoryTheory.Mod.Hom.mk' (M := selfMod H.X) (N := ⟨hm.Z.X⟩)
      (InternalGroups.twistedOrbit f g) (InternalGroups.isModHom_twistedOrbit f g).smul_hom)
  let s := InternalGroups.stabOf (G := H.X) (V := hm.Z.X) (InternalGroups.twistedOrbit f g)
  have hk : ∀ {T : C} (x : T ⟶ H.X),
      InternalGroups.KillsOf (InternalGroups.twistedOrbit f g) x ↔ x ≫ f = x ≫ g := by
    intro T x
    rw [InternalGroups.KillsOf, InternalGroups.twistedOrbit_basePoint]
    exact InternalGroups.twistedOrbit_eq_one_iff f g x
  have hmkill : InternalGroups.KillsOf (InternalGroups.twistedOrbit f g) m.hom.hom :=
    (hk _).2 congr(($(hm.w)).hom.hom)
  -- `m` factors through the stabilizer
  let u : I.X ⟶ s.N := pullback.lift m.hom.hom (toUnit _) hmkill
  have hu : u ≫ s.i = m.hom.hom := pullback.lift_fst _ _ _
  let _ : GrpObj s.N := s.grpObj
  have hi : IsMonHom u := InternalGroups.isMonHom_of_comp_mono u s.i s.mono_i s.isMonHom_i
    (hu.symm ▸ inferInstance)
  let a : I ⟶ s.toGrp := Grp.homMk' { hom := u, isMonHom_hom := hi }
  have ha : a ≫ s.inclGrp = m := Grp.hom_ext _ _ hu
  -- the stabilizer equalizes `f` and `g`, so it factors through `m`
  have hw : s.inclGrp ≫ hm.left = s.inclGrp ≫ hm.right := by
    apply Grp.hom_ext
    exact (hk s.i).1
      (InternalGroups.killsOf_stabSubIncl (G := H.X) (InternalGroups.twistedOrbit f g))
  let b : s.toGrp ⟶ I := Fork.IsLimit.lift hm.isLimit s.inclGrp hw
  have hb : b ≫ m = s.inclGrp := Fork.IsLimit.lift_ι' hm.isLimit _ _
  have : Mono m := hm.mono
  have : Mono s.inclGrp := (Grp.forget C).mono_of_mono_map s.mono_i
  let e : I ≅ s.toGrp :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply (cancel_mono m).1
        rw [Category.assoc, hb, ha, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono s.inclGrp).1
        rw [Category.assoc, ha, hb, Category.id_comp] }
  exact ⟨q, e, ha⟩

end InternalGroups
