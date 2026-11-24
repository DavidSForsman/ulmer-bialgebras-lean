module

public import InternalGroups.AugMonBasic
public import InternalGroups.GrpObjSubgroupCorrespondence

/-!
# Stabilizers in the category of group objects

The author's definition, in the group setting: a morphism `m : X ⟶ G` of group objects is a
**stabilizer** if, up to an isomorphism in `Grp(C)/G`, it is the inclusion of the stabilizer
`stab f : SubGrp G` of some morphism of modules `f : G ⟶ V` in `C^G`.  The module map `f` is
*not* required to be an epimorphism: a stabilizer is the fibre of the base point of an arbitrary
equivariant map out of `G`, and the stabilizer subgroup is the stabilizer of that map.  (The
quotient-module case `QuotMod` is the special case in which `f` is an epimorphism; every
`QuotMod` gives such a stabilizer, `InternalGroups.stab_of_quot`.)

The construction of `InternalGroups.stab f` follows the one in
`InternalGroups/SubMonQuotGalois.lean` and `InternalGroups/GrpObjSubgroupCorrespondence.lean`, with
the quotient map replaced by an arbitrary module map `f`: the underlying object is the fibre
`pullback f (η ≫ f)` of the base point, the inclusion is the first projection, and the monoid
structure is induced from that of `G`. Since the fibre of the base point of a module map is closed
under inversion (it is the stabilizer of the base point for the action of `G`), it is a subgroup
object.

## Main definitions

* `InternalGroups.stabBasePoint`, `InternalGroups.stabSubObj`, `InternalGroups.stabSubIncl`: the
  fibre of the base point of an arbitrary module map;
* `InternalGroups.stabOf`: the stabilizer of a module map, as a subgroup object;
* `InternalGroups.SubGrp.toGrp`, `InternalGroups.SubGrp.inclGrp`: a subgroup object as an object of
  `Grp C` together with its inclusion;
* `InternalGroups.GrpIsStabilizer`: stabilizers of morphisms of `Grp C`.

## Main results

* `InternalGroups.stabOf`: the stabilizer of any module map is a subgroup object;
* `InternalGroups.GrpIsStabilizer.of_iso`: stabilizers are closed under isomorphisms in `Grp(C)/G`;
* `InternalGroups.isGrpStabilizer_stabOf`: the inclusion of the stabilizer of a module map is a
  stabilizer.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
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

/-- The object of `Grp C` underlying a subgroup object. -/
def SubGrp.toGrp {G : C} [GrpObj G] (s : InternalGroups.SubGrp G) : Grp C :=
  Grp.mk s.N

/-- The inclusion of a subgroup object, as a morphism of `Grp C`. -/
noncomputable def SubGrp.inclGrp {G : C} [GrpObj G] (s : InternalGroups.SubGrp G) :
    s.toGrp ⟶ Grp.mk G :=
  Grp.homMk' (A := s.toGrp) (B := Grp.mk G)
    { hom := s.i, isMonHom_hom := s.isMonHom_i }


/-! ## The stabilizer subgroup of an arbitrary module map -/

section Stabiliser

variable {G : C} [GrpObj G] {V : C}

/-- The base point of a module map: the image of the unit of `G`. -/
noncomputable def stabBasePoint (f : G ⟶ V) : 𝟙_ C ⟶ V :=
  η[G] ≫ f

/-- The base point of a module map is a monomorphism. -/
lemma mono_stabBasePoint (f : G ⟶ V) : Mono (stabBasePoint f) :=
  ⟨fun _ _ _ => isTerminalTensorUnit.hom_ext _ _⟩

/-- A generalized element `g : T ⟶ G` **kills** the module map `f` if the module map sends it to
the base point.  In `Set`: `g` lies in the stabilizer of the base point. -/
def KillsOf (f : G ⟶ V) {T : C} (g : T ⟶ G) : Prop :=
  g ≫ f = toUnit T ≫ stabBasePoint f

section Equivariant

variable [ModObj G V]

/-- Equivariance of the module map, in the form used below. -/
lemma mul_comp_stabBasePoint (f : G ⟶ V) [IsModHom G f] :
    μ[G] ≫ f = G ◁ f ≫ γ[G, V] := by
  have := IsModHom.smul_hom (A := G) (f := f)
  simpa using this

/-- `G ◁ stabBasePoint f ≫ γ[G, V] = (ρ_ G).hom ≫ f`. -/
lemma unit_whisker_comp_stabBasePoint (f : G ⟶ V) [IsModHom G f] :
    G ◁ stabBasePoint f ≫ γ[G, V] = (ρ_ G).hom ≫ f := by
  rw [stabBasePoint, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ← mul_comp_stabBasePoint f, ← Category.assoc, MonObj.mul_one]

/-- The module map is the orbit map of the base point: `f (g) = g · f (1)`. -/
lemma comp_eq_act (f : G ⟶ V) [IsModHom G f] {T : C} (g : T ⟶ G) :
    g ≫ f = act g (toUnit T ≫ stabBasePoint f) := by
  have h := mul_comp_stabBasePoint f
  calc g ≫ f = (g * 1) ≫ f := by rw [_root_.mul_one]
    _ = lift g (1 : T ⟶ G) ≫ μ[G] ≫ f := by rw [← Category.assoc]; rfl
    _ = lift g ((1 : T ⟶ G) ≫ f) ≫ γ[G, V] := by
        rw [h, ← Category.assoc]
        simp only [lift_whiskerLeft]
    _ = act g (toUnit T ≫ stabBasePoint f) := by
        rw [act, stabBasePoint, Hom.one_def, Category.assoc]

/-- `g` kills `f` iff `g` fixes the base point: `g · pt = pt`. -/
lemma killsOf_iff_act (f : G ⟶ V) [IsModHom G f] {T : C} (g : T ⟶ G) :
    KillsOf f g ↔ act g (toUnit T ≫ stabBasePoint f) = toUnit T ≫ stabBasePoint f := by
  rw [KillsOf, comp_eq_act f g]

/-- If `g` kills `f`, so does `g⁻¹`. -/
lemma KillsOf.inv (f : G ⟶ V) [IsModHom G f] {T : C} {g : T ⟶ G} (hg : KillsOf f g) :
    KillsOf f g⁻¹ := by
  rw [killsOf_iff_act] at *
  conv_lhs => rw [← hg]
  rw [← act_mul, inv_mul_cancel, act_one]

end Equivariant

variable [HasPullbacks C]

/-- The underlying object of the stabilizer of a module map: the fibre of the base point. -/
noncomputable abbrev stabSubObj (f : G ⟶ V) : C :=
  pullback f (stabBasePoint f)

/-- The inclusion of the stabilizer of a module map. -/
noncomputable abbrev stabSubIncl (f : G ⟶ V) : stabSubObj f ⟶ G :=
  pullback.fst _ _

/-- The inclusion followed by the module map is constant at the base point. -/
lemma stabSubIncl_comp (f : G ⟶ V) :
    stabSubIncl f ≫ f = toUnit (stabSubObj f) ≫ stabBasePoint f := by
  rw [pullback.condition]
  congr 1
  exact isTerminalTensorUnit.hom_ext _ _

/-- The inclusion of the stabilizer of a module map is a monomorphism. -/
instance mono_stabSubIncl (f : G ⟶ V) : Mono (stabSubIncl f) := by
  have := mono_stabBasePoint f
  infer_instance

/-- The unit of the stabilizer of a module map. -/
noncomputable def stabSubOne (f : G ⟶ V) : 𝟙_ C ⟶ stabSubObj f :=
  pullback.lift η[G] (𝟙 _) (by simp [stabBasePoint])

/-- The unit of the stabilizer, followed by the inclusion, is the unit of `G`. -/
@[reassoc (attr := simp)]
lemma stabSubOne_comp (f : G ⟶ V) : stabSubOne f ≫ stabSubIncl f = η[G] := by
  simp [stabSubOne]

/-- The stabilizer of a module map is exactly the collection of generalized elements which factor
through `stabSubIncl f`. -/
lemma killsOf_iff_factors (f : G ⟶ V) {T : C} (g : T ⟶ G) :
    KillsOf f g ↔ ∃ h : T ⟶ stabSubObj f, h ≫ stabSubIncl f = g := by
  constructor
  · rintro hg
    exact ⟨pullback.lift g (toUnit T) hg, pullback.lift_fst _ _ _⟩
  · rintro ⟨h, rfl⟩
    rw [KillsOf, Category.assoc, stabSubIncl_comp f, ← Category.assoc,
      toUnit_unique (h ≫ toUnit _) (toUnit T)]

/-- The inclusion kills the module map. -/
lemma killsOf_stabSubIncl (f : G ⟶ V) : KillsOf f (stabSubIncl f) :=
  (killsOf_iff_factors f _).2 ⟨𝟙 _, Category.id_comp _⟩

variable [ModObj G V]

/-- The multiplication of the stabilizer of a module map. -/
noncomputable def stabSubMul (f : G ⟶ V) [IsModHom G f] :
    stabSubObj f ⊗ stabSubObj f ⟶ stabSubObj f :=
  pullback.lift ((stabSubIncl f ⊗ₘ stabSubIncl f) ≫ μ[G]) (toUnit _) (by
    have e1 : (stabSubIncl f ⊗ₘ stabSubIncl f) ≫ G ◁ f
        = (stabSubObj f ◁ (stabSubIncl f ≫ f)) ≫ (stabSubIncl f ▷ V) := by
      rw [tensorHom_def', Category.assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        whisker_exchange]
    calc ((stabSubIncl f ⊗ₘ stabSubIncl f) ≫ μ[G]) ≫ f
        = (stabSubIncl f ⊗ₘ stabSubIncl f) ≫ G ◁ f ≫ γ[G, V] := by
          rw [Category.assoc, mul_comp_stabBasePoint f]
      _ = (stabSubObj f ◁ (stabSubIncl f ≫ f)) ≫ (stabSubIncl f ▷ V) ≫ γ[G, V] := by
          rw [← Category.assoc, e1, Category.assoc]
      _ = (stabSubObj f ◁ toUnit (stabSubObj f)) ≫ (stabSubObj f ◁ stabBasePoint f) ≫
            (stabSubIncl f ▷ V) ≫ γ[G, V] := by
          rw [stabSubIncl_comp f, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = (stabSubObj f ◁ toUnit (stabSubObj f)) ≫ (stabSubIncl f ▷ 𝟙_ C) ≫
            (G ◁ stabBasePoint f) ≫ γ[G, V] := by
          rw [whisker_exchange_assoc]
      _ = (stabSubObj f ◁ toUnit (stabSubObj f)) ≫ (stabSubIncl f ▷ 𝟙_ C) ≫
            (ρ_ G).hom ≫ f := by
          rw [unit_whisker_comp_stabBasePoint f]
      _ = (stabSubObj f ◁ toUnit (stabSubObj f)) ≫ (ρ_ (stabSubObj f)).hom ≫
            stabSubIncl f ≫ f := by
          rw [rightUnitor_naturality_assoc]
      _ = toUnit (stabSubObj f ⊗ stabSubObj f) ≫ stabBasePoint f := by
          rw [stabSubIncl_comp f, ← Category.assoc, ← Category.assoc]
          congr 1
          exact isTerminalTensorUnit.hom_ext _ _)

/-- The multiplication of the stabilizer is compatible with that of `G` along the inclusion. -/
@[reassoc (attr := simp)]
lemma stabSubMul_comp (f : G ⟶ V) [IsModHom G f] :
    stabSubMul f ≫ stabSubIncl f = (stabSubIncl f ⊗ₘ stabSubIncl f) ≫ μ[G] := by
  simp [stabSubMul]

/-- The monoid structure of the stabilizer of a module map. -/
@[instance_reducible]
noncomputable def stabSubMonObj (f : G ⟶ V) [IsModHom G f] : MonObj (stabSubObj f) :=
  letI := mono_stabSubIncl f
  monObjOfMono (stabSubIncl f) (stabSubOne f) (stabSubMul f) (stabSubOne_comp f)
    (stabSubMul_comp f)

/-- With the monoid structure `stabSubMonObj f`, the inclusion is a morphism of monoid objects. -/
lemma isMonHom_stabSubIncl (f : G ⟶ V) [IsModHom G f] :
    letI := mono_stabSubIncl f
    letI := stabSubMonObj f
    IsMonHom (stabSubIncl f) :=
  letI := mono_stabSubIncl f
  isMonHom_monObjOfMono (stabSubIncl f) (stabSubOne f) (stabSubMul f) (stabSubOne_comp f)
    (stabSubMul_comp f)

/-! ### The action on generalized elements -/

/-- The inverse morphism of the stabilizer of a module map. -/
noncomputable def stabInvOf (f : G ⟶ V) [IsModHom G f] : stabSubObj f ⟶ stabSubObj f :=
  ((killsOf_iff_factors f _).1 (killsOf_stabSubIncl f).inv).choose

/-- `stabInvOf f ≫ stabSubIncl f = (stabSubIncl f)⁻¹`. -/
@[reassoc (attr := simp)]
lemma stabInvOf_comp (f : G ⟶ V) [IsModHom G f] :
    stabInvOf f ≫ stabSubIncl f = (stabSubIncl f)⁻¹ :=
  ((killsOf_iff_factors f _).1 (killsOf_stabSubIncl f).inv).choose_spec

/-- **The stabilizer of a module map is a subgroup object of `G`.** -/
noncomputable abbrev stabOf (f : G ⟶ V) [IsModHom G f] : SubGrp G :=
  letI := mono_stabSubIncl f
  letI := stabSubMonObj f
  letI := isMonHom_stabSubIncl f
  letI : GrpObj (stabSubObj f) := grpObjOfMono (stabSubIncl f) (stabInvOf f) (stabInvOf_comp f)
  { N := stabSubObj f
    i := stabSubIncl f }

/-- The inclusion of the stabilizer `stabOf f` is `stabSubIncl f`. -/
lemma stabOf_i (f : G ⟶ V) [IsModHom G f] : (stabOf f).i = stabSubIncl f := rfl

/-! ## The stabilizer of a quotient module -/

/-- The stabilizer of the module map underlying a quotient module is Forsman's stabilizer
`InternalGroups.stab q`. -/
lemma stab_of_quot (q : QuotMod G) : stabOf (G := G) q.p.hom = stab q := rfl

end Stabiliser

variable [HasPullbacks C]


/-! ## Stabilizers of morphisms of group objects -/

/-- **A morphism of group objects is a stabilizer** if, up to an isomorphism in `Grp(C)/G`, it is
the inclusion of the stabilizer `stabOf f` of some module map `f : G ⟶ V` of `C^G`.  The module
map is not assumed to be an epimorphism: stabilizers are fibres of arbitrary equivariant maps. -/
def GrpIsStabilizer {G X : Grp C} (m : X ⟶ G) : Prop :=
  ∃ q : Under (selfMod (grpToAugMon.obj G).X),
    ∃ e : X ≅ (InternalGroups.stabOf (G := G.X) (V := q.right.X) q.hom.hom).toGrp,
      e.hom ≫ (InternalGroups.stabOf (G := G.X) (V := q.right.X) q.hom.hom).inclGrp = m

/-- The inclusion of the stabilizer of a module map is a stabilizer. -/
theorem isGrpStabilizer_stabOf {G : Grp C} (q : Under (selfMod (grpToAugMon.obj G).X)) :
    GrpIsStabilizer (InternalGroups.stabOf (G := G.X) (V := q.right.X) q.hom.hom).inclGrp :=
  ⟨q, Iso.refl _, Category.id_comp _⟩

/-- The inclusion of the stabilizer of a quotient module is a stabilizer. -/
theorem isGrpStabilizer_stab {G : Grp C} (q : InternalGroups.QuotMod G.X) :
    GrpIsStabilizer (InternalGroups.stab q).inclGrp :=
  isGrpStabilizer_stabOf (Under.mk q.p)

/-- Stabilizers are closed under isomorphisms in `Grp(C)/G`. -/
theorem GrpIsStabilizer.of_iso {G X X' : Grp C} {m : X ⟶ G} {m' : X' ⟶ G}
    (hm : GrpIsStabilizer m) (e : X' ≅ X) (he : e.hom ≫ m = m') : GrpIsStabilizer m' := by
  obtain ⟨q, e', he'⟩ := hm
  exact ⟨q, e ≪≫ e', by rw [Iso.trans_hom, Category.assoc, he', he]⟩
end InternalGroups
