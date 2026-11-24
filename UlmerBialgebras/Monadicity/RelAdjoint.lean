module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Relative left adjoints

Let `F, G : C ⥤ D` be a parallel pair of functors.  An **`F`-relative left adjoint** of `G`
is an endofunctor `L : C ⥤ C` together with a bijection

  `(L x ⟶ y) ≃ (F x ⟶ G y)`

natural in `x` and in `y` (`UlmerBialgebras.RelLeftAdjoint`).  When `G` has an honest left adjoint
`H : D ⥤ C`, the composite `F ⋙ H` is an `F`-relative left adjoint of `G`
(`UlmerBialgebras.RelLeftAdjoint.ofAdjunction`), so this notion is strictly more general.

The two main constructions of this file are:

* `UlmerBialgebras.RelLeftAdjoint.preservesColimit` — a relative left adjoint `L` preserves every
  colimit that `F` preserves.  (This is what makes the transfinite constructions of free
  objects run: only `F` is assumed to preserve the relevant colimits.)
* the comparison with the *absolute* case: transposition along the bijection identifies
  `Ins F G` with `Ins L (𝟭 C)` over `C` (`UlmerBialgebras.RelLeftAdjoint.insEquivalence`,
  `UlmerBialgebras.RelLeftAdjoint.insEquivalence_forget`), and identifies the equifier of
  `α, β : F ⟶ G` with the equifier of the transposed pair `L ⟶ 𝟭 C`
  (`UlmerBialgebras.RelLeftAdjoint.equifProp_eq`).  Since `𝟭 C` is its own left adjoint, this
  reduces the relative situation to the absolute one.

## Main results

* `UlmerBialgebras.RelLeftAdjoint`: `F`-relative left adjoints `L` of `G`, with
  `(L x ⟶ y) ≃ (F x ⟶ G y)` natural in `x` and `y`.
* `UlmerBialgebras.RelLeftAdjoint.ofAdjunction`: a left adjoint `H ⊣ G` gives the `F`-relative left
  adjoint `F ⋙ H` of `G`.
* `UlmerBialgebras.RelLeftAdjoint.preservesColimit`: `L` preserves every colimit that `F` preserves.
* `UlmerBialgebras.RelLeftAdjoint.insEquivalence`,
  `UlmerBialgebras.RelLeftAdjoint.insEquivalence_forget`: an equivalence `Ins F G ≌ Ins L (𝟭 C)`
  commuting with the forgetful functors.
* `UlmerBialgebras.RelLeftAdjoint.equifProp_eq`: the equifier of `α, β : F ⟶ G` is the equifier of
  their transposes `L ⟶ 𝟭 C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.2,
  Theorem 5.5
* [F. Ulmer, *Properties of dense and relative adjoint
  functors*][ulmerPropertiesDenseRelative1968]
-/

@[expose] public section

universe w w' v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- An `F`-relative left adjoint of `G`: an endofunctor `L` of `C` together with a
bijection `(L x ⟶ y) ≃ (F x ⟶ G y)` natural in `x` and `y`. -/
structure RelLeftAdjoint (F G : C ⥤ D) (L : C ⥤ C) where
  /-- The transposition bijection. -/
  homEquiv (x y : C) : (L.obj x ⟶ y) ≃ (F.obj x ⟶ G.obj y)
  /-- Naturality in the first variable. -/
  homEquiv_naturality_left {x x' y : C} (f : x' ⟶ x) (g : L.obj x ⟶ y) :
    homEquiv x' y (L.map f ≫ g) = F.map f ≫ homEquiv x y g
  /-- Naturality in the second variable. -/
  homEquiv_naturality_right {x y y' : C} (g : L.obj x ⟶ y) (h : y ⟶ y') :
    homEquiv x y' (g ≫ h) = homEquiv x y g ≫ G.map h

namespace RelLeftAdjoint

variable {F G : C ⥤ D} {L : C ⥤ C} (ra : RelLeftAdjoint F G L)

/-- The inverse transposition is natural in the first variable. -/
lemma homEquiv_symm_naturality_left {x x' y : C} (f : x' ⟶ x) (g : F.obj x ⟶ G.obj y) :
    (ra.homEquiv x' y).symm (F.map f ≫ g) = L.map f ≫ (ra.homEquiv x y).symm g := by
  apply (ra.homEquiv x' y).injective
  rw [Equiv.apply_symm_apply, ra.homEquiv_naturality_left, Equiv.apply_symm_apply]

/-- The inverse transposition is natural in the second variable. -/
lemma homEquiv_symm_naturality_right {x y y' : C} (g : F.obj x ⟶ G.obj y) (h : y ⟶ y') :
    (ra.homEquiv x y').symm (g ≫ G.map h) = (ra.homEquiv x y).symm g ≫ h := by
  apply (ra.homEquiv x y').injective
  rw [Equiv.apply_symm_apply, ra.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- An honest left adjoint `H ⊣ G` gives an `F`-relative left adjoint `F ⋙ H` of `G`. -/
@[simps]
def ofAdjunction {H : D ⥤ C} (adj : H ⊣ G) (F : C ⥤ D) : RelLeftAdjoint F G (F ⋙ H) where
  homEquiv x y := adj.homEquiv (F.obj x) y
  homEquiv_naturality_left f g := by
    simpa using (adj.homEquiv_naturality_left (F.map f) g)
  homEquiv_naturality_right g h := adj.homEquiv_naturality_right g h

/-! ## Preservation of colimits -/

section Preserves

variable {J : Type w} [Category.{w'} J] (K : J ⥤ C)

/-- The cocone on `K ⋙ F` with vertex `G s.pt` obtained by transposing a cocone on
`K ⋙ L`. -/
@[simps]
def transposeCocone (s : Cocone (K ⋙ L)) : Cocone (K ⋙ F) where
  pt := G.obj s.pt
  ι :=
    { app := fun j => ra.homEquiv (K.obj j) s.pt (s.ι.app j)
      naturality := fun j j' u => by
        have h : s.ι.app j = L.map (K.map u) ≫ s.ι.app j' := (s.w u).symm
        dsimp
        rw [Category.comp_id, h, ra.homEquiv_naturality_left] }

include ra in
/-- **A relative left adjoint preserves every colimit that `F` preserves.** -/
lemma preservesColimit [PreservesColimit K F] : PreservesColimit K L := by
  constructor
  intro c hc
  have hF : IsColimit (F.mapCocone c) := isColimitOfPreserves F hc
  refine ⟨IsColimit.ofExistsUnique fun s => ?_⟩
  have key : ∀ (m : L.obj c.pt ⟶ s.pt) (j : J),
      ra.homEquiv (K.obj j) s.pt (L.map (c.ι.app j) ≫ m)
        = F.map (c.ι.app j) ≫ ra.homEquiv c.pt s.pt m := fun m j =>
    ra.homEquiv_naturality_left (x := c.pt) (y := s.pt) (c.ι.app j) m
  refine ⟨(ra.homEquiv c.pt s.pt).symm (hF.desc (ra.transposeCocone K s)), ?_, ?_⟩
  · intro j
    apply (ra.homEquiv (K.obj j) s.pt).injective
    rw [show (L.mapCocone c).ι.app j ≫ (ra.homEquiv c.pt s.pt).symm
          (hF.desc (ra.transposeCocone K s))
        = L.map (c.ι.app j) ≫ (ra.homEquiv c.pt s.pt).symm
          (hF.desc (ra.transposeCocone K s)) from rfl,
      key]
    exact (whisker_eq _ (Equiv.apply_symm_apply _ _)).trans (hF.fac (ra.transposeCocone K s) j)
  · intro m hm
    apply (ra.homEquiv c.pt s.pt).injective
    refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
    refine hF.hom_ext fun j => ?_
    exact ((key m j).symm.trans congr(ra.homEquiv (K.obj j) s.pt $(hm j))).trans
      (hF.fac (ra.transposeCocone K s) j).symm

include ra in
/-- A relative left adjoint `L` preserves colimits of shape `J` whenever `F` does. -/
lemma preservesColimitsOfShape [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J L :=
  ⟨fun {K} => ra.preservesColimit K⟩

end Preserves

/-! ## Reduction of the relative case to the absolute case -/

/-- Transposition of the structure morphism: an object of `Ins F G` as an object of
`Ins L (𝟭 C)`. -/
@[simps, implicit_reducible]
def toIns : Ins F G ⥤ Ins L (𝟭 C) where
  obj x := ⟨x.pt, (ra.homEquiv x.pt x.pt).symm x.cell⟩
  map {x y} f :=
    ⟨f.base, by
      apply (ra.homEquiv x.pt y.pt).injective
      dsimp
      rw [ra.homEquiv_naturality_left, ra.homEquiv_naturality_right,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact f.w⟩

/-- The inverse construction: an object of `Ins L (𝟭 C)` as an object of `Ins F G`. -/
@[simps, implicit_reducible]
def fromIns : Ins L (𝟭 C) ⥤ Ins F G where
  obj x := ⟨x.pt, ra.homEquiv x.pt x.pt x.cell⟩
  map {x y} f :=
    ⟨f.base, by
      dsimp
      rw [← ra.homEquiv_naturality_left, ← ra.homEquiv_naturality_right]
      exact congr(ra.homEquiv x.pt y.pt $(f.w))⟩

/-- `Ins F G` is isomorphic to `Ins L (𝟭 C)`, over `C`. -/
@[simps]
def insEquivalence : Ins F G ≌ Ins L (𝟭 C) where
  functor := ra.toIns
  inverse := ra.fromIns
  unitIso := NatIso.ofComponents
    (fun x =>
      { hom := ⟨𝟙 x.pt, by simp⟩
        inv := ⟨𝟙 x.pt, by simp⟩ })
    (fun f => by ext; simp)
  counitIso := NatIso.ofComponents
    (fun x =>
      { hom := ⟨𝟙 x.pt, by simp⟩
        inv := ⟨𝟙 x.pt, by simp⟩ })
    (fun f => by ext; simp)
  functor_unitIso_comp x := by ext; simp

/-- `toIns` commutes with the forgetful functors: `toIns ⋙ Ins.forget L (𝟭 C) = Ins.forget F G`. -/
lemma insEquivalence_forget :
    ra.toIns ⋙ Ins.forget L (𝟭 C) = Ins.forget F G := rfl

include ra in
/-- If the forgetful functor of `Ins L (𝟭 C)` has a left adjoint, so has that of
`Ins F G`. -/
theorem ins_forget_isRightAdjoint (h : (Ins.forget L (𝟭 C)).IsRightAdjoint) :
    (Ins.forget F G).IsRightAdjoint := by
  have := h
  have : ra.toIns.IsRightAdjoint := ra.insEquivalence.isRightAdjoint_functor
  rw [← ra.insEquivalence_forget]
  infer_instance

/-! ### Transposed cells -/

/-- The transpose `L x ⟶ x` of the structure morphism of an object of the inserter. -/
noncomputable def cellT (x : Ins F G) : L.obj x.pt ⟶ x.pt :=
  (ra.homEquiv x.pt x.pt).symm x.cell

/-- Transposing `cellT x` back along `ra.homEquiv` gives the structure morphism `x.cell`. -/
@[simp] lemma homEquiv_cellT (x : Ins F G) : ra.homEquiv x.pt x.pt (ra.cellT x) = x.cell :=
  Equiv.apply_symm_apply _ _

/-- A morphism of the inserter commutes with the transposed structure morphisms. -/
@[reassoc]
lemma cellT_naturality {x y : Ins F G} (f : x ⟶ y) :
    ra.cellT x ≫ f.base = L.map f.base ≫ ra.cellT y := by
  apply (ra.homEquiv x.pt y.pt).injective
  rw [ra.homEquiv_naturality_right, ra.homEquiv_naturality_left, homEquiv_cellT,
    homEquiv_cellT]
  exact f.w

/-- Conversely, a morphism of the underlying objects commuting with the transposed
structure morphisms is a morphism of the inserter. -/
lemma isHom_of_cellT {x y : Ins F G} (g : x.pt ⟶ y.pt)
    (h : ra.cellT x ≫ g = L.map g ≫ ra.cellT y) :
    x.cell ≫ G.map g = F.map g ≫ y.cell := by
  have := congr(ra.homEquiv x.pt y.pt $h)
  rwa [ra.homEquiv_naturality_right, ra.homEquiv_naturality_left, homEquiv_cellT,
    homEquiv_cellT] at this

/-- The transposed structure morphisms of a functor into the inserter. -/
@[simps]
noncomputable def insStrT {X : Type*} [Category X] (z : X ⥤ Ins F G) :
    (z ⋙ Ins.forget F G) ⋙ L ⟶ z ⋙ Ins.forget F G where
  app x := ra.cellT (z.obj x)
  naturality _ _ f := (ra.cellT_naturality (z.map f)).symm

/-- A functor into the inserter, given by transposed structure data. -/
@[simps]
noncomputable def liftFunctorT {X : Type*} [Category X] (z : X ⥤ C) (lam : z ⋙ L ⟶ z) :
    X ⥤ Ins F G where
  obj x := ⟨z.obj x, ra.homEquiv (z.obj x) (z.obj x) (lam.app x)⟩
  map {x y} f := ⟨z.map f, by
    change ra.homEquiv (z.obj x) (z.obj x) (lam.app x) ≫ G.map (z.map f)
      = F.map (z.map f) ≫ ra.homEquiv (z.obj y) (z.obj y) (lam.app y)
    rw [← ra.homEquiv_naturality_right, ← ra.homEquiv_naturality_left]
    exact congr(ra.homEquiv (z.obj x) (z.obj y) $((lam.naturality f).symm))⟩
  map_id x := by ext; exact z.map_id x
  map_comp f g := by ext; exact z.map_comp f g

/-- The transposed structure morphism of `liftFunctorT z lam` at `x` is `lam.app x`. -/
@[simp] lemma cellT_liftFunctorT {X : Type*} [Category X] (z : X ⥤ C) (lam : z ⋙ L ⟶ z)
    (x : X) : ra.cellT ((ra.liftFunctorT z lam).obj x) = lam.app x :=
  (ra.homEquiv _ _).symm_apply_apply _

/-! ### Equifiers -/

/-- The transpose of a natural transformation `F ⟶ G` as a natural transformation
`L ⟶ 𝟭 C`. -/
@[simps]
def transposeNat (α : F ⟶ G) : L ⟶ 𝟭 C where
  app x := (ra.homEquiv x x).symm (α.app x)
  naturality {x y} f := by
    dsimp
    rw [← ra.homEquiv_symm_naturality_left, ← ra.homEquiv_symm_naturality_right]
    exact congr((ra.homEquiv x y).symm $(α.naturality f))

/-- The transposes of `α` and `β` agree at `x` iff `α.app x = β.app x`. -/
lemma transposeNat_app_iff (α β : F ⟶ G) (x : C) :
    (ra.transposeNat α).app x = (ra.transposeNat β).app x ↔ α.app x = β.app x := by
  simp [transposeNat]

/-- The equifier of `α, β : F ⟶ G` is the equifier of their transposes. -/
lemma equifProp_eq (α β : F ⟶ G) :
    equifProp α β = equifProp (ra.transposeNat α) (ra.transposeNat β) :=
  funext fun x => propext (ra.transposeNat_app_iff α β x).symm

end RelLeftAdjoint

end UlmerBialgebras
