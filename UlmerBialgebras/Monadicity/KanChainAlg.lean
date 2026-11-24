module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import UlmerBialgebras.Monadicity.KanChainSetup
public import UlmerBialgebras.Monadicity.RelAdjoint

/-!
# Algebras of `step` are extensions into the inserter

Continuing `KanChainSetup.lean`.  Let `F, G : C ⥤ D` and let `L : C ⥤ C` be an `F`-relative
left adjoint of `G`.  Transposition turns the structure morphism `F x ⟶ G x` of an object
of `Ins F G` into a morphism `L x ⟶ x`, so that for `d : I ⥤ Ins F G` with underlying
diagram `A = d ⋙ U` the transposed structure is a natural transformation `ψ : A ⋙ L ⟶ A`.

For that `ψ`, the algebras of the endofunctor `step` of `Ext k A` are exactly the
extensions of `d` along `k`, and the correspondence is bijective on morphisms.
Consequently an initial `step`-algebra is a left Kan extension of `d` along `k`
(`UlmerBialgebras.KanChain.isInitialExtOfAlg`).

This is the isomorphism `LE(d, k) ≅ Ins(H, id)` of Lemma 5.6, for an `F`-relative left
adjoint as in Theorem 5.7.

## Main results

* `UlmerBialgebras.KanChain.algOfExt`, `UlmerBialgebras.KanChain.extOfAlg`: the `step`-algebra
  attached to an extension of `d`, and the extension of `d` carried by a `step`-algebra.
* `UlmerBialgebras.KanChain.isInitialExtOfAlg`: an initial `step`-algebra gives an initial
  extension of `d` along `k`.
* `UlmerBialgebras.KanChain.hasLeftKanExtension_of_isInitial`: if there is an initial
  `step`-algebra, then `d` has a left Kan extension along `k`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.6 and Theorem 5.7
* [F. Ulmer, *Properties of dense and relative adjoint functors*][ulmerPropertiesDenseRelative1968]
-/

@[expose] public section

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace UlmerBialgebras

open CategoryTheory Limits Functor

variable {C : Type u} [Category.{v} C] {D : Type u₃} [Category.{v₃} D]
  {I : Type u₁} [Category.{v₁} I] {K : Type u₂} [Category.{v₂} K]

namespace KanChain

variable {F G : C ⥤ D} {L : C ⥤ C} (ra : RelLeftAdjoint F G L) (d : I ⥤ Ins F G)

/-- The diagram underlying `d`. -/
abbrev dgm : I ⥤ C := d ⋙ Ins.forget F G

variable (k : I ⥤ K)

/-- The extension of the underlying diagram carried by an extension of `d`. -/
@[implicit_reducible]
noncomputable def extBase (W : Functor.LeftExtension k d) : Ext k (dgm d) :=
  StructuredArrow.mk (Y := W.right ⋙ Ins.forget F G)
    (Functor.whiskerRight W.hom (Ins.forget F G))

/-- The functor underlying `extBase d k W` is `W.right ⋙ Ins.forget F G`. -/
@[simp] lemma extBase_right (W : Functor.LeftExtension k d) :
    (extBase d k W).right = W.right ⋙ Ins.forget F G := rfl

/-- Morphisms of extensions of `d` are determined by their underlying components. -/
lemma leftExt_hom_ext {W₁ W₂ : Functor.LeftExtension k d} (m₁ m₂ : W₁ ⟶ W₂)
    (h : ∀ x, (m₁.right.app x).base = (m₂.right.app x).base) : m₁ = m₂ := by
  apply StructuredArrow.hom_ext
  ext x
  exact h x

variable [HasLeftKanExtension k (dgm d)] [HasLeftKanExtension k (dgm d ⋙ L)]

/-- The compatibility making the algebra structure well defined. -/
lemma algCompat (W : Functor.LeftExtension k d) :
    bb L k (dgm d) (ra.insStrT d) ≫ cc k (dgm d) (extBase d k W)
      = (aa L k (dgm d) (extBase d k W)).right ≫ ra.insStrT W.right := by
  apply pp_hom_ext L k (dgm d)
  refine (whisker_eq _ (Functor.whiskerLeft_comp _ _ _)).trans
    (Eq.trans ?_ (whisker_eq _ (Functor.whiskerLeft_comp _ _ _)).symm)
  rw [← Category.assoc, ← Category.assoc, bb_hom, aa_hom, Category.assoc, cc_hom]
  ext i
  exact ra.cellT_naturality (W.hom.app i)

variable [HasPushouts C]

/-- The endofunctor of extensions attached to `d`. -/
noncomputable abbrev dstep : Ext k (dgm d) ⥤ Ext k (dgm d) :=
  step L k (dgm d) (ra.insStrT d)

/-! ## From extensions of `d` to algebras -/

/-- The `step`-algebra attached to an extension of `d`. -/
@[implicit_reducible]
noncomputable def algOfExt (W : Functor.LeftExtension k d) :
    Endofunctor.Algebra (dstep ra d k) where
  a := extBase d k W
  str := StructuredArrow.homMk
    (sDesc L k (dgm d) (ra.insStrT d) (cc k (dgm d) (extBase d k W))
      (ra.insStrT W.right) (algCompat ra d k W))
    (by
      dsimp
      rw [Category.assoc, ← Functor.whiskerLeft_comp, sInl_sDesc, cc_hom])

/-- The carrier of the algebra `algOfExt ra d k W` is `extBase d k W`. -/
@[simp] lemma algOfExt_a (W : Functor.LeftExtension k d) :
    (algOfExt ra d k W).a = extBase d k W := rfl

/-- The left leg of the structure of `algOfExt ra d k W` is `cc k (dgm d) (extBase d k W)`. -/
@[reassoc (attr := simp)]
lemma sInl_algOfExt_str (W : Functor.LeftExtension k d) :
    sInl L k (dgm d) (ra.insStrT d) (extBase d k W) ≫ (algOfExt ra d k W).str.right
      = cc k (dgm d) (extBase d k W) :=
  sInl_sDesc _ _ _ _ _ _ _

/-- The right leg of the structure of `algOfExt ra d k W` is `ra.insStrT W.right`. -/
@[reassoc (attr := simp)]
lemma sInr_algOfExt_str (W : Functor.LeftExtension k d) :
    sInr L k (dgm d) (ra.insStrT d) (extBase d k W) ≫ (algOfExt ra d k W).str.right
      = ra.insStrT W.right :=
  sInr_sDesc _ _ _ _ _ _ _

/-! ## From algebras to extensions of `d` -/

variable (M : Endofunctor.Algebra (dstep ra d k))

/-- The structure map carried by an algebra. -/
noncomputable def algCell : M.a.right ⋙ L ⟶ M.a.right :=
  sInr L k (dgm d) (ra.insStrT d) M.a ≫ M.str.right

/-- The left leg of the algebra structure is the canonical map out of the initial
extension. -/
lemma sInl_str : sInl L k (dgm d) (ra.insStrT d) M.a ≫ M.str.right = cc k (dgm d) M.a := by
  have h : (ee k (dgm d)).hom ≫ Functor.whiskerLeft k
      (sInl L k (dgm d) (ra.insStrT d) M.a ≫ M.str.right) = M.a.hom := by
    rw [Functor.whiskerLeft_comp, ← Category.assoc]
    exact StructuredArrow.w M.str
  have := initial.hom_ext (StructuredArrow.homMk (f' := M.a)
      (sInl L k (dgm d) (ra.insStrT d) M.a ≫ M.str.right) h) (initial.to M.a)
  exact (CommaMorphism.ext_iff.mp this).2

/-- The unit of an algebra is compatible with the structure maps. -/
lemma alg_w : ra.insStrT d ≫ M.a.hom
    = Functor.whiskerRight M.a.hom L ≫ Functor.whiskerLeft k (algCell ra d k M) := by
  have h0 : bb L k (dgm d) (ra.insStrT d) ≫ cc k (dgm d) M.a
      = (aa L k (dgm d) M.a).right ≫ algCell ra d k M := by
    rw [← sInl_str ra d k M, algCell, ← Category.assoc, ← Category.assoc, sq]
  have h : (pp L k (dgm d)).hom ≫ Functor.whiskerLeft k
        (bb L k (dgm d) (ra.insStrT d) ≫ cc k (dgm d) M.a)
      = (pp L k (dgm d)).hom ≫ Functor.whiskerLeft k
        ((aa L k (dgm d) M.a).right ≫ algCell ra d k M) := by rw [h0]
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, ← Category.assoc, ← Category.assoc,
    bb_hom, aa_hom, Category.assoc, cc_hom] at h
  exact h

/-- The functor `K ⥤ Ins F G` carried by an algebra. -/
noncomputable def algFunctor : K ⥤ Ins F G :=
  ra.liftFunctorT M.a.right (algCell ra d k M)

/-- The diagram underlying `algFunctor ra d k M` is `M.a.right`. -/
@[simp] lemma algFunctor_forget : algFunctor ra d k M ⋙ Ins.forget F G = M.a.right := rfl

/-- The transposed structure of `(algFunctor ra d k M).obj x` is `(algCell ra d k M).app x`. -/
@[simp] lemma cellT_algFunctor (x : K) :
    ra.cellT ((algFunctor ra d k M).obj x) = (algCell ra d k M).app x :=
  ra.cellT_liftFunctorT _ _ x

/-- Componentwise form of the compatibility `alg_w`. -/
lemma cellT_alg_w (i : I) :
    ra.cellT (d.obj i) ≫ M.a.hom.app i
      = L.map (M.a.hom.app i) ≫ ra.cellT ((algFunctor ra d k M).obj (k.obj i)) := by
  rw [cellT_algFunctor]
  have h := congr_app (alg_w ra d k M) i
  simp only [comp_obj, Ins.forget_obj, whiskeringLeft_obj_obj, NatTrans.comp_app,
    RelLeftAdjoint.insStrT_app, whiskerRight_app, whiskerLeft_app] at h
  exact h

/-- The extension of `d` carried by an algebra. -/
@[implicit_reducible]
noncomputable def extOfAlg : Functor.LeftExtension k d :=
  StructuredArrow.mk (Y := algFunctor ra d k M)
    { app := fun i => ⟨M.a.hom.app i, ra.isHom_of_cellT (x := d.obj i)
        (y := (algFunctor ra d k M).obj (k.obj i)) _ (cellT_alg_w ra d k M i)⟩
      naturality := fun i j f => by
        apply Ins.hom_ext
        exact M.a.hom.naturality f }

/-- The functor of the extension `extOfAlg ra d k M` is `algFunctor ra d k M`. -/
@[simp] lemma extOfAlg_right : (extOfAlg ra d k M).right = algFunctor ra d k M := rfl

/-- The components of the unit of `extOfAlg ra d k M` have underlying morphisms
`M.a.hom.app i`. -/
@[simp] lemma extOfAlg_hom_app_base (i : I) :
    ((extOfAlg ra d k M).hom.app i).base = M.a.hom.app i := rfl

/-! ## The correspondence on morphisms -/

section Hom

variable (W : Functor.LeftExtension k d)

/-- The underlying morphism of extensions of a morphism of extensions of `d`. -/
noncomputable def algHomBase (m : extOfAlg ra d k M ⟶ W) : M.a ⟶ extBase d k W :=
  StructuredArrow.homMk (Functor.whiskerRight m.right (Ins.forget F G)) (by
    ext i
    exact Ins.Hom.ext_iff.mp (NatTrans.congr_app (StructuredArrow.w m) i))

/-- The natural transformation underlying `algHomBase ra d k M W m` is `m.right` whiskered
by `Ins.forget F G`. -/
@[simp] lemma algHomBase_right (m : extOfAlg ra d k M ⟶ W) :
    (algHomBase ra d k M W m).right = Functor.whiskerRight m.right (Ins.forget F G) := rfl

/-- A morphism of extensions of `d` gives a morphism of algebras. -/
noncomputable def algHomOfHom (m : extOfAlg ra d k M ⟶ W) : M ⟶ algOfExt ra d k W where
  f := algHomBase ra d k M W m
  h := by
    apply StructuredArrow.hom_ext
    simp only [StructuredArrow.comp_right, algOfExt_a]
    apply stepObj_hom_ext
    · rw [← Category.assoc, sInl_step_map, sInl_algOfExt_str, ← Category.assoc, sInl_str]
      exact (cc_naturality k (dgm d) (algHomBase ra d k M W m)).symm
    · rw [← Category.assoc, sInr_step_map, Category.assoc, sInr_algOfExt_str, ← Category.assoc]
      ext x
      change L.map (m.right.app x).base ≫ ra.cellT (W.right.obj x)
        = (algCell ra d k M).app x ≫ (m.right.app x).base
      rw [← cellT_algFunctor]
      exact (ra.cellT_naturality (m.right.app x)).symm

/-- The compatibility of a morphism of algebras with the structure maps. -/
lemma algHom_cell (f : M ⟶ algOfExt ra d k W) :
    algCell ra d k M ≫ f.f.right
      = Functor.whiskerRight f.f.right L ≫ ra.insStrT W.right := by
  have h : ((dstep ra d k).map f.f).right ≫ (algOfExt ra d k W).str.right
      = M.str.right ≫ f.f.right := (CommaMorphism.ext_iff.mp f.h).2
  have h2 := sInr L k (dgm d) (ra.insStrT d) M.a ≫= h
  rw [← Category.assoc, sInr_step_map, Category.assoc] at h2
  rw [algCell, Category.assoc, ← h2]
  congr 1
  exact sInr_algOfExt_str ra d k W

/-- Componentwise form of the compatibility `algHom_cell`. -/
lemma cellT_algHom_cell (f : M ⟶ algOfExt ra d k W) (x : K) :
    ra.cellT ((algFunctor ra d k M).obj x) ≫ f.f.right.app x
      = L.map (f.f.right.app x) ≫ ra.cellT (W.right.obj x) := by
  rw [cellT_algFunctor]
  have h := congr_app (algHom_cell ra d k M W f) x
  simp only [comp_obj, algOfExt_a, extBase_right, Ins.forget_obj, NatTrans.comp_app,
    whiskerRight_app, RelLeftAdjoint.insStrT_app] at h
  exact h

/-- A morphism of algebras gives a morphism of extensions of `d`. -/
noncomputable def homOfAlgHom (f : M ⟶ algOfExt ra d k W) : extOfAlg ra d k M ⟶ W :=
  StructuredArrow.homMk
    { app := fun x => ⟨f.f.right.app x, ra.isHom_of_cellT (x := (algFunctor ra d k M).obj x)
        (y := W.right.obj x) _ (cellT_algHom_cell ra d k M W f x)⟩
      naturality := fun x y g => by
        apply Ins.hom_ext
        exact f.f.right.naturality g }
    (by
      ext i
      exact congr_app (StructuredArrow.w f.f) i)

/-- `homOfAlgHom` is a left inverse of `algHomOfHom`. -/
lemma homOfAlgHom_algHomOfHom (m : extOfAlg ra d k M ⟶ W) :
    homOfAlgHom ra d k M W (algHomOfHom ra d k M W m) = m := by
  apply leftExt_hom_ext
  intro x
  rfl

end Hom

/-- **An initial `step`-algebra is a left Kan extension of `d` along `k`.** -/
noncomputable def isInitialExtOfAlg (hM : IsInitial M) : IsInitial (extOfAlg ra d k M) :=
  IsInitial.ofUniqueHom (fun W => homOfAlgHom ra d k M W (hM.to _)) (fun W m => by
    rw [← homOfAlgHom_algHomOfHom ra d k M W m]
    congr 1
    exact hM.hom_ext _ _)

/-- If there is an initial `step`-algebra, then `d` has a left Kan extension along `k`. -/
theorem hasLeftKanExtension_of_isInitial (hM : IsInitial M) :
    HasLeftKanExtension k d :=
  (isInitialExtOfAlg ra d k M hM).hasInitial

end KanChain

end UlmerBialgebras
