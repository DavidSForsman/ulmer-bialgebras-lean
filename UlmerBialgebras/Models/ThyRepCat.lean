module

public import UlmerBialgebras.Models.ThyRepCatEval

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Reindexing of `T`-algebras in `K(x, M)` and naturality in `x`

Precomposition with a 1-cell `k : x' → x` and 2-cells `α : k ⇒ k'` on `T`-algebras of
`K(x, M)` in `CAT`, together with naturality of the comparison isomorphism `K(x, E) ≅ K(x, M)^T`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (x : Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

/-! ### Precomposition with a 1-cell `k : x' → x` -/

section Reindex

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)

omit [Bicategory.Strict Obj] [HasChosenFinProducts Obj] in
/-- 2-cells of `CAT` between equal 1-cells with `ConjEq` components are `ConjEq`. -/
lemma cat_conjEq_of_app {C D : Cat.{w, v}} {F F' G G' : C ⟶ D} (hF : F = F') (hG : G = G')
    {α : F ⟶ G} {β : F' ⟶ G'} (h : ∀ d, ConjEq (α.toNatTrans.app d) (β.toNatTrans.app d)) :
    ConjEq α β := by
  subst hF hG
  exact ConjEq.of_eq (Cat.Hom₂.ext (NatTrans.ext (funext fun d => (h d).eq)))

variable {x' : Obj} (k : x' ⟶ x) {D : Cat.{w, v}}

/-- The environment of `K(x', M)` obtained by precomposing with `k`. -/
abbrev reindexEnv (ε : ∀ s : sg.Srt, D ⟶ (M.homModel x).obj (sg.sty s)) (s : sg.Srt) :
    D ⟶ (M.homModel x').obj (sg.sty s) :=
  ε s ≫ (precomp k (M.obj (sg.sty s))).toCatHom

/-- Naturality of `reindexCell k Y g` in `d : D`. -/
lemma reindexCell_naturality (Y : (M.homModel x).Alg sg T D) (g : sg.Fn)
    {d d' : D} (φ : d ⟶ d') :
    ((M.homModel x').interp (M.reindexEnv x sg k Y.env) (sg.fndom g)).toFunctor.map φ ≫
      (eqToHom (M.homInterp_obj x' sg (M.reindexEnv x sg k Y.env) d' _) ≫
        ((M.evalAlgAt x sg T Y d').precomp k).cell g ≫
        eqToHom (M.homInterp_obj x' sg (M.reindexEnv x sg k Y.env) d' _).symm) =
    (eqToHom (M.homInterp_obj x' sg (M.reindexEnv x sg k Y.env) d _) ≫
        ((M.evalAlgAt x sg T Y d).precomp k).cell g ≫
        eqToHom (M.homInterp_obj x' sg (M.reindexEnv x sg k Y.env) d _).symm) ≫
      ((M.homModel x').interp (M.reindexEnv x sg k Y.env) (sg.fncod g)).toFunctor.map φ := by
  have hm : ∀ t : sg.CTrm (sg.fnty g), ConjEq (((M.homModel x').interp
      (M.reindexEnv x sg k Y.env) t).toFunctor.map φ)
      (k ◁ M.interpCell (fun s => (Y.env s).toFunctor.map φ) t) := fun t =>
    (M.homInterp_map x' _ φ t).trans (M.whiskerLeft_interpCell _ k t)
  have hc : ∀ d, ConjEq (((M.evalAlgAt x sg T Y d).precomp k).cell g)
      (k ◁ M.evalCells x sg Y.env Y.cell d g) := fun d => ConjEq.conj _ _ _
  refine (ConjEq.eq_iff (ConjEq.comp (hm _) ((ConjEq.conj _ _ _).trans (hc d')))
    (ConjEq.comp ((ConjEq.conj _ _ _).trans (hc d)) (hm _))).mpr ?_
  exact (Bicategory.whiskerLeft_comp k _ _).symm.trans
    (congr(k ◁ $(((M.evalHomAt x sg T Y φ).comm g).symm)).trans
      (Bicategory.whiskerLeft_comp k _ _))

/-- The 2-cells of `K(x', M)` obtained by precomposing with `k`: at `d`, the 2-cells of the
evaluation at `d`, whiskered by `k`. -/
def reindexCell (Y : (M.homModel x).Alg sg T D) (g : sg.Fn) :
    (M.homModel x').interp (M.reindexEnv x sg k Y.env) (sg.fndom g) ⟶
      (M.homModel x').interp (M.reindexEnv x sg k Y.env) (sg.fncod g) :=
  NatTrans.toCatHom₂
    { app := fun d => eqToHom (M.homInterp_obj x' sg (M.reindexEnv x sg k Y.env) d _) ≫
        ((M.evalAlgAt x sg T Y d).precomp k).cell g ≫
        eqToHom (M.homInterp_obj x' sg (M.reindexEnv x sg k Y.env) d _).symm
      naturality := fun _ _ φ => M.reindexCell_naturality x sg T k Y g φ }

/-- The component at `d` of `reindexCell k Y g` is the 2-cell of the evaluation of `Y` at `d`,
precomposed with `k`, up to `ConjEq`. -/
lemma reindexCell_app (Y : (M.homModel x).Alg sg T D) (g : sg.Fn) (d : D) :
    ConjEq ((M.reindexCell x sg T k Y g).toNatTrans.app d)
      (((M.evalAlgAt x sg T Y d).precomp k).cell g) :=
  ConjEq.conj _ _ _

/-- The reindexed 2-cells satisfy the equations of `T`: for each equation `r`, the path cells of
its two sides agree. -/
lemma reindex_eqn (Y : (M.homModel x).Alg sg T D) (r : T.Eqn) :
    (M.homModel x').pathCellAlg sg (M.reindexEnv x sg k Y.env)
        (M.reindexCell x sg T k Y) (T.lhs r) =
      (M.homModel x').pathCellAlg sg (M.reindexEnv x sg k Y.env)
        (M.reindexCell x sg T k Y) (T.rhs r) := by
  ext d
  have hc : ∀ g, ConjEq (M.evalCells x' sg (M.reindexEnv x sg k Y.env)
      (M.reindexCell x sg T k Y) d g) (((M.evalAlgAt x sg T Y d).precomp k).cell g) := fun g =>
    (ConjEq.conj _ _ _).trans (M.reindexCell_app x sg T k Y g d)
  exact (ConjEq.eq_iff
    ((M.homPathCellAlg_app x' sg _ _ d (T.lhs r)).trans (M.pathCellAlg_congr sg rfl hc _))
    ((M.homPathCellAlg_app x' sg _ _ d (T.rhs r)).trans (M.pathCellAlg_congr sg rfl hc _))).mpr
    (((M.evalAlgAt x sg T Y d).precomp k).eqn r)

/-- **Reindexing along `k : x' → x`**: the `T`-algebra of `K(x', M)` over `D` whose evaluation at
`d` is the evaluation of `Y` at `d`, precomposed with `k`. -/
def reindex (Y : (M.homModel x).Alg sg T D) : (M.homModel x').Alg sg T D where
  env := M.reindexEnv x sg k Y.env
  cell := M.reindexCell x sg T k Y
  eqn r := M.reindex_eqn x sg T k Y r

/-- Reindexing along `k` commutes with precomposition by a 1-cell `G : D' ⟶ D`. -/
lemma reindex_precomp {D' : Cat.{w, v}} (Y : (M.homModel x).Alg sg T D) (G : D' ⟶ D) :
    M.reindex x sg T k (Y.precomp G) = (M.reindex x sg T k Y).precomp G := by
  refine Alg.ext' rfl fun g => cat_conjEq_of_app rfl rfl fun d' => ?_
  refine (M.reindexCell_app x sg T k _ g d').trans ?_
  refine (Alg.cell_conjEq_of_eq sg T
    congr(($(M.evalAlgAt_precomp x sg T Y G d')).precomp k) g).trans ?_
  exact ((M.precomp_cell_app x' sg T _ G d' g).trans (M.reindexCell_app x sg T k Y g _)).symm

/-- Reindexing the evaluation algebra of `A` at `x` along `k : x' → x` gives the evaluation algebra
of `A` at `x'`, precomposed with `K(k, E)`. -/
lemma evalAlg_reindex {E : Obj} (A : M.Alg sg T E) :
    M.reindex x sg T k (M.evalAlg x sg T A) =
      (M.evalAlg x' sg T A).precomp (precomp k E).toCatHom := by
  have he : M.reindexEnv x sg k (M.evalAlg x sg T A).env =
      ((M.evalAlg x' sg T A).precomp (precomp k E).toCatHom).env :=
    funext fun s => Cat.Hom.ext (CategoryTheory.Functor.ext
      (fun h => (Category.assoc k h (A.env s)).symm) fun h h' α => by
        obtain ⟨p, q, e⟩ := ConjEq.whiskerLeft_whiskerRight k α (A.env s)
        exact e)
  refine Alg.ext' he fun g => cat_conjEq_of_app
    congr((M.homModel x').interp $he (sg.fndom g))
    congr((M.homModel x').interp $he (sg.fncod g)) fun h => ?_
  refine (M.reindexCell_app x sg T k _ g h).trans ?_
  refine (Alg.cell_conjEq_of_eq sg T
    congr(($(M.evalAlgAt_evalAlg x sg T A h)).precomp k) g).trans ?_
  refine (Alg.cell_conjEq_of_eq sg T (Alg.precomp_precomp A h k) g).trans ?_
  exact ((M.precomp_cell_app x' sg T _ _ h g).trans (M.evalCell_app x' sg T A g _)).symm

end Reindex

section Reindex₂

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)

variable {x' : Obj} {k k' : x' ⟶ x} (α : k ⟶ k') {D : Cat.{w, v}}

/-- For `α : k ⇒ k'`, the 2-cell from the environment reindexed along `k` to the one reindexed
along `k'`: at `d`, `α ▷ ε_s(d)`. -/
def reindexEnvHom (ε : ∀ s : sg.Srt, D ⟶ (M.homModel x).obj (sg.sty s)) (s : sg.Srt) :
    M.reindexEnv x sg k ε s ⟶ M.reindexEnv x sg k' ε s :=
  NatTrans.toCatHom₂
    { app := fun d => α ▷ (ε s).toFunctor.obj d
      naturality := fun _ _ φ => Bicategory.whisker_exchange α ((ε s).toFunctor.map φ) }

/-- The component of `reindexEnvHom α ε s` at `d` is `α ▷ ε_s(d)`. -/
lemma reindexEnvHom_app (ε : ∀ s : sg.Srt, D ⟶ (M.homModel x).obj (sg.sty s)) (s : sg.Srt)
    (d : D) : (M.reindexEnvHom x sg α ε s).toNatTrans.app d = α ▷ (ε s).toFunctor.obj d := rfl

/-- Naturality of `reindexHom` with respect to function symbols. -/
lemma reindexHom_comm (Y : (M.homModel x).Alg sg T D) (f : sg.Fn) :
    (M.reindex x sg T k Y).cell f ≫
        (M.homModel x').interpCell (M.reindexEnvHom x sg α Y.env) (sg.fncod f) =
      (M.homModel x').interpCell (M.reindexEnvHom x sg α Y.env) (sg.fndom f) ≫
        (M.reindex x sg T k' Y).cell f := by
  ext d
  have hi : ∀ t : sg.CTrm (sg.fnty f), ConjEq (((M.homModel x').interpCell
      (M.reindexEnvHom x sg α Y.env) t).toNatTrans.app d)
      (M.interpCell ((M.evalAlgAt x sg T Y d).whiskerHom α).app t) := fun t =>
    M.homInterpCell_app x' _ d t
  exact (ConjEq.eq_iff
    (ConjEq.comp (M.reindexCell_app x sg T k Y f d) (hi _))
    (ConjEq.comp (hi _) (M.reindexCell_app x sg T k' Y f d))).mpr
    (((M.evalAlgAt x sg T Y d).whiskerHom α).comm f)

/-- **Reindexing along a 2-cell** `α : k ⇒ k'`: the 2-cell of `T`-algebras of `K(x', M)` from
the reindexing of `Y` along `k` to the one along `k'`. At `d`, it is `α` whiskered with the
evaluation of `Y` at `d` (`Model.Alg.whiskerHom`). -/
def reindexHom (Y : (M.homModel x).Alg sg T D) :
    Alg.Hom (M.reindex x sg T k Y) (M.reindex x sg T k' Y) where
  app := M.reindexEnvHom x sg α Y.env
  comm f := M.reindexHom_comm x sg T α Y f

end Reindex₂

section Natural

variable [HasChosenProductsOfSize.{s₁} Cat.{w, v}] [HasChosenProductsOfSize.{s₂} Cat.{w, v}]
  [HasChosenInserters Cat.{w, v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{w, v}] [HasChosenEquifiers Cat.{w, v}]

/-- **The functor `K(k, M)^T : K(x, M)^T ⥤ K(x', M)^T`** of precomposition with `k : x' → x`: on
`T`-algebras of `M`, `B ↦ B.precomp k`. -/
def homThyMap {x' : Obj} (k : x' ⟶ x) :
    (M.homModel x).thyObj sg T ⟶ (M.homModel x').thyObj sg T :=
  (M.homModel x').algLift sg T ((M.homModel x').P0 sg) ((M.homModel x').Pfn sg)
    ((M.homModel x').sigIns sg) ((M.homModel x').Peq sg T) ((M.homModel x').thyEquifOf sg T)
    (M.reindex x sg T k (M.homCanon x sg T))

/-- **The comparison functors are natural in `x`**: precomposition with `k : x' → x` on `K(x, E)`
corresponds to `K(k, M)^T` on `K(x, M)^T`. -/
theorem algComparison_natural {E : Obj} (A : M.Alg sg T E) {x' : Obj} (k : x' ⟶ x) :
    (precomp k E).toCatHom ≫ M.algComparison x' sg T A =
      M.algComparison x sg T A ≫ M.homThyMap x sg T k := by
  refine ((M.homCanon_isUniversal x' sg T (Cat.of (x ⟶ E))).1
    ((M.evalAlg x' sg T A).precomp (precomp k E).toCatHom)).unique ?_ ?_
  · rw [← Alg.precomp_precomp, homCanon_precomp_algComparison]
  · exact (Alg.precomp_precomp _ _ _).symm.trans
      (congr(($((M.homModel x').canonAlg_precomp_algLift sg T _ _ _ _ _ _)).precomp
          (M.algComparison x sg T A)).trans
        ((M.reindex_precomp x sg T k _ _).symm.trans
          (congr(M.reindex x sg T k $(M.homCanon_precomp_algComparison x sg T A)).trans
            (M.evalAlg_reindex x sg T k A))))


/-- Precomposing the canonical algebra over `K(x', M)^T` with `K(k, M)^T` gives the reindexing along
`k` of the canonical algebra over `K(x, M)^T`. -/
lemma homCanon_precomp_homThyMap {x' : Obj} (k : x' ⟶ x) :
    (M.homCanon x' sg T).precomp (M.homThyMap x sg T k) = M.reindex x sg T k (M.homCanon x sg T) :=
  (M.homModel x').canonAlg_precomp_algLift sg T _ _ _ _ _ _

/-- **The 2-cell `K(α, M)^T : K(k, M)^T ⇒ K(k', M)^T`** of a 2-cell `α : k ⇒ k'` between
`k, k' : x' → x`: the unique 2-cell whose whiskering with the canonical algebra of `K(x', M)^T` is
the reindexing along `α` (`Model.reindexHom`), by the two-dimensional universal property of
`K(x', M)^T`. On an object `B` of `K(x, M)^T`, it is `α` whiskered with `B`. -/
noncomputable def homThyMap₂ {x' : Obj} {k k' : x' ⟶ x} (α : k ⟶ k') :
    M.homThyMap x sg T k ⟶ M.homThyMap x sg T k' :=
  ((M.homCanon_isUniversal x' sg T ((M.homModel x).thyObj sg T)).2 _ _
    (Alg.Hom.transport sg T (M.homCanon_precomp_homThyMap x sg T k).symm
      (M.homCanon_precomp_homThyMap x sg T k').symm
      (M.reindexHom x sg T α (M.homCanon x sg T)))).exists.choose

/-- Whiskering `K(α, M)^T` with the canonical algebra of `K(x', M)^T` gives the reindexing of the
canonical algebra along `α`, transported along `homCanon_precomp_homThyMap`. -/
lemma homThyMap₂_whiskerRight {x' : Obj} {k k' : x' ⟶ x} (α : k ⟶ k') (s : sg.Srt) :
    M.homThyMap₂ x sg T α ▷ (M.homCanon x' sg T).env s =
      (Alg.Hom.transport sg T (M.homCanon_precomp_homThyMap x sg T k).symm
        (M.homCanon_precomp_homThyMap x sg T k').symm
        (M.reindexHom x sg T α (M.homCanon x sg T))).app s :=
  ((M.homCanon_isUniversal x' sg T ((M.homModel x).thyObj sg T)).2 _ _ _).exists.choose_spec s

/-- On an object `y` of `K(x, M)^T`, `K(α, M)^T` is `α` whiskered with the algebra `y`. -/
lemma homPsiHom_homThyMap₂ {x' : Obj} {k k' : x' ⟶ x} (α : k ⟶ k')
    (y : (M.homModel x).thyObj sg T) (s : sg.Srt) :
    ConjEq ((M.homPsiHom x' sg T ((M.homThyMap₂ x sg T α).toNatTrans.app y)).app s)
      (α ▷ (M.homPsi x sg T y).env s) := by
  have h := ConjEq.app (ConjEq.of_eq (M.homThyMap₂_whiskerRight x sg T α s)) y
  rw [Cat.whiskerRight_app] at h
  exact h.trans (ConjEq.app (Alg.Hom.transport_app sg T _ _ _ s) y)


/-- Two morphisms of `K(x, M)^T` whose 2-cells of `T`-algebras have `ConjEq` components are
`ConjEq`. -/
lemma conjEq_of_homPsiHom {y₁ y₂ y₁' y₂' : (M.homModel x).thyObj sg T} (u : y₁ ⟶ y₂)
    (v : y₁' ⟶ y₂') (p : y₁ = y₁') (q : y₂ = y₂')
    (h : ∀ s, ConjEq ((M.homPsiHom x sg T u).app s) ((M.homPsiHom x sg T v).app s)) :
    ConjEq u v := by
  subst p q
  exact ConjEq.of_eq ((M.homPsiHom_bijective x sg T _ _).1
    (Alg.Hom.ext (funext fun s => (h s).eq)))

/-- **The comparison functors are 2-natural in `x`**: for `α : k ⇒ k'` between `k, k' : x' → x`
and `a : x → E`, the comparison at `x'` sends `α ▷ a` to the component of `K(α, M)^T` at the
image of `a`. -/
theorem algComparison_natural₂ {E : Obj} (A : M.Alg sg T E) {x' : Obj} {k k' : x' ⟶ x}
    (α : k ⟶ k') (a : x ⟶ E) :
    ConjEq ((M.algComparison x' sg T A).toFunctor.map (α ▷ a))
      ((M.homThyMap₂ x sg T α).toNatTrans.app ((M.algComparison x sg T A).toFunctor.obj a)) := by
  refine M.conjEq_of_homPsiHom x' sg T _ _
    (Functor.congr_obj (Cat.Hom.ext_iff.mp (M.algComparison_natural x sg T A k)) a)
    (Functor.congr_obj (Cat.Hom.ext_iff.mp (M.algComparison_natural x sg T A k')) a) fun s => ?_
  refine (M.homPsiHom_algComparison x' sg T A (α ▷ a) s).trans ?_
  refine (ConjEq.whiskerRight_comp₁ α a (A.env s)).symm.trans ?_
  refine (ConjEq.whiskerRight_congr' α ?_).trans (M.homPsiHom_homThyMap₂ x sg T α _ s).symm
  exact congr(($(M.homPsi_algComparison x sg T A a)).env s).symm

end Natural

end Model

end UlmerBialgebras
