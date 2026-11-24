module

public import UlmerBialgebras.Syntax.CoTheory

/-!
# The object of bialgebras in `K^co`

The object `M^T` of `T`-bialgebras of a model `M` in `K` is the object of `T^co`-bialgebras of
the dual model `M^co` in `K^co` (`UlmerBialgebras.Model.thyObj_co`). The objects of operations agree
because the inserter of `(f, g)` in `K^co` is the inserter of `(g, f)` in `K` and `σ^co` swaps
the domain and codomain of each function symbol; the equifiers agree because both paths of each
equation are reversed (`UlmerBialgebras.Model.pathCell_co`).

## Main results

* `UlmerBialgebras.Model.sigObj_co`: the object of operations of `M^co` is `M^σ`.
* `UlmerBialgebras.Model.thyObj_co`: the object `(M^co)^{T^co}` in `K^co` is `M^T`.
* `UlmerBialgebras.Model.e_co_heq`: the equifier 1-cell of the dual is `e : M^T → M^σ`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 3.14
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory
open scoped Bicategory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  [HasChosenInserters.{u, v, w} Obj] {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- Lifting a family of term interpretations in `M^co` to `M.Peq sg T`. -/
lemma peq_lift_co (ts : ∀ r : T.Eqn, sg.CTrm (T.eqty r)) :
    (M.Peq sg T).lift (fun r => M.co.sigTm sg.co (ts r)) =
      eqToHom (M.sigObj_co sg) ≫ (M.Peq sg T).lift (fun r => M.sigTm sg (ts r)) := by
  refine Eq.trans ?_ ((M.Peq sg T).lift_uniq
    (eqToHom (M.sigObj_co sg) ≫ (M.Peq sg T).lift fun r => M.sigTm sg (ts r)))
  congr 1; funext r
  rw [Bicategory.Strict.assoc, Product.lift_π]
  exact M.sigTm_co sg (ts r)

private lemma peq_cell_co
    (p : ∀ r : T.Eqn, sg.Path (T.dom r) (T.cod r)) :
    (M.Peq sg T).lift₂ (fun r =>
        eqToHom (Product.lift_π (M.Peq sg T) (fun r => M.co.sigTm sg.co (T.dom r)) r) ≫
          Co.uncell (M.co.pathCell sg.co (p r).co) ≫
          eqToHom (Product.lift_π (M.Peq sg T) (fun r => M.co.sigTm sg.co (T.cod r)) r).symm) =
      eqToHom (M.peq_lift_co sg T T.dom) ≫
        (eqToHom (M.sigObj_co sg) ◁ (M.Peq sg T).lift₂ (fun r =>
          eqToHom (Product.lift_π (M.Peq sg T) (fun r => M.sigTm sg (T.dom r)) r) ≫
            M.pathCell sg (p r) ≫
            eqToHom (Product.lift_π (M.Peq sg T) (fun r => M.sigTm sg (T.cod r)) r).symm)) ≫
        eqToHom (M.peq_lift_co sg T T.cod).symm := by
  apply (M.Peq sg T).cell_ext
  intro r
  rw [(M.Peq sg T).lift₂_π, Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight]
  have hwa : ∀ {a b c d : Obj} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) (k : c ⟶ d),
      (f ◁ η) ▷ k = eqToHom (Bicategory.Strict.assoc f g k) ≫ (f ◁ (η ▷ k)) ≫
        eqToHom (Bicategory.Strict.assoc f h k).symm := by
    intro a b c d f g h η k
    rw [Bicategory.Strict.whisker_assoc]
    simp [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl]
  rw [hwa, (M.Peq sg T).lift₂_π]
  simp only [Bicategory.whiskerLeft_comp, Category.assoc]
  rw [M.pathCell_co sg (p r)]
  simp [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight]

/-- The 2-cell given by the left-hand sides of the equations of `T^co` in `M^co` is that of `T`
in `M`, up to `peq_lift_co` and `sigObj_co`. -/
lemma lhsCell_co :
    Co.uncell (M.co.lhsCell sg.co T.co) =
      eqToHom (M.peq_lift_co sg T T.dom) ≫ (eqToHom (M.sigObj_co sg) ◁ M.lhsCell sg T) ≫
        eqToHom (M.peq_lift_co sg T T.cod).symm := by
  dsimp only [Co.uncell, lhsCell, Theory.co]
  simp only [Co.comp_eq, Co.eqToHom_eq]
  simp only [Category.assoc]
  exact M.peq_cell_co sg T T.lhs

/-- The 2-cell given by the right-hand sides of the equations of `T^co` in `M^co` is that of `T`
in `M`, up to `peq_lift_co` and `sigObj_co`. -/
lemma rhsCell_co :
    Co.uncell (M.co.rhsCell sg.co T.co) =
      eqToHom (M.peq_lift_co sg T T.dom) ≫ (eqToHom (M.sigObj_co sg) ◁ M.rhsCell sg T) ≫
        eqToHom (M.peq_lift_co sg T T.cod).symm := by
  dsimp only [Co.uncell, rhsCell, Theory.co]
  simp only [Co.comp_eq, Co.eqToHom_eq]
  simp only [Category.assoc]
  exact M.peq_cell_co sg T T.rhs

/-- The 2-cell given by the left-hand sides of the equations of `T^co` in `M^co` is
heterogeneously equal to that of `T` in `M`. -/
lemma lhsCell_co_heq : HEq (M.co.lhsCell sg.co T.co) (M.lhsCell sg T) :=
  Co.cell_heq_of_eqToHom_whiskerLeft (M.sigObj_co sg) (M.peq_lift_co sg T T.dom)
    (M.peq_lift_co sg T T.cod) (M.lhsCell_co sg T)

/-- The 2-cell given by the right-hand sides of the equations of `T^co` in `M^co` is
heterogeneously equal to that of `T` in `M`. -/
lemma rhsCell_co_heq : HEq (M.co.rhsCell sg.co T.co) (M.rhsCell sg T) :=
  Co.cell_heq_of_eqToHom_whiskerLeft (M.sigObj_co sg) (M.peq_lift_co sg T T.dom)
    (M.peq_lift_co sg T T.cod) (M.rhsCell_co sg T)

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- **Duality for objects of bialgebras**: `(M^co)^{T^co}` in `K^co` is `M^T` in `K`. -/
lemma thyObj_co : Co.unop (M.co.thyObj sg.co T.co) = M.thyObj sg T :=
  Co.equif_pt_eq_of_heq (M.sigObj_co sg)
    (Co.hom_heq_of_eqToHom_comp (M.sigObj_co sg) (M.peq_lift_co sg T T.dom))
    (Co.hom_heq_of_eqToHom_comp (M.sigObj_co sg) (M.peq_lift_co sg T T.cod))
    (M.lhsCell_co_heq sg T) (M.rhsCell_co_heq sg T)

/-- The equifier 1-cell `e : (M^co)^{T^co} → (M^co)^{σ^co}` of the dual is `e : M^T → M^σ`. -/
lemma e_co_heq : HEq (M.co.e sg.co T.co) (M.e sg T) :=
  Co.equif_e_heq_of_heq (M.sigObj_co sg)
    (Co.hom_heq_of_eqToHom_comp (M.sigObj_co sg) (M.peq_lift_co sg T T.dom))
    (Co.hom_heq_of_eqToHom_comp (M.sigObj_co sg) (M.peq_lift_co sg T T.cod))
    (M.lhsCell_co_heq sg T) (M.rhsCell_co_heq sg T)

end Model

omit [HasChosenFinProducts.{u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]
  in
omit [Bicategory.Strict Obj] in
/-- A 1-cell `G` with `G q = p F₀` transports along equalities of its endpoints, given the
corresponding (heterogeneous) equalities of `p`, `q` and `F₀`. -/
lemma exists_comm_of_heq {a a' b b' x x' y y' : Obj} (ha : a = a') (hb : b = b') (hx : x = x')
    (hy : y = y') (G : a ⟶ b) {p : a ⟶ x} {p' : a' ⟶ x'} {q : b ⟶ y} {q' : b' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') {F₀ : x ⟶ y} {F₀' : x' ⟶ y'} (hF : HEq F₀ F₀')
    (h : G ≫ q = p ≫ F₀) : ∃ G' : a' ⟶ b', G' ≫ q' = p' ≫ F₀' := by
  subst ha hb hx hy
  cases eq_of_heq hp; cases eq_of_heq hq; cases eq_of_heq hF
  exact ⟨G, h⟩

end UlmerBialgebras
