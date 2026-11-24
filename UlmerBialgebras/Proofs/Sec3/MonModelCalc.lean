module

public import UlmerBialgebras.Paper.Sec3DefsMonModel
public import UlmerBialgebras.Models.CatCells
public import UlmerBialgebras.Models.CatSigObj
public import UlmerBialgebras.Kan.KanModel
public import UlmerBialgebras.Examples.MonEquiv
public import UlmerBialgebras.Proofs.Sec3.CategoryIso

/-!
# Examples 3.20 (1): monoids in an arbitrary `Σ_Mon`-model in `CAT`

For an arbitrary `Σ_Mon`-model `M` in `CAT` (`UlmerBialgebras.MonEx.twoSig`), with the notation of
`UlmerBialgebras/Paper/Sec3DefsMonModel.lean`, this file evaluates the arrows of the term graph that
occur in the
theory of monoids `T_Mon` (`UlmerBialgebras.MonEx.monTheory`) at an object `z = (x, m, e)` of `M^σ`:

* `µ`, `u` evaluate to `m`, `e`;
* `µ□s`, `s□µ`, `s□u`, `u□s` evaluate to `m ⊗ x`, `x ⊗ m`, `x ⊗ e`, `e ⊗ x`;
* `α_{s,s,s}`, `ρ_s`, `λ_s` evaluate to `M(α)_{x,x,x}`, `M(ρ)_x`, `M(λ)_x`.

The interpreted objects (such as `M(s□s)(x)`) and the readable ones (such as `x ⊗ x`) are equal
but not definitionally equal, so these evaluations are stated as heterogeneous equalities. The
defining condition of `M^T` at `z` is then the conjunction of the associativity and unit laws
(`UlmerBialgebras.Paper.MonModel.mem_thy_iff`). This generalises `UlmerBialgebras.MonEx.mem_thy_iff`
(`UlmerBialgebras/Examples/MonCalc.lean`), which treats the monoidal model of a monoidal
category.

It also shows that `M^σ` is the category of pointed magmas of `M`: its objects are the triples
`(x, m, e)` (`UlmerBialgebras.Paper.MonModel.sigObj_bijective`) and its morphisms are the morphisms
`g : x ⟶ x'` of `M_c` compatible with the multiplications and the units
(`UlmerBialgebras.Paper.MonModel.exists_hom_iff`).

The last section shows that the comparison functor `M^{T_Mon} ⥤ Mon C` of the monoidal model of a
monoidal category `C` (`UlmerBialgebras/Examples/MonEquiv.lean`) is an isomorphism of
categories over `C`.

## Main results

* `UlmerBialgebras.Paper.MonModel.sigObj_bijective`: the objects of `M^σ` correspond bijectively to
  the pointed magmas `(x, m, e)` of `M`.
* `UlmerBialgebras.Paper.MonModel.exists_hom_iff`: a morphism `g : x ⟶ x'` underlies a morphism of
  `M^σ` iff it is compatible with the multiplications and units.
* `UlmerBialgebras.Paper.MonModel.mem_thy_iff`: an object of `M^σ` lies in `M^{T_Mon}` iff it
  satisfies associativity and the two unit laws (Examples 3.20 (1)).
* `UlmerBialgebras.MonEx.comparison_comp_inverseFunctor`: `comparison C ⋙ inverseFunctor C = 𝟭 _`.
* `UlmerBialgebras.MonEx.comparison_comp_forget`: the comparison functor commutes with the forgetful
  functors to `C`.

## References

* *A Syntactic Approach to Ulmer's Bialgebras*, Examples 3.20 (1).
-/

@[expose] public section

universe u v

namespace UlmerBialgebras.Paper.MonModel

open CategoryTheory UlmerBialgebras.MonEx

/-! ## Heterogeneous equalities -/

/-- A functor sends heterogeneously equal morphisms to heterogeneously equal morphisms. -/
lemma heq_map {A B : Type*} [Category A] [Category B] (F : A ⥤ B) {a b a' b' : A}
    (ha : a = a') (hb : b = b') {φ : a ⟶ b} {ψ : a' ⟶ b'} (h : HEq φ ψ) :
    HEq (F.map φ) (F.map ψ) := by
  subst ha hb
  cases h
  rfl

/-- Morphisms of a product category in `CAT` are heterogeneously equal when their components
are. -/
lemma prod_hom_heq {ι : Type} {c : ι → Cat.{v, max u v}}
    {p q p' q' : ((HasChosenProductsOfSize.prod c).pt : Type (max u v))} (hp : p = p') (hq : q = q')
    {φ : p ⟶ q}
    {ψ : p' ⟶ q'} (h : ∀ i, HEq (φ i) (ψ i)) : HEq φ ψ := by
  subst hp hq
  exact heq_of_eq (funext fun i => eq_of_heq (h i))

/-- Two equations between heterogeneously equal terms are equivalent. -/
lemma eq_iff_of_heq {α β : Sort v} {a b : α} {a' b' : β} (ha : HEq a a') (hb : HEq b b') :
    a = b ↔ a' = b' :=
  ⟨fun h => eq_of_heq (ha.symm.trans ((heq_of_eq h).trans hb)),
    fun h => eq_of_heq (ha.trans ((heq_of_eq h).trans hb.symm))⟩

/-- Two mutually inverse `eqToHom`s cancel. -/
lemma eqToHom_eqToHom_comp {D : Type*} [Category D] {X Y W : D} (h₁ : X = Y) (h₂ : Y = X)
    (f : X ⟶ W) : eqToHom h₁ ≫ eqToHom h₂ ≫ f = f := by
  simp

/-- A component of a natural transformation at `p` is, up to `eqToHom`s, its component at any
`q = p`. -/
lemma app_heq_eqToHom_comp_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {p q : C} (h : p = q) {X Y : D} (h₁ : X = F.obj q) (h₂ : G.obj q = Y) :
    HEq (α.app p) (eqToHom h₁ ≫ α.app q ≫ eqToHom h₂) := by
  subst h h₁ h₂
  simp

/-- The variant of `app_heq_eqToHom_comp_app` with one `eqToHom` on each side. -/
lemma app_comp_eqToHom_heq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {p q : C} (h : p = q) {X Y : D} (h₁ : G.obj p = Y) (h₂ : X = F.obj q) :
    HEq (α.app p ≫ eqToHom h₁) (eqToHom h₂ ≫ α.app q) := by
  subst h h₁ h₂
  simp

/-- A component of a 2-cell of `CAT`, transported along an equality of hom-types induced by
equalities of its source and target, is heterogeneously equal to the original component. -/
lemma cast_app_heq {A B : Cat.{v, max u v}} {F G F' G' : A ⟶ B} (hF : F = F') (hG : G = G')
    (h : (F ⟶ G) = (F' ⟶ G')) (η : F ⟶ G) (z : A) :
    HEq ((cast h η).toNatTrans.app z) (η.toNatTrans.app z) := by
  subst hF hG
  rfl

/-- An `eqToHom` is heterogeneously equal to the identity of its source. -/
lemma eqToHom_heq_id' {D : Type*} [Category D] {X Y : D} (h : X = Y) : HEq (eqToHom h) (𝟙 X) := by
  subst h
  rfl

variable {M : Model MonEx.twoSig Cat.{v, max u v}}

/-! ## `M^σ` is the category of pointed magmas -/

/-- The term `a □ b` at a point `p` of `M₀` is `a(p) ⊗ b(p)`. -/
lemma tm_obj_tens (p : ((M.P0 oneSig).pt : Type (max u v))) (a b : oneSig.CTrm ()) :
    (M.tm oneSig (tens a b)).toFunctor.obj p = tensObj ((M.tm oneSig a).toFunctor.obj p) ((M.tm
        oneSig b).toFunctor.obj p) :=
  congrArg (M.fn FunSym.tens).toFunctor.obj (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))

/-- The term `I` at a point of `M₀` is the unit object `I`. -/
lemma tm_obj_unitT (p : ((M.P0 oneSig).pt : Type (max u v))) :
    (M.tm oneSig unitT).toFunctor.obj p = unitObj M :=
  congr((M.fn FunSym.unit).toFunctor.obj $(funext fun i => i.elim0))

/-- The functor `M(s□s) : M₀ → M_c` on morphisms: `b ↦ b ⊗ b`. -/
lemma tm_map_tensSS_heq {p p' : ((M.P0 oneSig).pt : Type (max u v))} (b : p ⟶ p') :
    HEq ((M.tm oneSig (tens sTm sTm)).toFunctor.map b) (tensHom (M := M) (b ()) (b ())) := by
  rw [Model.tm_app]
  simp only [Cat.Hom.comp_map, tensHom]
  apply heq_map
  · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  · apply prod_hom_heq
    · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    · intro i
      fin_cases i
      · rfl
      · rfl

/-- The functor `M(I) : M₀ → M_c` on morphisms: `b ↦ 𝟙 I`. -/
lemma tm_map_unitT_heq {p p' : ((M.P0 oneSig).pt : Type (max u v))} (b : p ⟶ p') :
    HEq ((M.tm oneSig unitT).toFunctor.map b) (𝟙 (unitObj M)) := by
  rw [Model.tm_app, show 𝟙 (unitObj M) = (M.fn FunSym.unit).toFunctor.map (𝟙 finZeroElim) from
    ((M.fn FunSym.unit).toFunctor.map_id _).symm]
  simp only [Cat.Hom.comp_map]
  apply heq_map
  · funext i; exact i.elim0
  · funext i; exact i.elim0
  · apply prod_hom_heq
    · funext i; exact i.elim0
    · funext i; exact i.elim0
    · intro i; exact i.elim0

/-- The pointed magma `(x, m, e)` of `M`, as an object of `M^σ`. -/
def ofMagma (x : (M.obj () : Type (max u v))) (m : tensObj x x ⟶ x) (e : unitObj M ⟶ x) :
    (M.sigObj oneSig : Type (max u v)) where
  pt := fun _ => x
  cell := fun f => match f with
    | .mul => eqToHom (tm_obj_tens (fun _ => x) sTm sTm) ≫ m
    | .one => eqToHom (tm_obj_unitT (fun _ => x)) ≫ e

/-- The multiplication of the object `(x, m, e)` of `M^σ` is `m`. -/
lemma mul_ofMagma (x : (M.obj () : Type (max u v))) (m : tensObj x x ⟶ x) (e : unitObj M ⟶ x) :
    mul (ofMagma x m e) = m :=
  eqToHom_eqToHom_comp _ _ _

/-- The unit of the object `(x, m, e)` of `M^σ` is `e`. -/
lemma one_ofMagma (x : (M.obj () : Type (max u v))) (m : tensObj x x ⟶ x) (e : unitObj M ⟶ x) :
    one (ofMagma x m e) = e :=
  eqToHom_eqToHom_comp _ _ _

/-- Every object of `M^σ` is the pointed magma of its parts. -/
lemma ofMagma_ob_mul_one (z : (M.sigObj oneSig : Type (max u v))) :
    ofMagma (ob z) (mul z) (one z) = z := by
  obtain ⟨pt, cell⟩ := z
  change Ins.mk pt _ = Ins.mk pt cell
  congr 1
  funext f
  cases f
  · exact eqToHom_eqToHom_comp _ _ _
  · exact eqToHom_eqToHom_comp _ _ _

/-- The objects of `M^σ` are the pointed magmas `(x, m, e)` of `M`. -/
theorem sigObj_bijective :
    Function.Bijective (fun z : (M.sigObj oneSig : Type (max u v)) =>
      (⟨ob z, mul z, one z⟩ :
        Σ x : (M.obj () : Type (max u v)), (tensObj x x ⟶ x) × (unitObj M ⟶ x))) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun t => ofMagma t.1 t.2.1 t.2.2, ?_, ?_⟩
  · intro z
    exact ofMagma_ob_mul_one z
  · rintro ⟨x, m, e⟩
    exact Sigma.ext rfl (heq_of_eq (Prod.ext (mul_ofMagma x m e) (one_ofMagma x m e)))

/-- The structure morphism of `z` at `µ` is the multiplication of `z`, up to `eqToHom`. -/
lemma cell_mul_heq (z : (M.sigObj oneSig : Type (max u v))) : HEq (Ins.cell z FnSym.mul) (mul z) :=
  (eqToHom_comp_heq _ _).symm

/-- The structure morphism of `z` at `u` is the unit of `z`, up to `eqToHom`. -/
lemma cell_one_heq (z : (M.sigObj oneSig : Type (max u v))) : HEq (Ins.cell z FnSym.one) (one z) :=
  (eqToHom_comp_heq _ _).symm

/-- The compatibility of a morphism of `M^σ` with the multiplications. -/
lemma w_mul_iff {z z' : (M.sigObj oneSig : Type (max u v))} (b : Ins.pt z ⟶ Ins.pt z') :
    Ins.cell z FnSym.mul ≫ (M.codCell oneSig).toFunctor.map b FnSym.mul =
        (M.domCell oneSig).toFunctor.map b FnSym.mul ≫ Ins.cell z' FnSym.mul ↔
      mul z ≫ b () = tensHom (b ()) (b ()) ≫ mul z' :=
  eq_iff_of_heq (heq_comp (tm_obj_tens (Ins.pt z) sTm sTm) rfl rfl (cell_mul_heq z) HEq.rfl)
    (heq_comp (tm_obj_tens (Ins.pt z) sTm sTm) (tm_obj_tens (Ins.pt z') sTm sTm) rfl
      (tm_map_tensSS_heq b) (cell_mul_heq z'))

/-- The compatibility of a morphism of `M^σ` with the units. -/
lemma w_one_iff {z z' : (M.sigObj oneSig : Type (max u v))} (b : Ins.pt z ⟶ Ins.pt z') :
    Ins.cell z FnSym.one ≫ (M.codCell oneSig).toFunctor.map b FnSym.one =
        (M.domCell oneSig).toFunctor.map b FnSym.one ≫ Ins.cell z' FnSym.one ↔
      one z ≫ b () = one z' :=
  (eq_iff_of_heq (heq_comp (tm_obj_unitT (Ins.pt z)) rfl rfl (cell_one_heq z) HEq.rfl)
    (heq_comp (tm_obj_unitT (Ins.pt z)) (tm_obj_unitT (Ins.pt z')) rfl (tm_map_unitT_heq b)
      (cell_one_heq z'))).trans
    ⟨fun h => h.trans (Category.id_comp _), fun h => h.trans (Category.id_comp _).symm⟩

/-- A morphism of `M^σ` is determined by its underlying morphism. -/
lemma hom_base_injective (z z' : (M.sigObj oneSig : Type (max u v))) :
    Function.Injective (fun f : z ⟶ z' => Ins.Hom.base f ()) := by
  intro f g h
  apply Ins.hom_ext
  funext s
  cases s
  exact h

/-- The morphisms of `M^σ` are the morphisms of pointed magmas. -/
lemma exists_hom_iff {z z' : (M.sigObj oneSig : Type (max u v))} (g : ob z ⟶ ob z') :
    (∃ f : z ⟶ z', Ins.Hom.base f () = g) ↔
      mul z ≫ g = tensHom g g ≫ mul z' ∧ one z ≫ g = one z' := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨(w_mul_iff f.base).1 (congr($(f.w) FnSym.mul)),
      (w_one_iff f.base).1 (congr($(f.w) FnSym.one))⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨fun _ => g, ?_⟩, rfl⟩
    funext fn
    cases fn
    · exact (w_mul_iff (z := z) (z' := z') (fun _ => g)).2 h₁
    · exact (w_one_iff (z := z) (z' := z') (fun _ => g)).2 h₂

variable (z : (M.sigObj MonEx.oneSig : Type (max u v)))

/-! ## The interpreted closed terms -/

/-- The term `a □ b`, interpreted on `M^σ`, at `z` is `a(z) ⊗ b(z)`. -/
lemma sigTm_obj_tens (a b : oneSig.CTrm ()) :
    (M.sigTm oneSig (tens a b)).toFunctor.obj z =
      tensObj ((M.sigTm oneSig a).toFunctor.obj z) ((M.sigTm oneSig b).toFunctor.obj z) :=
  congrArg (M.fn FunSym.tens).toFunctor.obj (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))

/-- The term `I`, interpreted on `M^σ`, at `z` is the unit object `I`. -/
lemma sigTm_obj_unitT : (M.sigTm oneSig unitT).toFunctor.obj z = unitObj M :=
  congr((M.fn FunSym.unit).toFunctor.obj $(funext fun i => i.elim0))

/-- The term `s □ s` at `z = (x, m, e)` is `x ⊗ x`. -/
lemma sigTm_obj_tensSS : (M.sigTm oneSig (tens sTm sTm)).toFunctor.obj z = tensObj (ob z) (ob z) :=
  sigTm_obj_tens z _ _

/-- The term `(s □ s) □ s` at `z = (x, m, e)` is `(x ⊗ x) ⊗ x`. -/
lemma sigTm_obj_tensSS_S :
    (M.sigTm oneSig (tens (tens sTm sTm) sTm)).toFunctor.obj z = tensObj (tensObj (ob z) (ob z))
        (ob z) :=
  (sigTm_obj_tens z _ _).trans (congr(tensObj $(sigTm_obj_tensSS z) (ob z)))

/-- The term `s □ (s □ s)` at `z = (x, m, e)` is `x ⊗ (x ⊗ x)`. -/
lemma sigTm_obj_tensS_SS :
    (M.sigTm oneSig (tens sTm (tens sTm sTm))).toFunctor.obj z = tensObj (ob z) (tensObj (ob z) (ob
        z)) :=
  (sigTm_obj_tens z _ _).trans (congr(tensObj (ob z) $(sigTm_obj_tensSS z)))

/-- The term `s □ I` at `z = (x, m, e)` is `x ⊗ I`. -/
lemma sigTm_obj_tensSI :
    (M.sigTm oneSig (tens sTm unitT)).toFunctor.obj z = tensObj (ob z) (unitObj M) :=
  (sigTm_obj_tens z _ _).trans (congr(tensObj (ob z) $(sigTm_obj_unitT z)))

/-- The term `I □ s` at `z = (x, m, e)` is `I ⊗ x`. -/
lemma sigTm_obj_tensIS :
    (M.sigTm oneSig (tens unitT sTm)).toFunctor.obj z = tensObj (unitObj M) (ob z) :=
  (sigTm_obj_tens z _ _).trans (congr(tensObj $(sigTm_obj_unitT z) (ob z)))

/-! ## The arrows of the term graph -/

/-- The arrow `µ` evaluates to `m`. -/
lemma arrCell_fn_mul_heq :
    HEq ((M.arrCell oneSig (OneSig.Arr.fn (sg := oneSig) FnSym.mul)).toNatTrans.app z) (mul z) := by
  rw [Model.arrCell_fn]
  simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app, Model.cat_sigIns_φ_app,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact (eqToHom_comp_heq _ _).symm

/-- The arrow `u` evaluates to `e`. -/
lemma arrCell_fn_one_heq :
    HEq ((M.arrCell oneSig (OneSig.Arr.fn (sg := oneSig) FnSym.one)).toNatTrans.app z) (one z) := by
  rw [Model.arrCell_fn]
  simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app, Model.cat_sigIns_φ_app,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact (eqToHom_comp_heq _ _).symm

/-- The arrow `µ □ s` evaluates to `m ⊗ x`. -/
lemma arrCell_mulTensS_heq :
    HEq ((M.arrCell oneSig mulTensS).toNatTrans.app z) (tensHom (mul z) (𝟙 (ob z))) := by
  rw [show M.arrCell oneSig mulTensS = _ from Model.arrCell_app (M := M) (sg := oneSig)
    FunSym.tens 0 ![tens sTm sTm, sTm] ![sTm, sTm] (fun j hj => by fin_cases j <;> simp_all)
    (OneSig.Arr.fn (sg := oneSig) FnSym.mul), PreModel.appCell]
  simp only [Cat.whiskerRight_app, tensHom]
  have h₁ := sigTm_obj_tensSS z
  apply heq_map
  · funext i; fin_cases i
    · exact h₁
    · rfl
  · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  · apply prod_hom_heq
    · funext i; fin_cases i
      · exact h₁
      · rfl
    · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    · intro i
      fin_cases i
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 0)).trans ?_
        simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, dite_true]
        exact (eqToHom_comp_heq_iff _ _ _).2 ((comp_eqToHom_heq_iff _ _ _).2
          ((cast_app_heq rfl rfl _ _ z).trans (arrCell_fn_mul_heq z)))
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 1)).trans ?_
        simp only [Cat.eqToHom_app, Fin.mk_one, Fin.isValue, one_ne_zero, dite_false,
          eqToHom_trans]
        exact eqToHom_heq_id' _

/-- The arrow `s □ µ` evaluates to `x ⊗ m`. -/
lemma arrCell_sTensMul_heq :
    HEq ((M.arrCell oneSig sTensMul).toNatTrans.app z) (tensHom (𝟙 (ob z)) (mul z)) := by
  rw [show M.arrCell oneSig sTensMul = _ from Model.arrCell_app (M := M) (sg := oneSig)
    FunSym.tens 1 ![sTm, tens sTm sTm] ![sTm, sTm] (fun j hj => by fin_cases j <;> simp_all)
    (OneSig.Arr.fn (sg := oneSig) FnSym.mul), PreModel.appCell]
  simp only [Cat.whiskerRight_app, tensHom]
  have h₁ := sigTm_obj_tensSS z
  apply heq_map
  · funext i; fin_cases i
    · rfl
    · exact h₁
  · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  · apply prod_hom_heq
    · funext i; fin_cases i
      · rfl
      · exact h₁
    · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    · intro i
      fin_cases i
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 0)).trans ?_
        simp only [Cat.eqToHom_app, Fin.isValue, zero_ne_one, dite_false,
          eqToHom_trans]
        exact eqToHom_heq_id' _
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 1)).trans ?_
        simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, Fin.mk_one, Fin.isValue, dite_true]
        exact (eqToHom_comp_heq_iff _ _ _).2 ((comp_eqToHom_heq_iff _ _ _).2
          ((cast_app_heq rfl rfl _ _ z).trans (arrCell_fn_mul_heq z)))

/-- The arrow `s □ u` evaluates to `x ⊗ e`. -/
lemma arrCell_sTensOne_heq :
    HEq ((M.arrCell oneSig sTensOne).toNatTrans.app z) (tensHom (𝟙 (ob z)) (one z)) := by
  rw [show M.arrCell oneSig sTensOne = _ from Model.arrCell_app (M := M) (sg := oneSig)
    FunSym.tens 1 ![sTm, unitT] ![sTm, sTm] (fun j hj => by fin_cases j <;> simp_all)
    (OneSig.Arr.fn (sg := oneSig) FnSym.one), PreModel.appCell]
  simp only [Cat.whiskerRight_app, tensHom]
  have h₁ := sigTm_obj_unitT z
  apply heq_map
  · funext i; fin_cases i
    · rfl
    · exact h₁
  · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  · apply prod_hom_heq
    · funext i; fin_cases i
      · rfl
      · exact h₁
    · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    · intro i
      fin_cases i
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 0)).trans ?_
        simp only [Cat.eqToHom_app, Fin.isValue, zero_ne_one, dite_false,
          eqToHom_trans]
        exact eqToHom_heq_id' _
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 1)).trans ?_
        simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, Fin.mk_one, Fin.isValue, dite_true]
        exact (eqToHom_comp_heq_iff _ _ _).2 ((comp_eqToHom_heq_iff _ _ _).2
          ((cast_app_heq rfl rfl _ _ z).trans (arrCell_fn_one_heq z)))

/-- The arrow `u □ s` evaluates to `e ⊗ x`. -/
lemma arrCell_oneTensS_heq :
    HEq ((M.arrCell oneSig oneTensS).toNatTrans.app z) (tensHom (one z) (𝟙 (ob z))) := by
  rw [show M.arrCell oneSig oneTensS = _ from Model.arrCell_app (M := M) (sg := oneSig)
    FunSym.tens 0 ![unitT, sTm] ![sTm, sTm] (fun j hj => by fin_cases j <;> simp_all)
    (OneSig.Arr.fn (sg := oneSig) FnSym.one), PreModel.appCell]
  simp only [Cat.whiskerRight_app, tensHom]
  have h₁ := sigTm_obj_unitT z
  apply heq_map
  · funext i; fin_cases i
    · exact h₁
    · rfl
  · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
  · apply prod_hom_heq
    · funext i; fin_cases i
      · exact h₁
      · rfl
    · exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    · intro i
      fin_cases i
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 0)).trans ?_
        simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, dite_true]
        exact (eqToHom_comp_heq_iff _ _ _).2 ((comp_eqToHom_heq_iff _ _ _).2
          ((cast_app_heq rfl rfl _ _ z).trans (arrCell_fn_one_heq z)))
      · refine (heq_of_eq (Model.cat_P_lift₂_app _ _ z 1)).trans ?_
        simp only [Cat.eqToHom_app, Fin.mk_one, Fin.isValue, one_ne_zero, dite_false,
          eqToHom_trans]
        exact eqToHom_heq_id' _

/-- The arrow `α_{s,s,s}` evaluates to `M(α)_{x,x,x}`. -/
lemma arrCell_assocArr_heq :
    HEq ((M.arrCell oneSig assocArr).toNatTrans.app z) (assocApp (ob z) (ob z) (ob z)) := by
  rw [assocArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    Functor.whiskerLeft_app, assocApp, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact app_heq_eqToHom_comp_app _ (funext fun i => by fin_cases i <;> rfl) _ _

/-- The arrow `ρ_s` evaluates to `M(ρ)_x`. -/
lemma arrCell_runitArr_heq :
    HEq ((M.arrCell oneSig runitArr).toNatTrans.app z) (runitApp (ob z)) := by
  rw [runitArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Fin.isValue, subst_var, PreModel.interp_app, PreModel.interp_var, eqToHom_naturality,
    eqToHom_refl, Category.id_comp, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp,
    Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans,
    NatTrans.comp_app, Functor.comp_obj, eqToHom_app, cat_finProd_π_obj, cat_finProd_lift_obj,
    Functor.whiskerLeft_app, runitApp, eqToHom_comp_heq_iff]
  refine app_comp_eqToHom_heq (M.tr TrSym.runit).toNatTrans ?_ _ _
  exact funext (Fin.forall_fin_one.2 rfl)

/-- The arrow `λ_s` evaluates to `M(λ)_x`. -/
lemma arrCell_lunitArr_heq :
    HEq ((M.arrCell oneSig lunitArr).toNatTrans.app z) (lunitApp (ob z)) := by
  rw [lunitArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Fin.isValue, subst_var, PreModel.interp_app, PreModel.interp_var, eqToHom_naturality,
    eqToHom_refl, Category.id_comp, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp,
    Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans,
    NatTrans.comp_app, Functor.comp_obj, eqToHom_app, cat_finProd_π_obj, cat_finProd_lift_obj,
    Functor.whiskerLeft_app, lunitApp, eqToHom_comp_heq_iff]
  refine app_comp_eqToHom_heq (M.tr TrSym.lunit).toNatTrans ?_ _ _
  exact funext (Fin.forall_fin_one.2 rfl)

/-! ## The equations of `T_Mon` -/

/-- The left-hand side of an equation of `T_Mon`, evaluated at an object of `M^σ`. -/
lemma lhsCell_app (r : monTheory.Eqn) :
    (M.lhsCell oneSig monTheory).toNatTrans.app z r = (M.pathCell oneSig (monTheory.lhs
        r)).toNatTrans.app z := by
  rw [Model.lhsCell, cat_lift₂_app]
  simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app]
  exact eq_of_heq ((eqToHom_comp_heq_iff _ _ _).2 ((comp_eqToHom_heq_iff _ _ _).2 HEq.rfl))

/-- The right-hand side of an equation of `T_Mon`, evaluated at an object of `M^σ`. -/
lemma rhsCell_app (r : monTheory.Eqn) :
    (M.rhsCell oneSig monTheory).toNatTrans.app z r = (M.pathCell oneSig (monTheory.rhs
        r)).toNatTrans.app z := by
  rw [Model.rhsCell, cat_lift₂_app]
  simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app]
  exact eq_of_heq ((eqToHom_comp_heq_iff _ _ _).2 ((comp_eqToHom_heq_iff _ _ _).2 HEq.rfl))

/-- The associativity equation of `T_Mon` at `z = (x, m, e)`. -/
lemma eqn_assoc_iff :
    (M.pathCell oneSig (monTheory.lhs EqnSym.assoc)).toNatTrans.app z =
        (M.pathCell oneSig (monTheory.rhs EqnSym.assoc)).toNatTrans.app z ↔
      tensHom (mul z) (𝟙 (ob z)) ≫ mul z =
        assocApp (ob z) (ob z) (ob z) ≫ tensHom (𝟙 (ob z)) (mul z) ≫ mul z := by
  apply eq_iff_of_heq
  · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom₂.comp_app,
      Category.comp_id]
    exact heq_comp (sigTm_obj_tensSS_S z) (sigTm_obj_tensSS z) rfl (arrCell_mulTensS_heq z)
      (arrCell_fn_mul_heq z)
  · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom₂.comp_app,
      Category.comp_id]
    exact heq_comp (sigTm_obj_tensSS_S z) (sigTm_obj_tensS_SS z) rfl (arrCell_assocArr_heq z)
      (heq_comp (sigTm_obj_tensS_SS z) (sigTm_obj_tensSS z) rfl (arrCell_sTensMul_heq z)
        (arrCell_fn_mul_heq z))

/-- The right unit equation of `T_Mon` at `z = (x, m, e)`. -/
lemma eqn_mulOne_iff :
    (M.pathCell oneSig (monTheory.lhs EqnSym.mulOne)).toNatTrans.app z =
        (M.pathCell oneSig (monTheory.rhs EqnSym.mulOne)).toNatTrans.app z ↔
      tensHom (𝟙 (ob z)) (one z) ≫ mul z = runitApp (ob z) := by
  apply eq_iff_of_heq
  · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom₂.comp_app,
      Category.comp_id]
    exact heq_comp (sigTm_obj_tensSI z) (sigTm_obj_tensSS z) rfl (arrCell_sTensOne_heq z)
      (arrCell_fn_mul_heq z)
  · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Category.comp_id]
    exact arrCell_runitArr_heq z

/-- The left unit equation of `T_Mon` at `z = (x, m, e)`. -/
lemma eqn_oneMul_iff :
    (M.pathCell oneSig (monTheory.lhs EqnSym.oneMul)).toNatTrans.app z =
        (M.pathCell oneSig (monTheory.rhs EqnSym.oneMul)).toNatTrans.app z ↔
      tensHom (one z) (𝟙 (ob z)) ≫ mul z = lunitApp (ob z) := by
  apply eq_iff_of_heq
  · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom₂.comp_app,
      Category.comp_id]
    exact heq_comp (sigTm_obj_tensIS z) (sigTm_obj_tensSS z) rfl (arrCell_oneTensS_heq z)
      (arrCell_fn_mul_heq z)
  · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Category.comp_id]
    exact arrCell_lunitArr_heq z

/-- An object of `M^σ` lies in `M^T` (the image of the full inclusion `e_M : M^T → M^σ`) exactly
when it equifies the two 2-cells defining `M^T`. -/
lemma exists_e_obj_iff :
    (∃ t : M.thyObj oneSig monTheory, (M.e oneSig monTheory).toFunctor.obj t = z) ↔
      (M.lhsCell oneSig monTheory).toNatTrans.app z = (M.rhsCell oneSig monTheory).toNatTrans.app z
          :=
  ⟨fun ⟨t, ht⟩ => by subst ht; exact t.property, fun h => ⟨⟨z, h⟩, rfl⟩⟩

/-- **The defining condition of `M^T`** for an arbitrary `Σ_Mon`-model `M` in `CAT`: an object
`z = (x, m, e)` of `M^σ` lies in `M^{T_Mon}` exactly when it satisfies the associativity and the
two unit laws. -/
theorem mem_thy_iff :
    (∃ t : M.thyObj oneSig monTheory, (M.e oneSig monTheory).toFunctor.obj t = z) ↔
      (tensHom (mul z) (𝟙 (ob z)) ≫ mul z =
          assocApp (ob z) (ob z) (ob z) ≫ tensHom (𝟙 (ob z)) (mul z) ≫ mul z ∧
        tensHom (𝟙 (ob z)) (one z) ≫ mul z = runitApp (ob z) ∧
        tensHom (one z) (𝟙 (ob z)) ≫ mul z = lunitApp (ob z)) := by
  rw [exists_e_obj_iff, Model.cat_Peq_hom_ext_iff]
  have key : ∀ r : monTheory.Eqn,
      (M.lhsCell oneSig monTheory).toNatTrans.app z r =
          (M.rhsCell oneSig monTheory).toNatTrans.app z r ↔
        (M.pathCell oneSig (monTheory.lhs r)).toNatTrans.app z =
          (M.pathCell oneSig (monTheory.rhs r)).toNatTrans.app z := fun r =>
    ⟨fun h => (lhsCell_app z r).symm.trans (h.trans (rhsCell_app z r)),
      fun h => (lhsCell_app z r).trans (h.trans (rhsCell_app z r).symm)⟩
  constructor
  · intro h
    exact ⟨(eqn_assoc_iff z).1 ((key _).1 (h EqnSym.assoc)),
      (eqn_mulOne_iff z).1 ((key _).1 (h EqnSym.mulOne)),
      (eqn_oneMul_iff z).1 ((key _).1 (h EqnSym.oneMul))⟩
  · rintro ⟨h1, h2, h3⟩ r
    refine (key r).2 ?_
    cases r
    · exact (eqn_assoc_iff z).2 h1
    · exact (eqn_mulOne_iff z).2 h2
    · exact (eqn_oneMul_iff z).2 h3

end UlmerBialgebras.Paper.MonModel

/-! ## The monoidal model: an isomorphism of categories over `C` -/

namespace UlmerBialgebras.MonEx

open CategoryTheory

variable (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C]

/-- The comparison functor is a strict left inverse of `inverseFunctor`. -/
lemma inverseFunctor_comp_comparison : inverseFunctor C ⋙ comparison C = 𝟭 (Mon C) := rfl

variable {C} in
/-- `inverseFunctor` is a strict left inverse of the comparison functor on objects. -/
lemma inverseFunctor_obj_comparison_obj (t : ThyObj C) :
    (inverseFunctor C).obj ((comparison C).obj t) = t := by
  apply ObjectProperty.FullSubcategory.ext
  obtain ⟨⟨pt, cell⟩, h⟩ := t
  change Ins.mk pt _ = Ins.mk pt cell
  congr 1
  funext f
  cases f <;> rfl

/-- `inverseFunctor` is a strict left inverse of the comparison functor. -/
lemma comparison_comp_inverseFunctor : comparison C ⋙ inverseFunctor C = 𝟭 (ThyObj C) :=
  Paper.comp_eq_id_of_faithful _ _ (inverseFunctor_comp_comparison C)
    inverseFunctor_obj_comparison_obj

/-- The comparison functor lies over `C`: it commutes with the forgetful functors to `C`, where
`M^{T_Mon}` lies over `C` through `u_M e_M : M^{T_Mon} → M₀` and the projection `M₀ → C`. -/
lemma comparison_comp_forget :
    comparison C ⋙ Mon.forget C = ((monModel C).thyForget oneSig monTheory).toFunctor ⋙
      (((monModel C).P0 oneSig).π ()).toFunctor :=
  rfl

end UlmerBialgebras.MonEx
