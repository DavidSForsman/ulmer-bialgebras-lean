module

public import UlmerBialgebras.Kan.KanProduct
public import UlmerBialgebras.Kan.CoKan

/-!
# Transport, composition and products of Kan-extension conditions

This file provides the general machinery needed to combine the three parts of Theorem 4.7
of *A Syntactic Approach to Ulmer's Bialgebras* into Corollaries 4.8, 4.11 and 4.12:

* `UlmerBialgebras.LeftExt.reindex` (and its dual) transports a category of extensions along an
  equality of the 1-cell being extended, together with the transport lemmas for
  initiality and quotient initiality;
* `UlmerBialgebras.LeftExt.push_push_obj` compares pushing along `f` and then `g` with pushing along
  the composite `f ≫ g`;
* `UlmerBialgebras.strictlyCreatesLeftKan_comp`: strict creation of left Kan extensions composes;
* `UlmerBialgebras.Product.preservesLeftKan_lift`,
  `UlmerBialgebras.Product.quotientInitial_push_lift` (and their duals): a 1-cell into a product
  inherits preservation of Kan extensions, resp. of quotient initiality, from its components.  This
  is the "only if" half of Theorem 4.7 (1) used in the proofs of Corollaries 4.11 and 4.12.

## Main results

* `UlmerBialgebras.LeftExt.reindex`: transport of a category of extensions along an equality.
* `UlmerBialgebras.strictlyCreatesLeftKan_comp`: strict creation of left Kan extensions composes.
* `UlmerBialgebras.Product.preservesLeftKan_lift`: if each component of a 1-cell into a product
  preserves a left Kan extension, so does the 1-cell.
* `UlmerBialgebras.Product.quotientInitial_push_lift`: the corresponding statement for quotient
  initiality.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 4.7, Corollaries 4.8, 4.11 and 4.12
-/

@[expose] public section

universe u v w s

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-! ## Quotient initiality and subterminality are invariant under isomorphism -/

/-- Quotient initiality is invariant under isomorphism. -/
lemma QuotientInitial.of_iso {A : Type*} [Category A] {a a' : A} (i : a ≅ a')
    (h : QuotientInitial a) : QuotientInitial a' :=
  fun b => ⟨fun x y => (cancel_epi i.hom).1 ((h b).elim (i.hom ≫ x) (i.hom ≫ y))⟩

/-! ## Transport along an equality of the extended 1-cell -/

section Reindex

variable {I X c c' c'' : Obj}

/-- Transport of left extensions along an equality `d = d'` of the 1-cell being extended. -/
def LeftExt.reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') : LeftExt k d ⥤ LeftExt k d' where
  obj L := LeftExt.mk L.ext (eqToHom h.symm ≫ L.unit)
  map {L L'} a := LeftExt.homMk (LeftExt.homCell (L := L) (L' := L') a)
    (by rw [LeftExt.mk_unit, LeftExt.mk_unit, Category.assoc, LeftExt.w a])
  map_id _ := LeftExt.hom_ext rfl
  map_comp _ _ := LeftExt.hom_ext rfl

/-- The extending 1-cell of a transported left extension is unchanged. -/
@[simp] lemma LeftExt.reindex_obj_ext (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') (L : LeftExt k d) :
    ((LeftExt.reindex k h).obj L).ext = L.ext := rfl

/-- The comparison 2-cell of a transported left extension. -/
@[simp] lemma LeftExt.reindex_obj_unit (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d')
    (L : LeftExt k d) : ((LeftExt.reindex k h).obj L).unit = eqToHom h.symm ≫ L.unit := rfl

/-- Transport does not change the 2-cell of a morphism of left extensions. -/
@[simp] lemma LeftExt.reindex_map_homCell (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d')
    {L L' : LeftExt k d} (a : L ⟶ L') :
    LeftExt.homCell ((LeftExt.reindex k h).map a) = LeftExt.homCell a := rfl

/-- Transport of right extensions along an equality `d = d'` of the 1-cell being extended. -/
def RightExt.reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') :
    RightExt k d ⥤ RightExt k d' where
  obj L := RightExt.mk L.ext (L.counit ≫ eqToHom h)
  map {L L'} a := RightExt.homMk (RightExt.homCell (L := L) (L' := L') a)
    (by rw [RightExt.mk_counit, RightExt.mk_counit, ← Category.assoc, RightExt.w a])
  map_id _ := RightExt.hom_ext rfl
  map_comp _ _ := RightExt.hom_ext rfl

/-- The extending 1-cell of a transported right extension is unchanged. -/
@[simp] lemma RightExt.reindex_obj_ext (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d')
    (L : RightExt k d) : ((RightExt.reindex k h).obj L).ext = L.ext := rfl

/-- The comparison 2-cell of a transported right extension. -/
@[simp] lemma RightExt.reindex_obj_counit (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d')
    (L : RightExt k d) : ((RightExt.reindex k h).obj L).counit = L.counit ≫ eqToHom h := rfl

/-- Transport does not change the 2-cell of a morphism of right extensions. -/
@[simp] lemma RightExt.reindex_map_homCell (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d')
    {L L' : RightExt k d} (a : L ⟶ L') :
    RightExt.homCell ((RightExt.reindex k h).map a) = RightExt.homCell a := rfl

/-- Transport of left extensions along `rfl` is the identity on objects. -/
@[simp] lemma LeftExt.reindex_rfl_obj (k : I ⟶ X) {d : I ⟶ c} (L : LeftExt k d) :
    (LeftExt.reindex k (rfl : d = d)).obj L = L :=
  LeftExt.eq_of_ext_eq rfl (by
    rw [LeftExt.reindex_obj_unit, eqToHom_refl, Category.id_comp]
    exact (whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _))

/-- Transport of right extensions along `rfl` is the identity on objects. -/
@[simp] lemma RightExt.reindex_rfl_obj (k : I ⟶ X) {d : I ⟶ c} (L : RightExt k d) :
    (RightExt.reindex k (rfl : d = d)).obj L = L :=
  RightExt.eq_of_ext_eq rfl (by
    rw [RightExt.reindex_obj_counit, eqToHom_refl, Category.comp_id]
    exact (eq_whisker (eqToHom_refl _ _) _).trans (Category.id_comp _))

/-- Transport of left extensions along `d = d'` is injective on objects. -/
lemma LeftExt.reindex_obj_injective (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d')
    {A B : LeftExt k d} (hAB : (LeftExt.reindex k h).obj A = (LeftExt.reindex k h).obj B) :
    A = B := by
  subst h; simpa using hAB

/-- Transport along `d = d'` (`LeftExt.reindex`) preserves initial left extensions. -/
lemma isInitial_reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') {A : LeftExt k d}
    (hA : Nonempty (Limits.IsInitial A)) :
    Nonempty (Limits.IsInitial ((LeftExt.reindex k h).obj A)) := by
  subst h; simpa using hA

/-- Transport along `d = d'` (`LeftExt.reindex`) preserves quotient initiality. -/
lemma quotientInitial_reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') {A : LeftExt k d}
    (hA : QuotientInitial A) : QuotientInitial ((LeftExt.reindex k h).obj A) := by
  subst h; simpa using hA

/-- Transport along `d = d'` (`RightExt.reindex`) preserves subterminality. -/
lemma subterminal_reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') {A : RightExt k d}
    (hA : Subterminal A) : Subterminal ((RightExt.reindex k h).obj A) := by
  subst h; simpa using hA

/-- Transport along `d = d'` (`LeftExt.reindex`) reflects initial left extensions. -/
lemma isInitial_of_reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') {A : LeftExt k d}
    (hA : Nonempty (Limits.IsInitial ((LeftExt.reindex k h).obj A))) :
    Nonempty (Limits.IsInitial A) := by
  subst h; simpa using hA

/-- Transport along `d = d'` (`RightExt.reindex`) reflects terminal right extensions. -/
lemma isTerminal_of_reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') {A : RightExt k d}
    (hA : Nonempty (Limits.IsTerminal ((RightExt.reindex k h).obj A))) :
    Nonempty (Limits.IsTerminal A) := by
  subst h; simpa using hA

/-- Transport along `d = d'` (`LeftExt.reindex`) reflects quotient initiality. -/
lemma quotientInitial_of_reindex (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') {A : LeftExt k d}
    (hA : QuotientInitial ((LeftExt.reindex k h).obj A)) : QuotientInitial A := by
  subst h; simpa using hA

variable [Bicategory.Strict Obj]

/-- Pushing commutes with transport. -/
lemma LeftExt.push_reindex_obj (k : I ⟶ X) {d d' : I ⟶ c} (h : d = d') (w : c ⟶ c')
    (A : LeftExt k d) :
    (LeftExt.push k d' w).obj ((LeftExt.reindex k h).obj A)
      = (LeftExt.reindex k (show d ≫ w = d' ≫ w by rw [h])).obj
          ((LeftExt.push k d w).obj A) := by
  subst h; simp

/-- Pushing along `f` and then along `g` is pushing along `f ≫ g`, up to transport. -/
lemma LeftExt.push_push_obj (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') (g : c' ⟶ c'')
    (L : LeftExt k d) :
    (LeftExt.push k (d ≫ f) g).obj ((LeftExt.push k d f).obj L)
      = (LeftExt.reindex k (Category.assoc d f g).symm).obj ((LeftExt.push k d (f ≫ g)).obj L) := by
  refine LeftExt.eq_of_ext_eq (Category.assoc L.ext f g) ?_
  simp only [LeftExt.push_obj_unit, LeftExt.reindex_obj_unit, Bicategory.comp_whiskerRight,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.whiskerRight_comp, Category.assoc,
      eqToHom_trans,
    eqToHom_trans_assoc]
  -- the leading transport is along `d ≫ f ≫ g = d ≫ f ≫ g`, an identity
  exact (Category.id_comp _).symm.trans (eq_whisker (eqToHom_refl _ _).symm _)

/-- Pushing along `f` and then along `g` is pushing along `f ≫ g`, up to transport. -/
lemma RightExt.push_push_obj (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') (g : c' ⟶ c'')
    (L : RightExt k d) :
    (RightExt.push k (d ≫ f) g).obj ((RightExt.push k d f).obj L)
      = (RightExt.reindex k (Category.assoc d f g).symm).obj ((RightExt.push k d (f ≫
        g)).obj L) := by
  refine RightExt.eq_of_ext_eq (Category.assoc L.ext f g) ?_
  simp only [RightExt.push_obj_counit, RightExt.reindex_obj_counit, Bicategory.comp_whiskerRight,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.whiskerRight_comp, Category.assoc,
      eqToHom_trans,
    eqToHom_trans_assoc]
  -- the trailing transport is along `d ≫ f ≫ g = d ≫ f ≫ g`, an identity
  exact (eqToHom_trans_assoc _ _ _).trans
    (whisker_eq _ ((whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _)))

/-- Pushing along equal 1-cells gives equal extensions, up to transport. -/
lemma LeftExt.push_congr_obj (k : I ⟶ X) (d : I ⟶ c) {f f' : c ⟶ c'} (hf : f = f')
    (L : LeftExt k d) :
    (LeftExt.push k d f).obj L
      = (LeftExt.reindex k (show d ≫ f' = d ≫ f by rw [hf])).obj
          ((LeftExt.push k d f').obj L) := by
  subst hf; simp

/-- Pushing along equal 1-cells gives equal extensions, up to transport. -/
lemma RightExt.push_congr_obj (k : I ⟶ X) (d : I ⟶ c) {f f' : c ⟶ c'} (hf : f = f')
    (L : RightExt k d) :
    (RightExt.push k d f).obj L
      = (RightExt.reindex k (show d ≫ f' = d ≫ f by rw [hf])).obj
          ((RightExt.push k d f').obj L) := by
  subst hf; simp

end Reindex

variable [Bicategory.Strict Obj]

/-! ## Composition of strict creation -/

section Comp

variable {I X c c' c'' : Obj}

/-- Strict creation of left Kan extensions composes: if `g` strictly creates the left Kan
extensions of `d ≫ f` along `k`, and, for every left Kan extension `b` of `d` along `k`
in the target, `f` strictly creates the left Kan extensions of `d`, then `f ≫ g` strictly
creates the left Kan extensions of `d`. -/
theorem strictlyCreatesLeftKan_comp (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') (g : c' ⟶ c'')
    (hg : StrictlyCreatesLeftKan k (d ≫ f) g)
    (hf : ∀ b : LeftExt k (d ≫ (f ≫ g)), Nonempty (Limits.IsInitial b) →
      StrictlyCreatesLeftKan k d f) :
    StrictlyCreatesLeftKan k d (f ≫ g) := by
  intro b hb
  obtain ⟨⟨a₀, ha₀, ha₀uniq⟩, hinit⟩ := hg _ (isInitial_reindex k (Category.assoc d f g).symm hb)
  obtain ⟨⟨L₀, hL₀, hL₀uniq⟩, hinit2⟩ := hf b hb a₀ (hinit a₀ ha₀)
  have key : ∀ L : LeftExt k d, (LeftExt.push k d (f ≫ g)).obj L = b →
      (LeftExt.push k d f).obj L = a₀ := by
    intro L hL
    refine ha₀uniq _ ?_
    change (LeftExt.push k (d ≫ f) g).obj ((LeftExt.push k d f).obj L) = _
    rw [LeftExt.push_push_obj, hL]
  refine ⟨⟨L₀, ?_, fun L hL => hL₀uniq L (key L hL)⟩, fun L hL => hinit2 L (key L hL)⟩
  refine LeftExt.reindex_obj_injective k (Category.assoc d f g).symm ?_
  rw [← LeftExt.push_push_obj, hL₀, ha₀]

/-- Preservation of left Kan extensions composes. -/
lemma preservesLeftKan_comp {k : I ⟶ X} {d : I ⟶ c} {f : c ⟶ c'} {g : c' ⟶ c''}
    (hf : PreservesLeftKan k d f) (hg : PreservesLeftKan k (d ≫ f) g) :
    PreservesLeftKan k d (f ≫ g) := by
  intro L hL
  refine isInitial_of_reindex k (Category.assoc d f g).symm ?_
  rw [← LeftExt.push_push_obj]
  exact hg _ (hf L hL)

/-- Preservation of right Kan extensions composes. -/
lemma preservesRightKan_comp {k : I ⟶ X} {d : I ⟶ c} {f : c ⟶ c'} {g : c' ⟶ c''}
    (hf : PreservesRightKan k d f) (hg : PreservesRightKan k (d ≫ f) g) :
    PreservesRightKan k d (f ≫ g) := by
  intro L hL
  refine isTerminal_of_reindex k (Category.assoc d f g).symm ?_
  rw [← RightExt.push_push_obj]
  exact hg _ (hf L hL)

/-- An initial object is quotient initial. -/
lemma quotientInitial_of_isInitial {A : Type*} [Category A] {a : A} (h : Limits.IsInitial a) :
    QuotientInitial a := fun _ => ⟨fun x y => h.hom_ext x y⟩

/-- A terminal object is subterminal. -/
lemma subterminal_of_isTerminal {A : Type*} [Category A] {a : A} (h : Limits.IsTerminal a) :
    Subterminal a := fun _ x y => h.hom_ext x y

/-- Preservation of left Kan extensions only depends on the 1-cells involved. -/
lemma preservesLeftKan_congr {k : I ⟶ X} {d d' : I ⟶ c} {f f' : c ⟶ c'} (hd : d = d')
    (hf : f = f') (h : PreservesLeftKan k d f) : PreservesLeftKan k d' f' := by
  subst hd; subst hf; exact h

end Comp

/-! ## 1-cells into a product -/

namespace Product

variable {ι : Type s} {cs : ι → Obj} (P : Product cs) {I X c : Obj}

/-- If each component preserves left Kan extensions, so does the induced 1-cell into the
product. -/
lemma preservesLeftKan_lift (k : I ⟶ X) (d : I ⟶ c) (h : ∀ i, c ⟶ cs i)
    (hh : ∀ i, PreservesLeftKan k d (h i)) : PreservesLeftKan k d (P.lift h) := by
  intro L hL
  have key : ∀ i, Nonempty (Limits.IsInitial
      ((LeftExt.push k (d ≫ P.lift h) (P.π i)).obj ((LeftExt.push k d (P.lift h)).obj L))) := by
    intro i
    rw [LeftExt.push_push_obj]
    refine isInitial_reindex _ _ ?_
    rw [LeftExt.push_congr_obj k d (P.lift_π h i) L]
    exact isInitial_reindex _ _ (hh i L hL)
  exact ⟨isInitialOfFullyFaithful (kanFunctorLeft P k (d ≫ P.lift h))
    (isInitialPi (fun i => (key i).some))⟩

/-- A 1-cell into a product preserves left Kan extensions exactly when each component does. -/
lemma preservesLeftKan_lift_iff (k : I ⟶ X) (d : I ⟶ c) (h : ∀ i, c ⟶ cs i) :
    PreservesLeftKan k d (P.lift h) ↔ ∀ i, PreservesLeftKan k d (h i) := by
  constructor
  · intro hp i
    exact preservesLeftKan_congr rfl (P.lift_π h i)
      (preservesLeftKan_comp hp (P.preserves_leftKan k (d ≫ P.lift h) i))
  · exact P.preservesLeftKan_lift k d h

/-- If each component preserves right Kan extensions, so does the induced 1-cell into the
product. -/
lemma preservesRightKan_lift (k : I ⟶ X) (d : I ⟶ c) (h : ∀ i, c ⟶ cs i)
    (hh : ∀ i, PreservesRightKan k d (h i)) : PreservesRightKan k d (P.lift h) := by
  refine (Co.preservesLeftKan_iff k d (P.lift h)).1 ?_
  exact Product.preservesLeftKan_lift (Co.product P) (Co.hom k) (Co.hom d)
    (fun i => Co.hom (h i)) (fun i => (Co.preservesLeftKan_iff k d (h i)).2 (hh i))

/-- The right Kan version of the componentwise criterion, by duality. -/
lemma preservesRightKan_lift_iff (k : I ⟶ X) (d : I ⟶ c) (h : ∀ i, c ⟶ cs i) :
    PreservesRightKan k d (P.lift h) ↔ ∀ i, PreservesRightKan k d (h i) := by
  constructor
  · intro hp i
    exact (Co.preservesLeftKan_iff k d (h i)).1
      (((Co.product P).preservesLeftKan_lift_iff (Co.hom k) (Co.hom d)
        (fun i => Co.hom (h i))).1 ((Co.preservesLeftKan_iff k d (P.lift h)).2 hp) i)
  · exact P.preservesRightKan_lift k d h

/-- If each component preserves quotient initiality of `L`, so does the induced 1-cell into
the product. -/
lemma quotientInitial_push_lift (k : I ⟶ X) (d : I ⟶ c) (h : ∀ i, c ⟶ cs i)
    (L : LeftExt k d) (hq : ∀ i, QuotientInitial ((LeftExt.push k d (h i)).obj L)) :
    QuotientInitial ((LeftExt.push k d (P.lift h)).obj L) := by
  intro Y
  refine ⟨fun a b => LeftExt.hom_ext (P.cell_ext fun i => ?_)⟩
  have hqi : QuotientInitial ((LeftExt.push k (d ≫ P.lift h) (P.π i)).obj
      ((LeftExt.push k d (P.lift h)).obj L)) := by
    rw [LeftExt.push_push_obj]
    refine quotientInitial_reindex _ _ ?_
    rw [LeftExt.push_congr_obj k d (P.lift_π h i) L]
    exact quotientInitial_reindex _ _ (hq i)
  exact LeftExt.hom_ext_iff.mp ((hqi ((LeftExt.push k (d ≫ P.lift h) (P.π i)).obj Y)).elim
    ((LeftExt.push k (d ≫ P.lift h) (P.π i)).map a)
    ((LeftExt.push k (d ≫ P.lift h) (P.π i)).map b))

/-- If each component preserves subterminality of `L`, so does the induced 1-cell into the
product. -/
lemma subterminal_push_lift (k : I ⟶ X) (d : I ⟶ c) (h : ∀ i, c ⟶ cs i)
    (L : RightExt k d) (hq : ∀ i, Subterminal ((RightExt.push k d (h i)).obj L)) :
    Subterminal ((RightExt.push k d (P.lift h)).obj L) := by
  intro Y a b
  refine RightExt.hom_ext (P.cell_ext fun i => ?_)
  have hqi : Subterminal ((RightExt.push k (d ≫ P.lift h) (P.π i)).obj
      ((RightExt.push k d (P.lift h)).obj L)) := by
    rw [RightExt.push_push_obj]
    refine subterminal_reindex _ _ ?_
    rw [RightExt.push_congr_obj k d (P.lift_π h i) L]
    exact subterminal_reindex _ _ (hq i)
  exact RightExt.hom_ext_iff.mp (hqi
    ((RightExt.push k (d ≫ P.lift h) (P.π i)).map a)
    ((RightExt.push k (d ≫ P.lift h) (P.π i)).map b))

end Product

end UlmerBialgebras
