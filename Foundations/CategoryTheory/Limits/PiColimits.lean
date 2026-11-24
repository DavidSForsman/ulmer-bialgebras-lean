module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Connected

/-!
# Colimits in a product of categories

The dual of `PiLimits.lean`: colimits in a product `∀ i, C i` of categories are computed
componentwise.  As there, everything is stated universe-polymorphically, and without
assuming that the colimits involved exist.

## Main results

* `UlmerBialgebras.piIsColimitOfEval` — a cocone whose components are all colimit cocones is a
  colimit cocone;
* `UlmerBialgebras.piEvalIsColimit`, `UlmerBialgebras.piEvalPreservesColimitsOfShape` — conversely,
  the projections of a product of categories preserve colimits;
* `UlmerBialgebras.constPreservesColimitsOfShape` — a constant functor preserves colimits of
  connected shapes;
* `UlmerBialgebras.pi'PreservesColimitsOfShape`, `UlmerBialgebras.diagPreservesColimitsOfShape` —
  colimit preservation for the functor induced into a product of categories, resp. for the
  diagonal into a binary product of categories;
* `UlmerBialgebras.updateFunctor x i : C i ⥤ ∀ j, C j` — the insertion `a ↦ (x with a in slot i)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 4.7 (1)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {J : Type*} [Category J]

/-- The `i`-th component of a cocone in a product of categories. This is Mathlib's
`CategoryTheory.pi.coconeCompEval` with the universes of `J` and of the `C i` independent. -/
@[simps]
def piCoconeEval (F : J ⥤ ∀ i, C i) (c : Cocone F) (i : ι) : Cocone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr($(c.ι.naturality f) i) }

/-- A cocone in a product of categories all of whose components are colimit cocones is a
colimit cocone. -/
def piIsColimitOfEval {F : J ⥤ ∀ i, C i} {c : Cocone F}
    (h : ∀ i, IsColimit (piCoconeEval F c i)) : IsColimit c where
  desc s i := (h i).desc (piCoconeEval F s i)
  fac s j := by funext i; exact (h i).fac (piCoconeEval F s i) j
  uniq s m w := by
    funext i
    exact (h i).uniq (piCoconeEval F s i) (m i) fun j => congr($(w j) i)

/-- A family of componentwise cocones assembles into a cocone in the product category. This is
Mathlib's `CategoryTheory.pi.coconeOfCoconeCompEval` with the universes independent. -/
@[simps]
def piCoconeOfCocones (F : J ⥤ ∀ i, C i) (c : ∀ i, Cocone (F ⋙ Pi.eval C i)) : Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun _ _ f => by funext i; exact (c i).ι.naturality f }

/-- A product of categories has colimits of shape `J` if every factor does. -/
instance pi_hasColimitsOfShape [∀ i, HasColimitsOfShape J (C i)] :
    HasColimitsOfShape J (∀ i, C i) where
  has_colimit F :=
    ⟨⟨⟨piCoconeOfCocones F fun _ => colimit.cocone _,
      piIsColimitOfEval fun _ => colimit.isColimit _⟩⟩⟩

/-- A constant functor preserves colimits of connected shapes. -/
instance constPreservesColimitsOfShape [IsConnected J] {A : Type*} [Category A] {E : Type*}
    [Category E] (x : E) : PreservesColimitsOfShape J ((Functor.const A).obj x) where
  preservesColimit := { preserves := fun _ => ⟨isColimitConstCocone J x⟩ }

/-- A functor into a product of categories preserves the colimits preserved by all of its
components. -/
noncomputable instance pi'PreservesColimitsOfShape {A : Type*} [Category A] (f : ∀ j, A ⥤ C j)
    [∀ j, PreservesColimitsOfShape J (f j)] : PreservesColimitsOfShape J (Functor.pi' f) where
  preservesColimit := ⟨fun hc => ⟨piIsColimitOfEval fun j => isColimitOfPreserves (f j) hc⟩⟩

/-- The first component of a cocone in a binary product of categories. -/
@[simps]
def prodCoconeFst {A : Type*} [Category A] {D : J ⥤ A} (t : Cocone (D ⋙ Functor.diag A)) :
    Cocone D where
  pt := t.pt.1
  ι := { app := fun k => (t.ι.app k).1
         naturality := fun _ _ f => (Prod.ext_iff.mp (t.ι.naturality f)).1 }

/-- The second component of a cocone in a binary product of categories. -/
@[simps]
def prodCoconeSnd {A : Type*} [Category A] {D : J ⥤ A} (t : Cocone (D ⋙ Functor.diag A)) :
    Cocone D where
  pt := t.pt.2
  ι := { app := fun k => (t.ι.app k).2
         naturality := fun _ _ f => (Prod.ext_iff.mp (t.ι.naturality f)).2 }

/-- The diagonal functor into a binary product of categories preserves colimits. -/
instance diagPreservesColimitsOfShape {A : Type*} [Category A] :
    PreservesColimitsOfShape J (Functor.diag A) where
  preservesColimit {D} := by
    refine ⟨fun {c} hc => ⟨?_⟩⟩
    refine
      { desc := fun t => (hc.desc (prodCoconeFst t), hc.desc (prodCoconeSnd t))
        fac := fun t k => Prod.ext (hc.fac (prodCoconeFst t) k) (hc.fac (prodCoconeSnd t) k)
        uniq := fun t m hm => Prod.ext
          (hc.uniq (prodCoconeFst t) m.1 fun k => (Prod.ext_iff.mp (hm k)).1)
          (hc.uniq (prodCoconeSnd t) m.2 fun k => (Prod.ext_iff.mp (hm k)).2) }

section Update

variable [DecidableEq ι]

/-- The cocone in `∀ j, C j` obtained from a cocone on the `i`-th component of `F` and the
remaining components of a fixed cocone `c`. -/
@[simps]
def piCoconeAux (F : J ⥤ ∀ i, C i) (c : Cocone F) (i : ι) (t : Cocone (F ⋙ Pi.eval C i)) :
    Cocone F where
  pt := Function.update c.pt i t.pt
  ι :=
    { app := fun k j =>
        if h : j = i then
          (by subst h; exact t.ι.app k ≫ eqToHom (Function.update_self j t.pt c.pt).symm)
        else c.ι.app k j ≫ eqToHom (Function.update_of_ne h t.pt c.pt).symm
      naturality := by
        intro k k' f
        funext j
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Pi.comp_apply, Pi.id_apply,
          Category.comp_id]
        by_cases h : j = i
        · subst h
          simp only [dite_eq_left]
          have ht : (F.map f) j ≫ t.ι.app k' = t.ι.app k :=
            (t.ι.naturality f).trans (Category.comp_id _)
          exact (Category.assoc _ _ _).symm.trans (ht =≫ _)
        · simp only [dite_eq_right h]
          have hc : (F.map f) j ≫ c.ι.app k' j = c.ι.app k j := by
            simpa using congr($(c.ι.naturality f) j)
          rw [← Category.assoc, hc] }

/-- The family `x ⟶ Function.update x i y` which is `m` (followed by a transport) in slot `i`
and a transport elsewhere. -/
def updateHom (x : ∀ j, C j) (i : ι) (y : C i) (m : x i ⟶ y) :
    ∀ j, x j ⟶ Function.update x i y j := fun j =>
  if hj : j = i then (by subst hj; exact m ≫ eqToHom (Function.update_self j y x).symm)
  else eqToHom (Function.update_of_ne hj y x).symm

/-- The slot `i` of `updateHom x i y m` is `m` followed by a transport. -/
lemma updateHom_self (x : ∀ j, C j) (i : ι) (y : C i) (m : x i ⟶ y) :
    updateHom x i y m i = m ≫ eqToHom (Function.update_self i y x).symm := by
  simp [updateHom]

/-- Away from slot `i`, `updateHom x i y m` is a transport. -/
lemma updateHom_ne (x : ∀ j, C j) (i : ι) (y : C i) (m : x i ⟶ y) {j : ι} (hj : j ≠ i) :
    updateHom x i y m j = eqToHom (Function.update_of_ne hj y x).symm := by
  simp [updateHom, hj]

/-- The projections of a product of categories preserve colimits. -/
def piEvalIsColimit {F : J ⥤ ∀ i, C i} {c : Cocone F} (hc : IsColimit c) (i : ι) :
    IsColimit ((Pi.eval C i).mapCocone c) where
  desc t := (hc.desc (piCoconeAux F c i t)) i ≫ eqToHom (Function.update_self i t.pt c.pt)
  fac t k := by
    have h := congr($(hc.fac (piCoconeAux F c i t) k) i)
    simp only [Pi.comp_apply, piCoconeAux_ι_app, dite_eq_left] at h
    refine (Category.assoc _ _ _).symm.trans ((h =≫ _).trans ?_)
    exact (Category.assoc _ _ _).trans
      ((_ ≫= (eqToHom_trans _ _).trans (eqToHom_refl _ _)).trans (Category.comp_id _))
  uniq t m hm := by
    have key : updateHom c.pt i t.pt m = hc.desc (piCoconeAux F c i t) := by
      refine hc.uniq (piCoconeAux F c i t) _ (fun k => ?_)
      funext j
      by_cases hj : j = i
      · subst j
        refine (c.ι.app k i ≫= updateHom_self c.pt i t.pt m).trans ?_
        refine (Category.assoc _ _ _).symm.trans ((hm k =≫ _).trans ?_)
        simp only [piCoconeAux_ι_app, dite_eq_left]
        rfl
      · refine (c.ι.app k j ≫= updateHom_ne c.pt i t.pt m hj).trans ?_
        simp only [piCoconeAux_ι_app, dite_eq_right hj]
    have h2 := (updateHom_self c.pt i t.pt m).symm.trans (congr($key i))
    change m = hc.desc (piCoconeAux F c i t) i ≫ _
    refine Eq.trans ?_ (h2 =≫ eqToHom (Function.update_self i t.pt c.pt))
    exact ((Category.comp_id _).symm.trans
      (m ≫= ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm)).trans (Category.assoc _ _ _).symm

/-- The insertion `a ↦ (x with `a` in slot `i`)`, as a functor `C i ⥤ ∀ j, C j`. -/
def updateFunctor (x : ∀ j, C j) (i : ι) : C i ⥤ (∀ j, C j) :=
  Functor.pi' fun j =>
    if h : j = i then (by subst h; exact 𝟭 (C j)) else (Functor.const (C i)).obj (x j)

end Update

/-- The projections of a product of categories preserve colimits of shape `J`. -/
noncomputable instance piEvalPreservesColimitsOfShape (i : ι) :
    PreservesColimitsOfShape J (Pi.eval C i) where
  preservesColimit := by classical exact ⟨fun hc => ⟨piEvalIsColimit hc i⟩⟩

end UlmerBialgebras
