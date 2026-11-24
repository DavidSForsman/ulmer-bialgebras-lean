module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import UlmerBialgebras.Appendix.VCatOfEnriched

/-!
# The free `V`-category on an arrow

For an object `x` of the base `V`, the **free `V`-category on an arrow of shape `x`** is the
two-object `V`-category

```
  Hom(0,0) = 𝟙_V     Hom(0,1) = x
  Hom(1,0) = 0       Hom(1,1) = 𝟙_V
```

where `0` is an initial object of `V` that is absorbing for the tensor product (this is
automatic when `V` is braided monoidal closed or biclosed, since tensoring on either side is then
a left adjoint).  All the
composition maps whose source involves `Hom(1,0)` are forced by initiality, and the remaining
ones are unitors, so the enriched category axioms reduce to monoidal coherence.

* `UlmerBialgebras.MonoidalInitial` — the data of such an absorbing initial object;
* `UlmerBialgebras.ArrowObj`, `UlmerBialgebras.arrowVCat` — the free `V`-category on an arrow, as an
  object of `CAT_V`, with two objects, hence *small*;
* `UlmerBialgebras.arrowVFunctor` — `V`-functors out of it: a pair of objects `c c'` of `E` together
  with a generalized element `k : x ⟶ (c ⟶[V] c')` of the hom-object;
* `UlmerBialgebras.arrowVNatTrans` — `V`-natural transformations between `V`-functors out of it: a
  pair of components subject to a *single* naturality square.

This is the probe that detects `V`-enriched full faithfulness: post-composition with a
`V`-functor `F` acts on `CAT_V(2_x, -)` as the map `V(x, (c ⟶[V] c')) → V(x, (Fc ⟶[V] Fc'))`
given by `F.emap`.

## Main definitions

* `UlmerBialgebras.MonoidalInitial`: an initial object of `V` that is absorbing for the tensor
  product.
* `UlmerBialgebras.arrowVCat`: the free `V`-category `2_x` on an arrow of shape `x`, as an object of
  `CAT_V`.
* `UlmerBialgebras.arrowVFunctor`: the `V`-functor out of `2_x` sending the generic arrow to a
  generalized element `k : x ⟶ (c ⟶[V] c')`.
* `UlmerBialgebras.arrowVNatTrans`: the `V`-natural transformation between `V`-functors out of `2_x`
  given by two components satisfying the naturality square at the generic arrow.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma A.3,
  Definition A.4 (the `V`-category `2_x`)
* [H. Wolff, *V-cat and V-graph*][wolffVcatVgraph1974]
-/

@[expose] public section

universe w v u u₁

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory Limits

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-! ## An absorbing initial object -/

/-- An **absorbing initial object** of a monoidal category: an initial object whose tensor
products with arbitrary objects, on either side, are again initial.  When `V` is braided monoidal
closed (or biclosed) and has an initial object this is automatic, since `x ⊗ -` and `- ⊗ x` are
then left adjoints (this construction is not formalized here). -/
structure MonoidalInitial (V : Type v) [Category.{w} V] [MonoidalCategory V] where
  /-- The initial object. -/
  zero : V
  /-- It is initial. -/
  isInitial : IsInitial zero
  /-- Tensoring it on the left with anything is initial. -/
  zeroTensor : ∀ y : V, IsInitial (zero ⊗ y)
  /-- Tensoring it on the right with anything is initial. -/
  tensorZero : ∀ y : V, IsInitial (y ⊗ zero)

namespace MonoidalInitial

/-- Any initial object tensored on the left with anything is initial. -/
def tensorLeftInitial (Z : MonoidalInitial V) (y : V) {u : V} (hu : IsInitial u) :
    IsInitial (y ⊗ u) :=
  (Z.tensorZero y).ofIso (Iso.refl y ⊗ᵢ (hu.uniqueUpToIso Z.isInitial).symm)

end MonoidalInitial

/-! ## The two-object `V`-category -/

/-- The two objects of the free `V`-category on an arrow. -/
inductive ArrowObj (Z : MonoidalInitial V) (x : V) : Type u₁ where
  /-- The source of the generic arrow. -/
  | src : ArrowObj Z x
  /-- The target of the generic arrow. -/
  | tgt : ArrowObj Z x

namespace ArrowObj

variable (Z : MonoidalInitial V) (x : V)

/-- The hom-objects of the free `V`-category on an arrow. -/
def hom : ArrowObj.{w, v, u₁} Z x → ArrowObj.{w, v, u₁} Z x → V
  | .src, .src => 𝟙_ V
  | .src, .tgt => x
  | .tgt, .src => Z.zero
  | .tgt, .tgt => 𝟙_ V

/-- The identities of the free `V`-category on an arrow. -/
def eid : ∀ a : ArrowObj.{w, v, u₁} Z x, 𝟙_ V ⟶ hom Z x a a
  | .src => 𝟙 _
  | .tgt => 𝟙 _

/-- The composition of the free `V`-category on an arrow: the unitors, except where the
source involves the initial hom-object `Hom(1,0)`, in which case it is forced. -/
def ecomp : ∀ a b c : ArrowObj.{w, v, u₁} Z x, hom Z x a b ⊗ hom Z x b c ⟶ hom Z x a c
  | .src, .src, .src => (λ_ (𝟙_ V)).hom
  | .src, .src, .tgt => (λ_ x).hom
  | .src, .tgt, .src => (Z.tensorZero x).to _
  | .src, .tgt, .tgt => (ρ_ x).hom
  | .tgt, .src, .src => (Z.zeroTensor _).to _
  | .tgt, .src, .tgt => (Z.zeroTensor x).to _
  | .tgt, .tgt, .src => (Z.tensorZero _).to _
  | .tgt, .tgt, .tgt => (λ_ (𝟙_ V)).hom

/-- The left unit law of `ecomp Z x`: the `V`-category axiom `id_comp`. -/
theorem ecomp_id_comp (a b : ArrowObj.{w, v, u₁} Z x) :
    (λ_ (hom Z x a b)).inv ≫ eid Z x a ▷ hom Z x a b ≫ ecomp Z x a a b = 𝟙 _ := by
  cases a <;> cases b <;>
    first
      | exact Z.isInitial.hom_ext _ _
      | (show (λ_ _).inv ≫ _ ≫ _ = _; simp [eid, ecomp, hom])

/-- The right unit law of `ecomp Z x`: the `V`-category axiom `comp_id`. -/
theorem ecomp_comp_id (a b : ArrowObj.{w, v, u₁} Z x) :
    (ρ_ (hom Z x a b)).inv ≫ hom Z x a b ◁ eid Z x b ≫ ecomp Z x a b b = 𝟙 _ := by
  cases a <;> cases b <;>
    first
      | exact Z.isInitial.hom_ext _ _
      | (show (ρ_ _).inv ≫ _ ≫ _ = _; simp [eid, ecomp, hom, unitors_equal])

/-- The associativity of `ecomp Z x`: the `V`-category axiom `assoc`. -/
theorem ecomp_assoc (a b c d : ArrowObj.{w, v, u₁} Z x) :
    (α_ (hom Z x a b) (hom Z x b c) (hom Z x c d)).inv ≫ ecomp Z x a b c ▷ hom Z x c d ≫
        ecomp Z x a c d =
      hom Z x a b ◁ ecomp Z x b c d ≫ ecomp Z x a b d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
      | exact (Z.zeroTensor _).hom_ext _ _
      | exact (Z.tensorLeftInitial _ (Z.zeroTensor _)).hom_ext _ _
      | exact (Z.tensorLeftInitial _ (Z.tensorZero _)).hom_ext _ _
      | (show (α_ _ _ _).inv ≫ _ ≫ _ = _ ≫ _;
          first | (simp [ecomp, hom]; done) | (dsimp [ecomp, hom]; monoidal))

/-- The `V`-category structure on the two objects `src`, `tgt` of the free `V`-category on
an arrow of shape `x`, with composition `ecomp` and identities `eid`. -/
instance enrichedCategory : EnrichedCategory V (ArrowObj.{w, v, u₁} Z x) where
  Hom := hom Z x
  id := eid Z x
  comp := ecomp Z x
  id_comp := ecomp_id_comp Z x
  comp_id := ecomp_comp_id Z x
  assoc := ecomp_assoc Z x
/-- The hom-object from `src` to `tgt` is `x`. -/
@[simp] lemma eHom_src_tgt : ((.src : ArrowObj.{w, v, u₁} Z x) ⟶[V] .tgt) = x := rfl

/-- The hom-object from `src` to itself is the unit `𝟙_ V`. -/
@[simp] lemma eHom_src_src : ((.src : ArrowObj.{w, v, u₁} Z x) ⟶[V] .src) = 𝟙_ V := rfl

/-- The hom-object from `tgt` to itself is the unit `𝟙_ V`. -/
@[simp] lemma eHom_tgt_tgt : ((.tgt : ArrowObj.{w, v, u₁} Z x) ⟶[V] .tgt) = 𝟙_ V := rfl

/-- The hom-object from `tgt` to `src` is the initial object `Z.zero`. -/
@[simp] lemma eHom_tgt_src : ((.tgt : ArrowObj.{w, v, u₁} Z x) ⟶[V] .src) = Z.zero := rfl


/-- The identity of `src` is `𝟙 (𝟙_ V)`. -/
lemma eId_src : eId V (.src : ArrowObj.{w, v, u₁} Z x) = 𝟙 (𝟙_ V) := rfl
/-- The identity of `tgt` is `𝟙 (𝟙_ V)`. -/
lemma eId_tgt : eId V (.tgt : ArrowObj.{w, v, u₁} Z x) = 𝟙 (𝟙_ V) := rfl

/-- The `V`-category of the arrow has (two, hence) `w`-small many objects. -/
instance : Small.{w} (ArrowObj.{w, v, u₁} Z x) :=
  small_of_injective (f := fun a => match a with
      | .src => (⟨false⟩ : ULift.{w} Bool)
      | .tgt => ⟨true⟩)
    (by rintro ⟨⟩ ⟨⟩ h <;> simp_all)

end ArrowObj

variable (Z : MonoidalInitial V) (x : V)

/-- **The free `V`-category on an arrow of shape `x`**, as an object of `CAT_V`. -/
def arrowVCat : VCat.{w, v, u₁} V := VCat.of (ForgetEnrichment V (ArrowObj.{w, v, u₁} Z x))

/-- The source of the generic arrow, as an object of `arrowVCat`. -/
def arrowSrc : (arrowVCat.{w, v, u₁} Z x).carrier := ForgetEnrichment.of V .src

/-- The target of the generic arrow, as an object of `arrowVCat`. -/
def arrowTgt : (arrowVCat.{w, v, u₁} Z x).carrier := ForgetEnrichment.of V .tgt

/-- The free `V`-category on an arrow has a `w`-small type of objects. -/
instance : Small.{w} (arrowVCat.{w, v, u₁} Z x).carrier :=
  inferInstanceAs (Small.{w} (ArrowObj.{w, v, u₁} Z x))

/-! ## Two unit laws for a generalized element of a hom-object -/

section Unit

variable {E : Type u} [Category.{w} E] [EnrichedOrdinaryCategory V E]

/-- Composing a generalized element of `(c ⟶[V] c')` with the identity of `c` on the left. -/
lemma leftUnitor_comp_eId {y : V} {c c' : E} (k : y ⟶ (c ⟶[V] c')) :
    (λ_ y).hom ≫ k = (eId V c ⊗ₘ k) ≫ eComp V c c c' := by
  have h : eId V c ▷ (c ⟶[V] c') ≫ eComp V c c c' = (λ_ (c ⟶[V] c')).hom := by
    have := e_id_comp V c c'
    rw [Iso.inv_comp_eq] at this
    simpa using this
  rw [MonoidalCategory.tensorHom_def', Category.assoc, h,
    MonoidalCategory.leftUnitor_naturality]

/-- Composing a generalized element of `(c ⟶[V] c')` with the identity of `c'` on the
right. -/
lemma rightUnitor_comp_eId {y : V} {c c' : E} (k : y ⟶ (c ⟶[V] c')) :
    (ρ_ y).hom ≫ k = (k ⊗ₘ eId V c') ≫ eComp V c c' c' := by
  have h : (c ⟶[V] c') ◁ eId V c' ≫ eComp V c c' c' = (ρ_ (c ⟶[V] c')).hom := by
    have := e_comp_id V c c'
    rw [Iso.inv_comp_eq] at this
    simpa using this
  rw [MonoidalCategory.tensorHom_def, Category.assoc, h,
    MonoidalCategory.rightUnitor_naturality]

/-- The identity of `c` whiskered on the left by `f` and the identity of `d` whiskered on the
right by `f` are the same generalized element of `(c ⟶[V] d)`, namely the name of `f`. -/
lemma eId_eHomWhiskerLeft {c d : E} (f : c ⟶ d) :
    eId V c ≫ eHomWhiskerLeft V c f = eId V d ≫ eHomWhiskerRight V f d := by
  rw [← eHomEquiv_id (V := V) (X := c), eHomEquiv_comp_eHomWhiskerLeft,
    ← eHomEquiv_id (V := V) (X := d), eHomEquiv_comp_eHomWhiskerRight]
  simp

end Unit

/-! ## `V`-functors out of the free `V`-category on an arrow -/

section Functor

variable {E : Type u} [Category.{w} E] [EnrichedOrdinaryCategory V E]

/-- The action on objects of the `V`-functor determined by a generalized element. -/
def arrowObjMap (c c' : E) : ArrowObj.{w, v, u₁} Z x → E
  | .src => c
  | .tgt => c'

/-- The action on hom-objects of the `V`-functor determined by a generalized element. -/
def arrowEmap (c c' : E) (k : x ⟶ (c ⟶[V] c')) : ∀ a b : ArrowObj.{w, v, u₁} Z x,
    (a ⟶[V] b) ⟶ (arrowObjMap Z x c c' a ⟶[V] arrowObjMap Z x c c' b)
  | .src, .src => eId V c
  | .src, .tgt => k
  | .tgt, .src => Z.isInitial.to _
  | .tgt, .tgt => eId V c'

/-- **`V`-functors out of the free `V`-category on an arrow**: the `V`-functor sending the
generic arrow to the generalized element `k : x ⟶ (c ⟶[V] c')`. -/
def arrowVFunctor (c c' : E) (k : x ⟶ (c ⟶[V] c')) :
    VFunctor V (ForgetEnrichment V (ArrowObj.{w, v, u₁} Z x)) E :=
  VFunctor.ofEnriched (arrowObjMap Z x c c') (arrowEmap Z x c c' k)
    (by
      rintro (_ | _) <;>
        simp [arrowEmap, ArrowObj.eId_src, ArrowObj.eId_tgt, arrowObjMap])
    (by
      rintro (_ | _) (_ | _) (_ | _)
      · exact leftUnitor_comp_eId (eId V c)
      · exact leftUnitor_comp_eId k
      · exact (Z.tensorZero x).hom_ext _ _
      · exact rightUnitor_comp_eId k
      · exact (Z.zeroTensor _).hom_ext _ _
      · exact (Z.zeroTensor _).hom_ext _ _
      · exact (Z.tensorZero _).hom_ext _ _
      · exact leftUnitor_comp_eId (eId V c'))

/-- `arrowVFunctor` sends `src` to `c`. -/
@[simp] lemma arrowVFunctor_obj_src (c c' : E) (k : x ⟶ (c ⟶[V] c')) :
    (arrowVFunctor Z x c c' k).obj (.src) = c := rfl

/-- `arrowVFunctor` sends `tgt` to `c'`. -/
@[simp] lemma arrowVFunctor_obj_tgt (c c' : E) (k : x ⟶ (c ⟶[V] c')) :
    (arrowVFunctor Z x c c' k).obj (.tgt) = c' := rfl

/-- `arrowVFunctor` acts on the hom-object from `src` to `tgt` by `k`. -/
@[simp] lemma arrowVFunctor_emap (c c' : E) (k : x ⟶ (c ⟶[V] c')) :
    (arrowVFunctor Z x c c' k).emap (.src) (.tgt) = k := rfl

end Functor

/-! ## `V`-natural transformations out of the free `V`-category on an arrow -/

section NatTrans

variable {E : Type u} [Category.{w} E] [EnrichedOrdinaryCategory V E]

/-- **`V`-natural transformations out of the free `V`-category on an arrow**: a pair of
components subject to the single naturality square at the generic arrow.  The squares at the
identities hold automatically, and the one at `Hom(1,0)` because that hom-object is
initial. -/
def arrowVNatTrans
    {H H' : VFunctor V (ForgetEnrichment V (ArrowObj.{w, v, u₁} Z x)) E}
    (app0 : H.obj (.src) ⟶ H'.obj (.src)) (app1 : H.obj (.tgt) ⟶ H'.obj (.tgt))
    (hsq : H.emap (.src) (.tgt) ≫ eHomWhiskerLeft V (H.obj (.src)) app1
      = H'.emap (.src) (.tgt) ≫ eHomWhiskerRight V app0 (H'.obj (.tgt))) :
    VNatTrans H H' where
  app a := ArrowObj.casesOn (motive := fun a => H.obj a ⟶ H'.obj a) a app0 app1
  vnaturality a b := by
    have hs : H.emap (.src) (.src) = eId V (H.obj (.src)) := by
      have h := H.emap_id (ArrowObj.src)
      -- `eId V .src` is `𝟙 (𝟙_ V)` (`ArrowObj.eId_src`, by `rfl`)
      exact (Category.id_comp _).symm.trans h
    have ht : H.emap (.tgt) (.tgt) = eId V (H.obj (.tgt)) := by
      have h := H.emap_id (ArrowObj.tgt)
      -- `eId V .tgt` is `𝟙 (𝟙_ V)` (`ArrowObj.eId_tgt`, by `rfl`)
      exact (Category.id_comp _).symm.trans h
    have hs' : H'.emap (.src) (.src) = eId V (H'.obj (.src)) := by
      have h := H'.emap_id (ArrowObj.src)
      -- `eId V .src` is `𝟙 (𝟙_ V)` (`ArrowObj.eId_src`, by `rfl`)
      exact (Category.id_comp _).symm.trans h
    have ht' : H'.emap (.tgt) (.tgt) = eId V (H'.obj (.tgt)) := by
      have h := H'.emap_id (ArrowObj.tgt)
      -- `eId V .tgt` is `𝟙 (𝟙_ V)` (`ArrowObj.eId_tgt`, by `rfl`)
      exact (Category.id_comp _).symm.trans h
    rcases a with _ | _ <;> rcases b with _ | _
    · rw [hs, hs']; exact eId_eHomWhiskerLeft app0
    · exact hsq
    · exact Z.isInitial.hom_ext _ _
    · rw [ht, ht']; exact eId_eHomWhiskerLeft app1

/-- The component of `arrowVNatTrans` at `src` is `app0`. -/
@[simp] lemma arrowVNatTrans_app_src
    {H H' : VFunctor V (ForgetEnrichment V (ArrowObj.{w, v, u₁} Z x)) E}
    (app0 : H.obj (.src) ⟶ H'.obj (.src)) (app1 : H.obj (.tgt) ⟶ H'.obj (.tgt)) (hsq) :
    (arrowVNatTrans Z x app0 app1 hsq).app (.src) = app0 := rfl

/-- The component of `arrowVNatTrans` at `tgt` is `app1`. -/
@[simp] lemma arrowVNatTrans_app_tgt
    {H H' : VFunctor V (ForgetEnrichment V (ArrowObj.{w, v, u₁} Z x)) E}
    (app0 : H.obj (.src) ⟶ H'.obj (.src)) (app1 : H.obj (.tgt) ⟶ H'.obj (.tgt)) (hsq) :
    (arrowVNatTrans Z x app0 app1 hsq).app (.tgt) = app1 := rfl

end NatTrans

end UlmerBialgebras
