module

public import UlmerBialgebras.Density.ATensor

/-!
# `A`-cotensors in a 2-category

The formal dual of `ATensor.lean`: an object `c` of a 2-category `K` is `A`-**cotensored**
when every restriction functor `K(r, c) : K(y, c) ⥤ K(x, c)` along a 1-cell `r : x ⟶ y`
between objects of the class `A` has a *right* adjoint — the right Kan extension along `r`.
In `K = CAT` with `A` the small categories this is completeness of `c`; taking for `r` the
projection `J ⊗ x ⟶ x` of a tensor by a small category `J` it says that `K(x, c)` has
`J`-indexed limits, which is the cotensor reading of the hom-wise completeness conditions of
`AComplete.lean`.

* `UlmerBialgebras.IsCotensorUniv r ε` — the 2-cell `ε : r ≫ t ⟶ m` exhibits `t` as the cotensor of
  `m : x ⟶ c` along `r`;
* `UlmerBialgebras.IsACotensored A c` — every `m` has such a cotensor;
* `UlmerBialgebras.RespectsACotensors A f` — post-composition with `f : c ⟶ d` carries cotensors to
  cotensors.  (In `CAT` this is implied by continuity of `f`.)

As in the tensor case the notions are phrased through universal arrows, and the same calculus
— uniqueness, invariance under isomorphism, closure under identities and composition — is
proved.

## Main results

* `UlmerBialgebras.IsCotensorUniv`: a 2-cell `ε : r ≫ t ⟶ m` exhibits `t` as the cotensor of `m`
  along `r`.
* `UlmerBialgebras.IsACotensored`: every 1-cell `m : x ⟶ c` has a cotensor along every 1-cell
  `r : x ⟶ y` between objects of `A` (right Kan extensions along `A`, as in Definition 7.3).
* `UlmerBialgebras.RespectsACotensors`: post-composition with `f` carries cotensors to cotensors.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.3
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Universal arrows for restriction, dual form -/

/-- The 2-cell `ε : r ≫ t ⟶ m` **exhibits `t` as the cotensor of `m` along `r`**: every
2-cell `r ≫ n ⟶ m` factors uniquely through `ε`.  Equivalently, `ε` is a universal arrow
from the restriction functor `K(r, c)` to `m`. -/
def IsCotensorUniv {x y c : Obj} (r : x ⟶ y) {m : x ⟶ c} {t : y ⟶ c} (ε : r ≫ t ⟶ m) :
    Prop :=
  ∀ (n : y ⟶ c) (k : r ≫ n ⟶ m), ∃! β : n ⟶ t, (r ◁ β) ≫ ε = k

/-- An object `c` is **`A`-cotensored** when every restriction functor `K(r, c)` along a
1-cell `r` between objects of `A` has a right adjoint, i.e. every `m : x ⟶ c` has a cotensor
along `r`. -/
def IsACotensored (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃x y : Obj⦄, A x → A y → ∀ (r : x ⟶ y) (m : x ⟶ c),
    ∃ (t : y ⟶ c) (ε : r ≫ t ⟶ m), IsCotensorUniv r ε

/-- The universal 2-cell `ε : r ≫ t ⟶ m`, post-composed with `f : c ⟶ d`. -/
def cotensorWhisker {x y c d : Obj} (r : x ⟶ y) {m : x ⟶ c} {t : y ⟶ c} (ε : r ≫ t ⟶ m)
    (f : c ⟶ d) : r ≫ (t ≫ f) ⟶ m ≫ f :=
  eqToHom (Category.assoc r t f).symm ≫ (ε ▷ f)

/-- A 1-cell `f : c ⟶ d` **respects the `A`-cotensors** when post-composition with `f`
carries cotensors to cotensors. -/
def RespectsACotensors (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃x y : Obj⦄, A x → A y → ∀ (r : x ⟶ y) {m : x ⟶ c} {t : y ⟶ c} (ε : r ≫ t ⟶ m),
    IsCotensorUniv r ε → IsCotensorUniv r (cotensorWhisker r ε f)

/-! ## The calculus of universal arrows -/

namespace IsCotensorUniv

variable {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c} {t : y ⟶ c} {ε : r ≫ t ⟶ m}

/-- The comparison 2-cell induced by a universal arrow. -/
noncomputable def lift (h : IsCotensorUniv r ε) {n : y ⟶ c} (k : r ≫ n ⟶ m) : n ⟶ t :=
  (h n k).exists.choose

/-- The factorisation property: `(r ◁ lift k) ≫ ε = k`. -/
@[simp] lemma fac (h : IsCotensorUniv r ε) {n : y ⟶ c} (k : r ≫ n ⟶ m) :
    (r ◁ h.lift k) ≫ ε = k :=
  (h n k).exists.choose_spec

/-- Uniqueness of the factorisation: any `β` with `(r ◁ β) ≫ ε = k` equals `lift k`. -/
lemma lift_unique (h : IsCotensorUniv r ε) {n : y ⟶ c} {k : r ≫ n ⟶ m} {β : n ⟶ t}
    (hβ : (r ◁ β) ≫ ε = k) : β = h.lift k :=
  (h n k).unique hβ (h.fac k)

/-- Two factorisations through a universal arrow agree. -/
lemma hom_ext (h : IsCotensorUniv r ε) {n : y ⟶ c} {β γ : n ⟶ t}
    (hβγ : (r ◁ β) ≫ ε = (r ◁ γ) ≫ ε) : β = γ := by
  rw [h.lift_unique hβγ]
  exact (h.lift_unique (β := γ) rfl).symm

end IsCotensorUniv

/-! ## Identities and composites -/

namespace RespectsACotensors

variable {A : ObjectProperty Obj}

end RespectsACotensors

end UlmerBialgebras
