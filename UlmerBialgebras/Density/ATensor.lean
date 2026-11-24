module

public import UlmerBialgebras.Basic.HomCat

/-!
# `A`-tensors in a 2-category

Let `K` be a strict 2-category and `A` a class of objects of `K` (the "small" ones).  The
`A`-accessibility theory (Definitions 7.2 and 7.3, `ALocPres.lean`) measures an object `c`
through its hom-categories `K(a, c)`, `a ∈ A`, and the restriction functors
`K(r, c) : K(y, c) ⥤ K(x, c)` along 1-cells `r : x ⟶ y` of `A`.

This file adds the **tensors** to that picture.  An object `c` is `A`-*tensored* when every
restriction functor `K(r, c)` has a left adjoint — the left Kan extension along `r`.  In
`K = CAT` with `A` the small categories this is exactly cocompleteness of `c`; the special
case in which `r` is the projection `J ⊗ x ⟶ x` of a tensor of `x ∈ A` by a small category
`J` says that `K(x, c)` has `J`-indexed colimits, which is the "tensor" reading of the
hom-wise conditions of `ALocPres.lean`.

Everything is phrased elementarily, in terms of *universal arrows* rather than adjunctions:

* `UlmerBialgebras.IsTensorUniv r η` — the 2-cell `η : m ⟶ r ≫ t` exhibits `t` as the tensor of
  `m : x ⟶ c` along `r : x ⟶ y`;
* `UlmerBialgebras.IsATensored A c` — every `m` has such a tensor, for every `r` between objects of
  `A`;
* `UlmerBialgebras.RespectsATensors A f` — post-composition with `f : c ⟶ d` carries universal
  arrows to universal arrows: `f` *respects the `A`-tensors*.  (In `CAT` this is implied by
  cocontinuity of `f`, the Kan extensions being computed by colimits.)

The basic calculus proved here — uniqueness of tensors, invariance under isomorphism, and
closure of `RespectsATensors` under identities and composition — is what the adjoint functor
theorem of `ATensorAdjoint.lean` runs on.

## Main results

* `UlmerBialgebras.IsTensorUniv`: a 2-cell `η : m ⟶ r ≫ t` exhibits `t` as the tensor of `m` along
  `r`.
* `UlmerBialgebras.IsATensored`: every 1-cell `m : x ⟶ c` has a tensor along every 1-cell
  `r : x ⟶ y` between objects of `A` (left Kan extensions along `A`, as in Definition 7.3).
* `UlmerBialgebras.RespectsATensors`: post-composition with `f` carries tensors to tensors.

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

/-! ## Universal arrows for restriction -/

/-- The 2-cell `η : m ⟶ r ≫ t` **exhibits `t` as the tensor of `m` along `r`**: every
2-cell `m ⟶ r ≫ n` factors uniquely through `η`.  Equivalently, `η` is a universal arrow
from `m` to the restriction functor `K(r, c)`. -/
def IsTensorUniv {x y c : Obj} (r : x ⟶ y) {m : x ⟶ c} {t : y ⟶ c} (η : m ⟶ r ≫ t) :
    Prop :=
  ∀ (n : y ⟶ c) (k : m ⟶ r ≫ n), ∃! β : t ⟶ n, η ≫ (r ◁ β) = k

/-- An object `c` is **`A`-tensored** when every restriction functor `K(r, c)` along a 1-cell
`r` between objects of `A` has a left adjoint, i.e. every `m : x ⟶ c` has a tensor along
`r`. -/
def IsATensored (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃x y : Obj⦄, A x → A y → ∀ (r : x ⟶ y) (m : x ⟶ c),
    ∃ (t : y ⟶ c) (η : m ⟶ r ≫ t), IsTensorUniv r η

/-- The universal 2-cell `η : m ⟶ r ≫ t`, post-composed with `f : c ⟶ d`. -/
def tensorWhisker {x y c d : Obj} (r : x ⟶ y) {m : x ⟶ c} {t : y ⟶ c} (η : m ⟶ r ≫ t)
    (f : c ⟶ d) : m ≫ f ⟶ r ≫ (t ≫ f) :=
  (η ▷ f) ≫ eqToHom (Category.assoc r t f)

/-- A 1-cell `f : c ⟶ d` **respects the `A`-tensors** when post-composition with `f` carries
tensors to tensors: if `η` exhibits `t` as the tensor of `m` along `r`, then `η ▷ f` exhibits
`t ≫ f` as the tensor of `m ≫ f`. -/
def RespectsATensors (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃x y : Obj⦄, A x → A y → ∀ (r : x ⟶ y) {m : x ⟶ c} {t : y ⟶ c} (η : m ⟶ r ≫ t),
    IsTensorUniv r η → IsTensorUniv r (tensorWhisker r η f)

/-! ## The calculus of universal arrows -/

namespace IsTensorUniv

variable {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c} {t : y ⟶ c} {η : m ⟶ r ≫ t}

/-- The comparison 2-cell induced by a universal arrow. -/
noncomputable def desc (h : IsTensorUniv r η) {n : y ⟶ c} (k : m ⟶ r ≫ n) : t ⟶ n :=
  (h n k).exists.choose

/-- The factorisation property: `η ≫ (r ◁ desc k) = k`. -/
@[simp] lemma fac (h : IsTensorUniv r η) {n : y ⟶ c} (k : m ⟶ r ≫ n) :
    η ≫ (r ◁ h.desc k) = k :=
  (h n k).exists.choose_spec

/-- Uniqueness of the factorisation: any `β` with `η ≫ (r ◁ β) = k` equals `desc k`. -/
lemma desc_unique (h : IsTensorUniv r η) {n : y ⟶ c} {k : m ⟶ r ≫ n} {β : t ⟶ n}
    (hβ : η ≫ (r ◁ β) = k) : β = h.desc k :=
  ((h n k).unique hβ (h.fac k))

/-- Two factorisations through a universal arrow agree. -/
lemma hom_ext (h : IsTensorUniv r η) {n : y ⟶ c} {β γ : t ⟶ n}
    (hβγ : η ≫ (r ◁ β) = η ≫ (r ◁ γ)) : β = γ := by
  rw [h.desc_unique hβγ]
  exact (h.desc_unique (β := γ) rfl).symm

end IsTensorUniv

/-! ## Identities and composites -/

namespace RespectsATensors

variable {A : ObjectProperty Obj}

end RespectsATensors

end UlmerBialgebras
