module

public import UlmerBialgebras.Basic.HomCat
public import Foundations.CategoryTheory.Factorization.Transport
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Foundations.CategoryTheory.Factorization.RegularExact
public import UlmerBialgebras.Factorization.LiftOFS
public import UlmerBialgebras.Kan.LiftLimits
public import Foundations.CategoryTheory.Limits.PiLimits

/-!
# Representable orthogonal factorization systems, regularity and exactness

A representable form of Section 6 of *A Syntactic Approach to Ulmer's Bialgebras* (not a
numbered part of the current version of the paper; compare the `A`-properties of
Definition 7.2):

* `UlmerBialgebras.RepOFS` — a representable orthogonal factorization system on an
  object `c` of a 2-category: an OFS on every hom-category `K(x, c)`, compatibly with
  pre-composition;
* `UlmerBialgebras.RepPreservesLeft`, `UlmerBialgebras.RepPreservesRight`,
  `UlmerBialgebras.RepPreservesFiniteLimits` — representable preservation of structure by a 1-cell,
  i.e. preservation by all post-composition functors;
* `UlmerBialgebras.Product.repOFS`, `UlmerBialgebras.Inserter.repOFS`,
  `UlmerBialgebras.Equifier.repOFS` — the existence part of the representable form of Theorem 6.3.

Everything is deduced from Section 6 through the comparison equivalences of
`HomCat.lean` and the transport results of `Transport.lean`.

## Main results

* `UlmerBialgebras.RepOFS`: a representable orthogonal factorization system on an object of a
  2-category.
* `UlmerBialgebras.RepPreservesLeft`, `UlmerBialgebras.RepPreservesRight`,
  `UlmerBialgebras.RepPreservesFiniteLimits`: representable preservation of the left class, the
  right class and finite limits.
* `UlmerBialgebras.Product.repOFS`, `UlmerBialgebras.Inserter.repOFS`,
  `UlmerBialgebras.Equifier.repOFS`: the representable orthogonal factorization systems on a
  product, an inserter and an equifier (representable form of the existence part of Theorem 6.3).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 6.3,
  Definition 6.4, Definition 7.2
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w s

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Representable orthogonal factorization systems -/

/-- A **representable orthogonal factorization system** on an object `c`:
an orthogonal factorization system on each hom-category `K(x, c)` such that every
pre-composition functor preserves the left and the right classes. -/
structure RepOFS (c : Obj) where
  /-- The orthogonal factorization system on the hom-category `K(x, c)`. -/
  ofs : ∀ x : Obj, OFS (x ⟶ c)
  /-- Pre-composition preserves the left class. -/
  precomp_E : ∀ {x y : Obj} (f : x ⟶ y) {g h : y ⟶ c} (α : g ⟶ h),
    (ofs y).E α → (ofs x).E (f ◁ α)
  /-- Pre-composition preserves the right class. -/
  precomp_M : ∀ {x y : Obj} (f : x ⟶ y) {g h : y ⟶ c} (α : g ⟶ h),
    (ofs y).M α → (ofs x).M (f ◁ α)

/-- A 1-cell `u : c ⟶ d` **representably preserves the left class**. -/
def RepPreservesLeft {c d : Obj} (Sc : RepOFS c) (Sd : RepOFS d) (u : c ⟶ d) : Prop :=
  ∀ (x : Obj) {g h : x ⟶ c} (α : g ⟶ h), (Sc.ofs x).E α → (Sd.ofs x).E (α ▷ u)

/-- A 1-cell `u : c ⟶ d` **representably preserves the right class**. -/
def RepPreservesRight {c d : Obj} (Sc : RepOFS c) (Sd : RepOFS d) (u : c ⟶ d) : Prop :=
  ∀ (x : Obj) {g h : x ⟶ c} (α : g ⟶ h), (Sc.ofs x).M α → (Sd.ofs x).M (α ▷ u)

/-! ## Representable regularity and exactness -/

/-- A 1-cell representably preserves finite limits. -/
def RepPreservesFiniteLimits {c d : Obj} (u : c ⟶ d) : Prop :=
  ∀ x : Obj, Nonempty (Limits.PreservesFiniteLimits (postcomp x u))

/-! ## Products (representable form of Theorem 6.3 (1)) -/

namespace Product

variable {ι : Type s} {c : ι → Obj} (P : Product c)

/-- The orthogonal factorization system on `K(x, ∏ cᵢ)` obtained from a family of
orthogonal factorization systems on the `K(x, cᵢ)`. -/
noncomputable def homOFS (x : Obj) (S : ∀ i, OFS (x ⟶ c i)) : OFS (x ⟶ P.pt) :=
  (prodOFS S).transport (P.homEquiv x).symm

/-- A 2-cell lies in the left class of `homOFS` iff each of its projections does. -/
lemma homOFS_E (x : Obj) (S : ∀ i, OFS (x ⟶ c i)) {g h : x ⟶ P.pt} (α : g ⟶ h) :
    (P.homOFS x S).E α ↔ ∀ i, (S i).E (α ▷ P.π i) := Iff.rfl

/-- A 2-cell lies in the right class of `homOFS` iff each of its projections does. -/
lemma homOFS_M (x : Obj) (S : ∀ i, OFS (x ⟶ c i)) {g h : x ⟶ P.pt} (α : g ⟶ h) :
    (P.homOFS x S).M α ↔ ∀ i, (S i).M (α ▷ P.π i) := Iff.rfl

/-- **Theorem 6.3 (1), representable form**: the representable orthogonal factorization system on a
product. -/
noncomputable def repOFS (S : ∀ i, RepOFS (c i)) : RepOFS P.pt where
  ofs x := P.homOFS x fun i => (S i).ofs x
  precomp_E := by
    intro x y f g h α hα
    rw [homOFS_E]
    intro i
    have h1 : ((S i).ofs x).E (f ◁ (α ▷ P.π i)) := (S i).precomp_E f _ (hα i)
    rw [Bicategory.Strict.whisker_assoc f α (P.π i)] at h1
    exact (((S i).ofs x).e_conj_iff _ _ _).1 h1
  precomp_M := by
    intro x y f g h α hα
    rw [homOFS_M]
    intro i
    have h1 : ((S i).ofs x).M (f ◁ (α ▷ P.π i)) := (S i).precomp_M f _ (hα i)
    rw [Bicategory.Strict.whisker_assoc f α (P.π i)] at h1
    exact (((S i).ofs x).m_conj_iff _ _ _).1 h1

end Product

/-! ## Inserters (representable form of Theorem 6.3 (2)) -/

namespace Inserter

variable {c d : Obj} {u v : c ⟶ d} (I : Inserter u v)

/-- The orthogonal factorization system on `K(x, Ins(u, v))`. -/
noncomputable def homOFS (x : Obj) (Sc : OFS (x ⟶ c)) (Sd : OFS (x ⟶ d))
    (hu : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.E α → Sd.E ((postcomp x u).map α))
    (hv : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.M α → Sd.M ((postcomp x v).map α)) :
    OFS (x ⟶ I.pt) :=
  (insOFS Sc Sd hu hv).transport (I.homEquiv x).symm

/-- A 2-cell lies in the left class of `homOFS` iff its image under `I.u` does. -/
lemma homOFS_E (x : Obj) (Sc : OFS (x ⟶ c)) (Sd : OFS (x ⟶ d))
    (hu : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.E α → Sd.E ((postcomp x u).map α))
    (hv : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.M α → Sd.M ((postcomp x v).map α))
    {g h : x ⟶ I.pt} (α : g ⟶ h) :
    (I.homOFS x Sc Sd hu hv).E α ↔ Sc.E (α ▷ I.u) := Iff.rfl

/-- A 2-cell lies in the right class of `homOFS` iff its image under `I.u` does. -/
lemma homOFS_M (x : Obj) (Sc : OFS (x ⟶ c)) (Sd : OFS (x ⟶ d))
    (hu : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.E α → Sd.E ((postcomp x u).map α))
    (hv : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.M α → Sd.M ((postcomp x v).map α))
    {g h : x ⟶ I.pt} (α : g ⟶ h) :
    (I.homOFS x Sc Sd hu hv).M α ↔ Sc.M (α ▷ I.u) := Iff.rfl

/-- **Theorem 6.3 (2), representable form**: the representable orthogonal factorization system on an
inserter. -/
noncomputable def repOFS (Sc : RepOFS c) (Sd : RepOFS d)
    (hu : RepPreservesLeft Sc Sd u) (hv : RepPreservesRight Sc Sd v) : RepOFS I.pt where
  ofs x := I.homOFS x (Sc.ofs x) (Sd.ofs x) (fun _ _ α h => hu x α h) (fun _ _ α h => hv x α h)
  precomp_E := by
    intro x y f g h α hα
    rw [homOFS_E]
    have h1 : (Sc.ofs x).E (f ◁ (α ▷ I.u)) := Sc.precomp_E f _ hα
    rw [Bicategory.Strict.whisker_assoc f α I.u] at h1
    exact ((Sc.ofs x).e_conj_iff _ _ _).1 h1
  precomp_M := by
    intro x y f g h α hα
    rw [homOFS_M]
    have h1 : (Sc.ofs x).M (f ◁ (α ▷ I.u)) := Sc.precomp_M f _ hα
    rw [Bicategory.Strict.whisker_assoc f α I.u] at h1
    exact ((Sc.ofs x).m_conj_iff _ _ _).1 h1

end Inserter

/-! ## Equifiers (representable form of Theorem 6.3 (3)) -/

namespace Equifier

variable {c d : Obj} {u v : c ⟶ d} {η θ : u ⟶ v} (E : Equifier η θ)

/-- The orthogonal factorization system on `K(x, Eq(η, θ))`. -/
noncomputable def homOFS (x : Obj) (Sc : OFS (x ⟶ c)) (Sd : OFS (x ⟶ d))
    (hu : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.E α → Sd.E ((postcomp x u).map α))
    (hv : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.M α → Sd.M ((postcomp x v).map α)) :
    OFS (x ⟶ E.pt) :=
  (equifOFS (η := postcompNat x η) (θ := postcompNat x θ) Sc Sd hu hv).transport
    (E.homEquiv x).symm

/-- A 2-cell lies in the left class of `homOFS` iff its image under `E.e` does. -/
lemma homOFS_E (x : Obj) (Sc : OFS (x ⟶ c)) (Sd : OFS (x ⟶ d))
    (hu : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.E α → Sd.E ((postcomp x u).map α))
    (hv : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.M α → Sd.M ((postcomp x v).map α))
    {g h : x ⟶ E.pt} (α : g ⟶ h) :
    (E.homOFS x Sc Sd hu hv).E α ↔ Sc.E (α ▷ E.e) := Iff.rfl

/-- A 2-cell lies in the right class of `homOFS` iff its image under `E.e` does. -/
lemma homOFS_M (x : Obj) (Sc : OFS (x ⟶ c)) (Sd : OFS (x ⟶ d))
    (hu : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.E α → Sd.E ((postcomp x u).map α))
    (hv : ∀ ⦃g h : x ⟶ c⦄ (α : g ⟶ h), Sc.M α → Sd.M ((postcomp x v).map α))
    {g h : x ⟶ E.pt} (α : g ⟶ h) :
    (E.homOFS x Sc Sd hu hv).M α ↔ Sc.M (α ▷ E.e) := Iff.rfl

/-- **Theorem 6.3 (3), representable form**: the representable orthogonal factorization system on an
equifier. -/
noncomputable def repOFS (Sc : RepOFS c) (Sd : RepOFS d)
    (hu : RepPreservesLeft Sc Sd u) (hv : RepPreservesRight Sc Sd v) : RepOFS E.pt where
  ofs x := E.homOFS x (Sc.ofs x) (Sd.ofs x) (fun _ _ α h => hu x α h) (fun _ _ α h => hv x α h)
  precomp_E := by
    intro x y f g h α hα
    rw [homOFS_E]
    have h1 : (Sc.ofs x).E (f ◁ (α ▷ E.e)) := Sc.precomp_E f _ hα
    rw [Bicategory.Strict.whisker_assoc f α E.e] at h1
    exact ((Sc.ofs x).e_conj_iff _ _ _).1 h1
  precomp_M := by
    intro x y f g h α hα
    rw [homOFS_M]
    have h1 : (Sc.ofs x).M (f ◁ (α ▷ E.e)) := Sc.precomp_M f _ hα
    rw [Bicategory.Strict.whisker_assoc f α E.e] at h1
    exact ((Sc.ofs x).m_conj_iff _ _ _).1 h1

end Equifier

end UlmerBialgebras
