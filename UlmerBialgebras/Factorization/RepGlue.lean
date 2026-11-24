module

public import UlmerBialgebras.Factorization.RepRegular
public import Foundations.CategoryTheory.Limits.PiColimits

/-!
# Glue for the representable lifting results of `RepModel.lean`

The representable form of Theorem 6.6 and Corollary 6.7 (`RepModel.lean`) assembles the
object `M^T` of bialgebras out of a product, an inserter and an equifier, and its hypotheses
are stated in terms of the *supports* `M(t)`.  Translating
between the two requires knowing how representable preservation properties behave under

* composition of 1-cells (`UlmerBialgebras.repPreservesLeft_comp` and friends), and
* the 1-cells `P.lift g` induced by a family into a product
  (`UlmerBialgebras.Product.repPreservesLeft_lift` and friends),

together with the fact that the canonical 1-cell `u : Ins(f, g) ⟶ a` out of an inserter
representably preserves the left class, finite limits and — in the exact case — the
coequalizers of kernel pairs.

## Main results

* `UlmerBialgebras.repPreservesLeft_comp`, `UlmerBialgebras.repPreservesRight_comp`,
  `UlmerBialgebras.repPreservesFiniteLimits_comp`: representable preservation of the left class, of
  the right class and of finite limits are closed under composition of 1-cells.
* `UlmerBialgebras.Product.repPreservesLeft_lift`, `UlmerBialgebras.Product.repPreservesRight_lift`,
  `UlmerBialgebras.Product.repPreservesFiniteLimits_lift`: a 1-cell into a product inherits these
  properties from its components.
* `UlmerBialgebras.Inserter.repPreservesLeft_u`, `UlmerBialgebras.Inserter.repPreservesRight_u`: the
  canonical 1-cell out of an inserter representably preserves both classes of the inserter's induced
  factorization system.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.16, Theorem 6.6, Corollary 6.7
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w s

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## Preservation of coequalizers of kernel pairs -/

section OneCat

variable {A : Type*} [Category A] {B : Type*} [Category B] {C : Type*} [Category C]

end OneCat

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Composition of 1-cells -/

/-- Whiskering by a composite 1-cell is whiskering by each, up to the associativity
identifications. -/
lemma whiskerRight_comp_eqToHom {x c d e : Obj} (f : c ⟶ d) (g : d ⟶ e) {k k' : x ⟶ c}
    (α : k ⟶ k') :
    (α ▷ (f ≫ g)) ≫ eqToHom (Category.assoc k' f g).symm
      = eqToHom (Category.assoc k f g).symm ≫ ((α ▷ f) ▷ g) := by
  rw [Bicategory.Strict.whiskerRight_comp]
  simp

/-- Post-composition with a composite 1-cell. -/
def postcompCompIso (x : Obj) {c d e : Obj} (f : c ⟶ d) (g : d ⟶ e) :
    postcomp x (f ≫ g) ≅ postcomp x f ⋙ postcomp x g :=
  NatIso.ofComponents (fun k => eqToIso (Category.assoc k f g).symm) (by
    intro k k' α
    exact whiskerRight_comp_eqToHom f g α)

/-- Representable preservation of the left class is closed under composition of 1-cells. -/
theorem repPreservesLeft_comp {c d e : Obj} {Sc : RepOFS c} {Sd : RepOFS d} {Se : RepOFS e}
    {f : c ⟶ d} {g : d ⟶ e} (hf : RepPreservesLeft Sc Sd f)
    (hg : RepPreservesLeft Sd Se g) : RepPreservesLeft Sc Se (f ≫ g) := by
  intro x k k' α hα
  have h1 : (Se.ofs x).E ((α ▷ f) ▷ g) := hg x _ (hf x α hα)
  rw [Bicategory.Strict.whiskerRight_comp]
  exact ((Se.ofs x).e_conj_iff _ _ _).2 h1

/-- Representable preservation of the right class is closed under composition of 1-cells. -/
theorem repPreservesRight_comp {c d e : Obj} {Sc : RepOFS c} {Sd : RepOFS d} {Se : RepOFS e}
    {f : c ⟶ d} {g : d ⟶ e} (hf : RepPreservesRight Sc Sd f)
    (hg : RepPreservesRight Sd Se g) : RepPreservesRight Sc Se (f ≫ g) := by
  intro x k k' α hα
  have h1 : (Se.ofs x).M ((α ▷ f) ▷ g) := hg x _ (hf x α hα)
  rw [Bicategory.Strict.whiskerRight_comp]
  exact ((Se.ofs x).m_conj_iff _ _ _).2 h1

/-- Representable preservation of finite limits is closed under composition of 1-cells. -/
theorem repPreservesFiniteLimits_comp {c d e : Obj} {f : c ⟶ d} {g : d ⟶ e}
    (hf : RepPreservesFiniteLimits f) (hg : RepPreservesFiniteLimits g) :
    RepPreservesFiniteLimits (f ≫ g) := by
  intro x
  have := (hf x).some
  have := (hg x).some
  exact ⟨preservesFiniteLimits_of_natIso (postcompCompIso x f g).symm⟩

/-! ## Whiskering with a composite -/

section CompIff

variable {x a b e : Obj}

/-- `α ▷ (f₁ ≫ f₂)` lies in the left class of `S` iff `(α ▷ f₁) ▷ f₂` does. -/
lemma e_whiskerRight_comp_iff (S : OFS (x ⟶ e)) {g h : x ⟶ a} (α : g ⟶ h) (f₁ : a ⟶ b)
    (f₂ : b ⟶ e) : S.E (α ▷ (f₁ ≫ f₂)) ↔ S.E ((α ▷ f₁) ▷ f₂) := by
  rw [Bicategory.Strict.whiskerRight_comp]
  exact S.e_conj_iff _ _ _

/-- `α ▷ (f₁ ≫ f₂)` lies in the right class of `S` iff `(α ▷ f₁) ▷ f₂` does. -/
lemma m_whiskerRight_comp_iff (S : OFS (x ⟶ e)) {g h : x ⟶ a} (α : g ⟶ h) (f₁ : a ⟶ b)
    (f₂ : b ⟶ e) : S.M (α ▷ (f₁ ≫ f₂)) ↔ S.M ((α ▷ f₁) ▷ f₂) := by
  rw [Bicategory.Strict.whiskerRight_comp]
  exact S.m_conj_iff _ _ _

/-- A 2-cell whiskered by a threefold composite lies in the left class iff its iterated
whiskering does. -/
lemma e_whiskerRight_comp₂_iff {d : Obj} (S : OFS (x ⟶ e)) {g h : x ⟶ a} (α : g ⟶ h)
    (f₁ : a ⟶ b) (f₂ : b ⟶ d) (f₃ : d ⟶ e) :
    S.E (α ▷ ((f₁ ≫ f₂) ≫ f₃)) ↔ S.E (((α ▷ f₁) ▷ f₂) ▷ f₃) := by
  rw [e_whiskerRight_comp_iff, Bicategory.Strict.whiskerRight_comp α f₁ f₂]
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  exact S.e_conj_iff _ _ _

/-- A 2-cell whiskered by a threefold composite lies in the right class iff its iterated
whiskering does. -/
lemma m_whiskerRight_comp₂_iff {d : Obj} (S : OFS (x ⟶ e)) {g h : x ⟶ a} (α : g ⟶ h)
    (f₁ : a ⟶ b) (f₂ : b ⟶ d) (f₃ : d ⟶ e) :
    S.M (α ▷ ((f₁ ≫ f₂) ≫ f₃)) ↔ S.M (((α ▷ f₁) ▷ f₂) ▷ f₃) := by
  rw [m_whiskerRight_comp_iff, Bicategory.Strict.whiskerRight_comp α f₁ f₂]
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  exact S.m_conj_iff _ _ _

end CompIff

/-! ## 1-cells into a product -/

namespace Product

variable {ι : Type s} {c : ι → Obj} (P : Product c)

/-- Whiskering with the 1-cell induced by a family, followed by a projection. -/
lemma whiskerRight_lift_π {z x : Obj} (g : ∀ i, z ⟶ c i) {k k' : x ⟶ z} (α : k ⟶ k')
    (i : ι) :
    (α ▷ P.lift g) ▷ P.π i
      = eqToHom (by rw [Category.assoc, P.lift_π]) ≫ (α ▷ g i) ≫
        eqToHom (by rw [Category.assoc, P.lift_π] : (k' ≫ P.lift g) ≫ P.π i = k' ≫ g i).symm := by
  rw [Bicategory.whiskerRight_congr α (P.lift_π g i),
    Bicategory.Strict.whiskerRight_comp α (P.lift g) (P.π i)]
  simp

/-- A projection representably preserves the left class of the product factorization
system, by construction. -/
theorem repPreservesLeft_π (S : ∀ i, RepOFS (c i)) (i : ι) :
    RepPreservesLeft (P.repOFS S) (S i) (P.π i) := fun _ _ _ _ hα => hα i

/-- A projection representably preserves the right class of the product factorization
system, by construction. -/
theorem repPreservesRight_π (S : ∀ i, RepOFS (c i)) (i : ι) :
    RepPreservesRight (P.repOFS S) (S i) (P.π i) := fun _ _ _ _ hα => hα i

/-- A projection representably preserves finite limits, as soon as the hom-categories of
the factors have finite limits. -/
theorem repPreservesFiniteLimits_π (hlim : ∀ (x : Obj) (i : ι), HasFiniteLimits (x ⟶ c i))
    (i : ι) : RepPreservesFiniteLimits (P.π i) := fun x => by
  have : ∀ j, HasFiniteLimits (x ⟶ c j) := fun j => hlim x j
  exact ⟨preservesFiniteLimits_of_natIso
    (F := homFunctor P x ⋙ Pi.eval (fun i => (x ⟶ c i)) i) (Iso.refl _)⟩

/-- The 1-cell `P.lift g` into a product (with the product factorization system)
representably preserves the left class when every `g i` does. -/
theorem repPreservesLeft_lift {z : Obj} (Sz : RepOFS z) (S : ∀ i, RepOFS (c i))
    (g : ∀ i, z ⟶ c i) (h : ∀ i, RepPreservesLeft Sz (S i) (g i)) :
    RepPreservesLeft Sz (P.repOFS S) (P.lift g) := by
  intro x k k' α hα
  refine (P.homOFS_E x (fun i => (S i).ofs x) _).2 (fun i => ?_)
  rw [P.whiskerRight_lift_π g α i]
  exact (((S i).ofs x).e_conj_iff _ _ _).2 (h i x α hα)

/-- The 1-cell `P.lift g` into a product (with the product factorization system)
representably preserves the right class when every `g i` does. -/
theorem repPreservesRight_lift {z : Obj} (Sz : RepOFS z) (S : ∀ i, RepOFS (c i))
    (g : ∀ i, z ⟶ c i) (h : ∀ i, RepPreservesRight Sz (S i) (g i)) :
    RepPreservesRight Sz (P.repOFS S) (P.lift g) := by
  intro x k k' α hα
  refine (P.homOFS_M x (fun i => (S i).ofs x) _).2 (fun i => ?_)
  rw [P.whiskerRight_lift_π g α i]
  exact (((S i).ofs x).m_conj_iff _ _ _).2 (h i x α hα)

/-- Comparing the `i`-th component of the comparison functor with post-composition. -/
def liftEvalIso (x : Obj) {z : Obj} (g : ∀ i, z ⟶ c i) (i : ι) :
    (postcomp x (P.lift g) ⋙ homFunctor P x) ⋙ Pi.eval (fun i => (x ⟶ c i)) i
      ≅ postcomp x (g i) :=
  NatIso.ofComponents
    (fun k => eqToIso (show (k ≫ P.lift g) ≫ P.π i = k ≫ g i by rw [Category.assoc, P.lift_π]))
    (by
      intro k k' α
      change ((α ▷ P.lift g) ▷ P.π i) ≫
          eqToHom (show (k' ≫ P.lift g) ≫ P.π i = k' ≫ g i by rw [Category.assoc, P.lift_π])
        = eqToHom (show (k ≫ P.lift g) ≫ P.π i = k ≫ g i by rw [Category.assoc, P.lift_π]) ≫
          (α ▷ g i)
      rw [P.whiskerRight_lift_π g α i]
      simp)

/-- The 1-cell `P.lift g` into a product representably preserves finite limits when every
`g i` does. -/
theorem repPreservesFiniteLimits_lift {z : Obj} (g : ∀ i, z ⟶ c i)
    (h : ∀ i, RepPreservesFiniteLimits (g i)) :
    RepPreservesFiniteLimits (P.lift g) := by
  intro x
  refine ⟨⟨fun J _ _ => ?_⟩⟩
  have : ∀ i, PreservesLimitsOfShape J (postcomp x (g i)) := fun i =>
    ((h i x).some).preservesFiniteLimits J
  have : ∀ i, PreservesLimitsOfShape J
      ((postcomp x (P.lift g) ⋙ homFunctor P x) ⋙ Pi.eval (fun i => (x ⟶ c i)) i) := fun i =>
    preservesLimitsOfShape_of_natIso (P.liftEvalIso x g i).symm
  have : PreservesLimitsOfShape J (postcomp x (P.lift g) ⋙ homFunctor P x) := by
    constructor
    intro F
    constructor
    intro s hs
    exact ⟨piIsLimitOfEval _ (fun i => isLimitOfPreserves
      ((postcomp x (P.lift g) ⋙ homFunctor P x) ⋙ Pi.eval (fun i => (x ⟶ c i)) i) hs)⟩
  exact ⟨fun {F} => preservesLimit_of_reflects_of_preserves (postcomp x (P.lift g))
    (homFunctor P x)⟩

end Product

/-! ## The canonical 1-cell out of an inserter -/

namespace Inserter

variable {a b : Obj} {u v : a ⟶ b} (I : Inserter u v)

/-- The canonical 1-cell out of an inserter representably preserves the left class of the
inserter's own factorization system, by construction. -/
theorem repPreservesLeft_u (Sa : RepOFS a) (Sb : RepOFS b) (hu : RepPreservesLeft Sa Sb u)
    (hv : RepPreservesRight Sa Sb v) :
    RepPreservesLeft (I.repOFS Sa Sb hu hv) Sa I.u := fun _ _ _ _ hα => hα

/-- The canonical 1-cell out of an inserter representably preserves the right class of the
inserter's own factorization system, by construction. -/
theorem repPreservesRight_u (Sa : RepOFS a) (Sb : RepOFS b) (hu : RepPreservesLeft Sa Sb u)
    (hv : RepPreservesRight Sa Sb v) :
    RepPreservesRight (I.repOFS Sa Sb hu hv) Sa I.u := fun _ _ _ _ hα => hα

end Inserter

/-! ## The canonical 1-cell out of an equifier -/

namespace Equifier

variable {a b : Obj} {u v : a ⟶ b} {η θ : u ⟶ v} (E : Equifier η θ)

end Equifier

end UlmerBialgebras
