module

public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Order.BourbakiWitt

/-!
# Orthogonal factorization systems

Definition 6.1 and Remark 6.2 of *A Syntactic Approach to Ulmer's Bialgebras*.

We formalize orthogonality of two morphisms, the left and right orthogonal classes of a
class of morphisms, and an orthogonal factorization system (OFS) on a category as a pair
of classes `(E, M)` such that every morphism factors as a morphism of `E` followed by a
morphism of `M`, and `M = E⊥`, `E = ⊥M`.

Besides the definitions we prove two structural facts that are used throughout
Section 6 of the paper.

## Main results

* `UlmerBialgebras.OFS`: orthogonal factorization systems (Definition 6.1);
* `UlmerBialgebras.OFS.mk'` (Remark 6.2): factorizations, orthogonality `E ⊥ M` and closure of both
  classes under retracts already give an orthogonal factorization system;
* `UlmerBialgebras.OFS.ext_of_le`: an orthogonal factorization system is determined by *any* pair of
  inclusions, i.e. two OFS `(E₁, M₁)`, `(E₂, M₂)` with `E₁ ⊆ E₂` and `M₁ ⊆ M₂` are equal.
  This is the mechanism behind all the uniqueness statements of Section 6.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.1, Remark 6.2
* [E. Riehl, *Categorical Homotopy Theory*][Riehl2014CategoricalHomotopyTheory],
  Lemma 11.2.3
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Two morphisms `e` and `m` are **orthogonal**, `e ⊥ m`, if every commutative square from
`e` to `m` has a unique diagonal filler. -/
def Orthogonal {a b c d : C} (e : a ⟶ b) (m : c ⟶ d) : Prop :=
  ∀ (f : a ⟶ c) (g : b ⟶ d), f ≫ m = e ≫ g → ∃! h : b ⟶ c, e ≫ h = f ∧ h ≫ m = g

/-- The right orthogonal class `A⊥` of a class `A` of morphisms. -/
def rightOrth (A : MorphismProperty C) : MorphismProperty C :=
  fun _ _ m => ∀ ⦃a b : C⦄ (e : a ⟶ b), A e → Orthogonal e m

/-- The left orthogonal class `⊥A` of a class `A` of morphisms. -/
def leftOrth (A : MorphismProperty C) : MorphismProperty C :=
  fun _ _ e => ∀ ⦃c d : C⦄ (m : c ⟶ d), A m → Orthogonal e m

/-- An **orthogonal factorization system** on a category `C` (Definition 6.1). -/
structure OFS (C : Type u) [Category.{v} C] where
  /-- The left class. -/
  E : MorphismProperty C
  /-- The right class. -/
  M : MorphismProperty C
  /-- Every morphism factors as a morphism of `E` followed by a morphism of `M`. -/
  fact : ∀ ⦃x y : C⦄ (f : x ⟶ y), ∃ (z : C) (e : x ⟶ z) (m : z ⟶ y), E e ∧ M m ∧ e ≫ m = f
  /-- `M = E⊥`. -/
  M_eq : M = rightOrth E
  /-- `E = ⊥M`. -/
  E_eq : E = leftOrth M

namespace OFS

variable (S : OFS C)

/-- Every morphism of the left class is orthogonal to every morphism of the right class. -/
lemma orth {x y z w : C} {e : x ⟶ y} {m : z ⟶ w} (he : S.E e) (hm : S.M m) : Orthogonal e m := by
  rw [S.M_eq] at hm
  exact hm e he

end OFS

/-- The right orthogonal class of any class is stable under retracts. -/
lemma rightOrth_isStableUnderRetracts (A : MorphismProperty C) :
    (rightOrth A).IsStableUnderRetracts := by
  constructor
  intro x y z w m m' hr hm' a b e he f g hsq
  have hsq' : (f ≫ hr.i.left) ≫ m' = e ≫ (g ≫ hr.i.right) := by
    rw [Category.assoc, hr.i_w, ← Category.assoc, hsq, Category.assoc]
  obtain ⟨h', ⟨h1, h2⟩, huniq⟩ := hm' e he (f ≫ hr.i.left) (g ≫ hr.i.right) hsq'
  refine ⟨h' ≫ hr.r.left, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, h1, Category.assoc, hr.retract_left, Category.comp_id]
  · rw [Category.assoc, hr.r_w, ← Category.assoc, h2, Category.assoc, hr.retract_right,
      Category.comp_id]
  · rintro k ⟨k1, k2⟩
    have hk : k ≫ hr.i.left = h' := by
      refine huniq _ ⟨?_, ?_⟩
      · rw [← Category.assoc, k1]
      · rw [Category.assoc, hr.i_w, ← Category.assoc, k2]
    rw [← hk, Category.assoc, hr.retract_left, Category.comp_id]

/-- The left orthogonal class of any class is stable under retracts. -/
lemma leftOrth_isStableUnderRetracts (A : MorphismProperty C) :
    (leftOrth A).IsStableUnderRetracts := by
  constructor
  intro x y z w e e' hr he' a b m hm f g hsq
  have hsq' : (hr.r.left ≫ f) ≫ m = e' ≫ (hr.r.right ≫ g) := by
    rw [Category.assoc, hsq, ← Category.assoc, hr.r_w, Category.assoc]
  obtain ⟨h', ⟨h1, h2⟩, huniq⟩ := he' m hm (hr.r.left ≫ f) (hr.r.right ≫ g) hsq'
  refine ⟨hr.i.right ≫ h', ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← hr.i_w, Category.assoc, h1, ← Category.assoc, hr.retract_left,
      Category.id_comp]
  · rw [Category.assoc, h2, ← Category.assoc, hr.retract_right, Category.id_comp]
  · rintro k ⟨k1, k2⟩
    have hk : hr.r.right ≫ k = h' := by
      refine huniq _ ⟨?_, ?_⟩
      · rw [← Category.assoc, ← hr.r_w, Category.assoc, k1]
      · rw [Category.assoc, k2]
    rw [← hk, ← Category.assoc, hr.retract_right, Category.id_comp]

namespace OFS

variable (S : OFS C)

/-- The left class of an orthogonal factorization system is stable under retracts. -/
lemma e_isStableUnderRetracts : S.E.IsStableUnderRetracts := by
  rw [S.E_eq]; exact leftOrth_isStableUnderRetracts _

/-- The right class of an orthogonal factorization system is stable under retracts. -/
lemma m_isStableUnderRetracts : S.M.IsStableUnderRetracts := by
  rw [S.M_eq]; exact rightOrth_isStableUnderRetracts _

end OFS

/-- Remark 6.2 ([Riehl2014CategoricalHomotopyTheory], Lemma 11.2.3): factorizations,
orthogonality and closure under retracts suffice to produce an orthogonal factorization
system. -/
def OFS.mk' (E M : MorphismProperty C)
    (fact : ∀ ⦃x y : C⦄ (f : x ⟶ y), ∃ (z : C) (e : x ⟶ z) (m : z ⟶ y), E e ∧ M m ∧ e ≫ m = f)
    (orth : ∀ ⦃x y z w : C⦄ (e : x ⟶ y) (m : z ⟶ w), E e → M m → Orthogonal e m)
    (hE : E.IsStableUnderRetracts) (hM : M.IsStableUnderRetracts) : OFS C where
  E := E
  M := M
  fact := fact
  M_eq := by
    ext x y m
    constructor
    · intro hm _ _ e he; exact orth e m he hm
    · intro hm
      obtain ⟨z, e, m', he, hm', hfac⟩ := fact m
      obtain ⟨h, ⟨h1, h2⟩, -⟩ := hm e he (𝟙 x) m' (by rw [Category.id_comp, hfac])
      refine hM.of_retract (f := m) (g := m')
        { i := Arrow.homMk e (𝟙 y) (by simpa using hfac)
          r := Arrow.homMk h (𝟙 y) (by simpa using h2)
          retract := by ext <;> simp [h1] } hm'
  E_eq := by
    ext x y e
    constructor
    · intro he _ _ m hm; exact orth e m he hm
    · intro he
      obtain ⟨z, e', m, he', hm, hfac⟩ := fact e
      obtain ⟨h, ⟨h1, h2⟩, -⟩ := he m hm e' (𝟙 y) (by rw [Category.comp_id, hfac])
      refine hE.of_retract (f := e) (g := e')
        { i := Arrow.homMk (𝟙 x) h (by simpa using h1.symm)
          r := Arrow.homMk (𝟙 x) m (by simpa using hfac.symm)
          retract := by ext <;> simp [h2] } he'

/-! ## Closure properties of the orthogonal classes -/

/-- Every isomorphism is left orthogonal to every morphism. -/
lemma leftOrth_of_isIso (A : MorphismProperty C) {x y : C} (u : x ⟶ y) [IsIso u] :
    leftOrth A u := by
  intro c d m _ f g hsq
  refine ⟨inv u ≫ f, ⟨by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp], ?_⟩, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · rintro k ⟨k1, -⟩
    rw [← k1, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Every isomorphism is right orthogonal to every morphism. -/
lemma rightOrth_of_isIso (A : MorphismProperty C) {x y : C} (u : x ⟶ y) [IsIso u] :
    rightOrth A u := by
  intro a b e _ f g hsq
  refine ⟨g ≫ inv u, ⟨?_, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩, ?_⟩
  · rw [← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rintro k ⟨-, k2⟩
    rw [← k2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The left orthogonal class of any class is closed under composition. -/
lemma leftOrth_comp {A : MorphismProperty C} {x y z : C} {e₁ : x ⟶ y} {e₂ : y ⟶ z}
    (h₁ : leftOrth A e₁) (h₂ : leftOrth A e₂) : leftOrth A (e₁ ≫ e₂) := by
  intro c d m hm f g hsq
  obtain ⟨h, ⟨ha, hb⟩, huniq⟩ := h₁ m hm f (e₂ ≫ g) (by rw [hsq, Category.assoc])
  obtain ⟨k, ⟨ka, kb⟩, kuniq⟩ := h₂ m hm h g hb
  refine ⟨k, ⟨by rw [Category.assoc, ka, ha], kb⟩, ?_⟩
  rintro l ⟨l1, l2⟩
  refine kuniq l ⟨?_, l2⟩
  refine huniq (e₂ ≫ l) ⟨by rw [← Category.assoc, l1], ?_⟩
  rw [Category.assoc, l2]

/-- The right orthogonal class of any class is closed under composition. -/
lemma rightOrth_comp {A : MorphismProperty C} {x y z : C} {m₁ : x ⟶ y} {m₂ : y ⟶ z}
    (h₁ : rightOrth A m₁) (h₂ : rightOrth A m₂) : rightOrth A (m₁ ≫ m₂) := by
  intro a b e he f g hsq
  obtain ⟨k, ⟨ka, kb⟩, kuniq⟩ := h₂ e he (f ≫ m₁) g (by rw [Category.assoc, hsq])
  obtain ⟨h, ⟨ha, hb⟩, huniq⟩ := h₁ e he f k ka.symm
  refine ⟨h, ⟨ha, by rw [← Category.assoc, hb, kb]⟩, ?_⟩
  rintro l ⟨l1, l2⟩
  refine huniq l ⟨l1, ?_⟩
  refine kuniq (l ≫ m₁) ⟨by rw [← Category.assoc, l1], ?_⟩
  rw [Category.assoc, l2]

namespace OFS

variable (S : OFS C)

/-- Every isomorphism belongs to the left class. -/
lemma e_of_isIso {x y : C} (u : x ⟶ y) [IsIso u] : S.E u := by
  rw [S.E_eq]; exact leftOrth_of_isIso _ u

/-- Every isomorphism belongs to the right class. -/
lemma m_of_isIso {x y : C} (u : x ⟶ y) [IsIso u] : S.M u := by
  rw [S.M_eq]; exact rightOrth_of_isIso _ u

/-- The left class is closed under composition. -/
lemma e_comp {x y z : C} {e₁ : x ⟶ y} {e₂ : y ⟶ z} (h₁ : S.E e₁) (h₂ : S.E e₂) :
    S.E (e₁ ≫ e₂) := by
  rw [S.E_eq] at h₁ h₂ ⊢; exact leftOrth_comp h₁ h₂

/-- The right class is closed under composition. -/
lemma m_comp {x y z : C} {m₁ : x ⟶ y} {m₂ : y ⟶ z} (h₁ : S.M m₁) (h₂ : S.M m₂) :
    S.M (m₁ ≫ m₂) := by
  rw [S.M_eq] at h₁ h₂ ⊢; exact rightOrth_comp h₁ h₂

/-- The left class is invariant under conjugation by isomorphisms. -/
lemma e_conj_iff {x y x' y' : C} (i : x' ⟶ x) [IsIso i] (α : x ⟶ y) (j : y ⟶ y') [IsIso j] :
    S.E (i ≫ α ≫ j) ↔ S.E α := by
  constructor
  · intro h
    have := S.e_comp (S.e_comp (S.e_of_isIso (inv i)) h) (S.e_of_isIso (inv j))
    simpa using this
  · intro h
    exact S.e_comp (S.e_of_isIso i) (S.e_comp h (S.e_of_isIso j))

/-- The right class is invariant under conjugation by isomorphisms. -/
lemma m_conj_iff {x y x' y' : C} (i : x' ⟶ x) [IsIso i] (α : x ⟶ y) (j : y ⟶ y') [IsIso j] :
    S.M (i ≫ α ≫ j) ↔ S.M α := by
  constructor
  · intro h
    have := S.m_comp (S.m_comp (S.m_of_isIso (inv i)) h) (S.m_of_isIso (inv j))
    simpa using this
  · intro h
    exact S.m_comp (S.m_of_isIso i) (S.m_comp h (S.m_of_isIso j))

end OFS

/-- An orthogonal factorization system is determined by its two classes. -/
lemma OFS.ext' {S₁ S₂ : OFS C} (hE : S₁.E = S₂.E) (hM : S₁.M = S₂.M) : S₁ = S₂ := by
  cases S₁; cases S₂; dsimp only at hE hM; subst hE; subst hM; rfl

/-- Two orthogonal factorization systems with `E₁ ⊆ E₂` and `M₁ ⊆ M₂` coincide.  This is the
uniqueness principle used in all parts of Theorem 6.3 and of its representable form
(`Representable.lean`). -/
lemma OFS.ext_of_le {S₁ S₂ : OFS C} (hE : S₁.E ≤ S₂.E) (hM : S₁.M ≤ S₂.M) : S₁ = S₂ := by
  have hM' : S₂.M ≤ S₁.M := by
    intro x y m hm
    rw [S₁.M_eq]
    intro a b e he
    exact S₂.orth (hE _ he) hm
  have hMeq : S₁.M = S₂.M := le_antisymm hM hM'
  have hE' : S₂.E ≤ S₁.E := by
    intro x y e he
    rw [S₁.E_eq]
    intro c d m hm
    exact S₂.orth he (hMeq ▸ hm)
  exact OFS.ext' (le_antisymm hE hE') hMeq

end UlmerBialgebras
