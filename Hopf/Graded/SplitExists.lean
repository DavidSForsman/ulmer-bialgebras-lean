module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Hopf.Graded.Split

/-!
# Existence of split filtrations adapted to a submodule

Over a field every increasing filtration `F : ℕ → Submodule k V` admits a splitting
(`HopfAlgebra.Graded.Split`), and the splitting can be chosen *adapted* to a prescribed submodule
`A`, in the sense that each projection `pr n` maps `A` into itself. This is what makes the
associated graded object of `A` a graded submodule of the associated graded object of `V`.

The construction is the standard one: one chooses a decreasing family of complements
`E 0 ⊇ E 1 ⊇ ⋯` of the `F n`, each adapted to `A`, and sets `pr n = ρ n - ρ (n-1)` where `ρ n` is
the projection onto `F n` along `E n`.

## Main results

* `HopfAlgebra.Graded.exists_adapted_isCompl` — an adapted complement inside a submodule;
* `HopfAlgebra.Graded.Split.exists_adapted` — the split filtration adapted to `A`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

namespace HopfAlgebra.Graded

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-! ### Complements inside a submodule -/

/-- Inside a submodule `W`, any submodule `X ≤ W` has a complement. -/
theorem exists_isCompl_le {W X : Submodule k V} (hXW : X ≤ W) :
    ∃ E, E ≤ W ∧ X ⊓ E = ⊥ ∧ X ⊔ E = W := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.comap W.subtype X)
  refine ⟨q.map W.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · refine le_antisymm ?_ bot_le
    rintro x ⟨hxX, hxq⟩
    obtain ⟨⟨y, hyW⟩, hyq, rfl⟩ := hxq
    have hy : (⟨y, hyW⟩ : ↥W) ∈ Submodule.comap W.subtype X ⊓ q := ⟨hxX, hyq⟩
    rw [hq.inf_eq_bot] at hy
    simpa using Subtype.ext_iff.1 hy
  · have hmapX : Submodule.map W.subtype (Submodule.comap W.subtype X) = X := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hXW]
    rw [← hmapX, ← Submodule.map_sup, hq.sup_eq_top, Submodule.map_subtype_top]

/-- **Adapted complement.**  Inside a submodule `W`, a submodule `X ≤ W` has a complement `E`
which is adapted to a given `B ≤ W`, in the sense that `B` is the sum of its intersections with
`X` and with `E`. -/
theorem exists_adapted_isCompl {W X B : Submodule k V} (hXW : X ≤ W) (hBW : B ≤ W) :
    ∃ E, E ≤ W ∧ X ⊓ E = ⊥ ∧ X ⊔ E = W ∧ B ≤ (B ⊓ X) ⊔ (B ⊓ E) := by
  obtain ⟨B', hB'B, hB'inf, hB'sup⟩ := exists_isCompl_le (W := B) (X := B ⊓ X) inf_le_left
  obtain ⟨D, hDW, hDinf, hDsup⟩ :=
    exists_isCompl_le (W := W) (X := X ⊔ B') (sup_le hXW (hB'B.trans hBW))
  refine ⟨B' ⊔ D, sup_le (hB'B.trans hBW) hDW, ?_, ?_, ?_⟩
  · refine le_antisymm ?_ bot_le
    rintro x ⟨hxX, hxBD⟩
    obtain ⟨b, hb, d, hd, rfl⟩ := Submodule.mem_sup.1 (show x ∈ B' ⊔ D from hxBD)
    have hd0 : d = 0 := by
      have hmem : d ∈ (X ⊔ B') ⊓ D := by
        refine ⟨?_, hd⟩
        have hbd : d = (b + d) - b := by abel
        rw [hbd]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hxX) (Submodule.mem_sup_right hb)
      rw [hDinf] at hmem
      simpa using hmem
    subst hd0
    have hb' : b ∈ (B ⊓ X) ⊓ B' := ⟨⟨hB'B hb, by simpa using hxX⟩, hb⟩
    rw [hB'inf] at hb'
    simpa using hb'
  · rw [← sup_assoc, hDsup]
  · intro b hb
    have hb2 : b ∈ (B ⊓ X) ⊔ B' := by rw [hB'sup]; exact hb
    rw [Submodule.mem_sup] at hb2
    obtain ⟨c, hc, b', hb', rfl⟩ := hb2
    exact Submodule.add_mem _ (Submodule.mem_sup_left hc)
      (Submodule.mem_sup_right ⟨hB'B hb', Submodule.mem_sup_left hb'⟩)

/-! ### The decreasing family of complements -/

variable (F : ℕ → Submodule k V) (A : Submodule k V)

/-- The complements of the filtration, chosen decreasing and adapted to `A`. -/
noncomputable def compl : ℕ → Submodule k V
  | 0 => (exists_adapted_isCompl (W := (⊤ : Submodule k V)) (X := F 0) (B := A) le_top
      le_top).choose
  | (n + 1) =>
      (exists_adapted_isCompl (W := compl n) (X := F (n + 1) ⊓ compl n) (B := A ⊓ compl n)
        inf_le_right inf_le_right).choose

/-- `compl F A 0` is a complement of `F 0` (`⊓ = ⊥`, `⊔ = ⊤`), and
`A ≤ (A ⊓ F 0) ⊔ (A ⊓ compl F A 0)`. -/
theorem compl_spec_zero :
    F 0 ⊓ compl F A 0 = ⊥ ∧ F 0 ⊔ compl F A 0 = ⊤ ∧
      A ≤ (A ⊓ F 0) ⊔ (A ⊓ compl F A 0) := by
  obtain ⟨-, h1, h2, h3⟩ :=
    (exists_adapted_isCompl (W := (⊤ : Submodule k V)) (X := F 0) (B := A) le_top
        le_top).choose_spec
  exact ⟨h1, h2, h3⟩

/-- `compl F A (n + 1) ≤ compl F A n` is a complement of `F (n + 1) ⊓ compl F A n` inside
`compl F A n`, and `A ⊓ compl F A n` is contained in the sum of its intersections with the two
pieces. -/
theorem compl_spec_succ (n : ℕ) :
    compl F A (n + 1) ≤ compl F A n ∧
      (F (n + 1) ⊓ compl F A n) ⊓ compl F A (n + 1) = ⊥ ∧
      (F (n + 1) ⊓ compl F A n) ⊔ compl F A (n + 1) = compl F A n ∧
      (A ⊓ compl F A n) ≤ ((A ⊓ compl F A n) ⊓ (F (n + 1) ⊓ compl F A n))
        ⊔ ((A ⊓ compl F A n) ⊓ compl F A (n + 1)) :=
  (exists_adapted_isCompl (W := compl F A n) (X := F (n + 1) ⊓ compl F A n)
    (B := A ⊓ compl F A n) inf_le_right inf_le_right).choose_spec

/-- The complements `compl F A n` are antitone in `n`. -/
theorem compl_antitone : Antitone (compl F A) := by
  refine antitone_nat_of_succ_le fun n => (compl_spec_succ F A n).1

variable {F A}

/-- `F n ⊓ compl F A n = ⊥`. -/
theorem compl_inf (n : ℕ) : F n ⊓ compl F A n = ⊥ := by
  induction n with
  | zero => exact (compl_spec_zero F A).1
  | succ n _ =>
      obtain ⟨hle, hinf, -, -⟩ := compl_spec_succ F A n
      refine le_antisymm ?_ bot_le
      rintro x ⟨hxF, hxE⟩
      have : x ∈ (F (n + 1) ⊓ compl F A n) ⊓ compl F A (n + 1) := ⟨⟨hxF, hle hxE⟩, hxE⟩
      rw [hinf] at this
      simpa using this

/-- For monotone `F`, `F n ⊔ compl F A n = ⊤`. -/
theorem compl_sup (hF : Monotone F) (n : ℕ) : F n ⊔ compl F A n = ⊤ := by
  induction n with
  | zero => exact (compl_spec_zero F A).2.1
  | succ n ih =>
      obtain ⟨-, -, hsup, -⟩ := compl_spec_succ F A n
      refine le_antisymm le_top ?_
      rw [← ih]
      refine sup_le (le_trans (hF (Nat.le_succ n)) le_sup_left) ?_
      rw [← hsup]
      exact sup_le (le_trans inf_le_left le_sup_left) le_sup_right

/-- For monotone `F`, `compl F A n` is a complement of `F n`. -/
theorem isCompl_compl (hF : Monotone F) (n : ℕ) : IsCompl (F n) (compl F A n) :=
  ⟨disjoint_iff.2 (compl_inf n), codisjoint_iff.2 (compl_sup hF n)⟩

/-- For monotone `F`, `A ≤ (A ⊓ F n) ⊔ (A ⊓ compl F A n)`. -/
theorem adapted_compl (hF : Monotone F) (n : ℕ) :
    A ≤ (A ⊓ F n) ⊔ (A ⊓ compl F A n) := by
  induction n with
  | zero => exact (compl_spec_zero F A).2.2
  | succ n ih =>
      obtain ⟨-, -, -, hB⟩ := compl_spec_succ F A n
      intro a ha
      have h1 : a ∈ (A ⊓ F n) ⊔ (A ⊓ compl F A n) := ih ha
      rw [Submodule.mem_sup] at h1
      obtain ⟨x, hx, y, hy, rfl⟩ := h1
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.mem_sup_left ⟨hx.1, hF (Nat.le_succ n) hx.2⟩
      · have := hB hy
        rw [Submodule.mem_sup] at this
        obtain ⟨u, hu, v, hv, rfl⟩ := this
        exact Submodule.add_mem _
          (Submodule.mem_sup_left ⟨hu.1.1, hu.2.1⟩)
          (Submodule.mem_sup_right ⟨hv.1.1, hv.2⟩)

/-! ### The projections -/

variable (F A)

/-- The projection onto `F n` along the chosen complement. -/
noncomputable def proj (hF : Monotone F) (n : ℕ) : V →ₗ[k] V :=
  (F n).subtype ∘ₗ Submodule.projectionOnto (F n) (compl F A n) (isCompl_compl hF n)

variable {F A}

/-- `proj n` takes values in `F n`. -/
theorem proj_mem (hF : Monotone F) (n : ℕ) (x : V) : proj F A hF n x ∈ F n :=
  (Submodule.projectionOnto (F n) (compl F A n) (isCompl_compl hF n) x).2

/-- `proj n` is the identity on `F n`. -/
theorem proj_eq_self (hF : Monotone F) {n : ℕ} {x : V} (hx : x ∈ F n) :
    proj F A hF n x = x := by
  rw [proj, LinearMap.comp_apply, Submodule.subtype_apply,
    show x = ((⟨x, hx⟩ : ↥(F n)) : V) from rfl,
    Submodule.projectionOnto_apply_left (isCompl_compl hF n) (⟨x, hx⟩ : ↥(F n))]

/-- `proj n` vanishes on `compl F A n`. -/
theorem proj_eq_zero (hF : Monotone F) {n : ℕ} {x : V} (hx : x ∈ compl F A n) :
    proj F A hF n x = 0 := by
  rw [proj, LinearMap.comp_apply, Submodule.subtype_apply,
    show x = ((⟨x, hx⟩ : ↥(compl F A n)) : V) from rfl,
    Submodule.projectionOnto_apply_right (isCompl_compl hF n) (⟨x, hx⟩ : ↥(compl F A n))]
  rfl

/-- `x - proj n x ∈ compl F A n`. -/
theorem sub_proj_mem_compl (hF : Monotone F) (n : ℕ) (x : V) :
    x - proj F A hF n x ∈ compl F A n := by
  have hx : x ∈ F n ⊔ compl F A n := by rw [compl_sup hF n]; trivial
  rw [Submodule.mem_sup] at hx
  obtain ⟨f, hf, e, he, rfl⟩ := hx
  have : proj F A hF n (f + e) = f := by
    rw [map_add, proj_eq_self hF hf, proj_eq_zero hF he, add_zero]
  rw [this]
  simpa using he

/-- For `m ≤ n`, `proj m (proj n x) = proj m x`. -/
theorem proj_proj (hF : Monotone F) {m n : ℕ} (hmn : m ≤ n) (x : V) :
    proj F A hF m (proj F A hF n x) = proj F A hF m x := by
  have h : proj F A hF n x - x ∈ compl F A m := by
    have := sub_proj_mem_compl (A := A) hF n x
    have h2 : proj F A hF n x - x = -(x - proj F A hF n x) := (neg_sub _ _).symm
    rw [h2]
    exact Submodule.neg_mem _ (compl_antitone F A hmn this)
  have := proj_eq_zero (A := A) hF h
  rw [map_sub, sub_eq_zero] at this
  exact this

/-- For `n ≤ m`, `proj m (proj n x) = proj n x`. -/
theorem proj_proj_of_le (hF : Monotone F) {m n : ℕ} (hmn : n ≤ m) (x : V) :
    proj F A hF m (proj F A hF n x) = proj F A hF n x :=
  proj_eq_self hF (hF hmn (proj_mem hF n x))

/-- `proj n` maps `A` into `A`. -/
theorem proj_mem_of_mem (hF : Monotone F) (n : ℕ) {a : V} (ha : a ∈ A) :
    proj F A hF n a ∈ A := by
  have := adapted_compl (A := A) hF n ha
  rw [Submodule.mem_sup] at this
  obtain ⟨x, hx, y, hy, rfl⟩ := this
  rw [map_add, proj_eq_self hF hx.2, proj_eq_zero hF hy.2, add_zero]
  exact hx.1

/-! ### The split filtration -/

variable (F A)

/-- The graded projections attached to the chosen complements. -/
noncomputable def prAux (hF : Monotone F) : ℕ → (V →ₗ[k] V)
  | 0 => proj F A hF 0
  | (n + 1) => proj F A hF (n + 1) - proj F A hF n

variable {F A}

/-- `prAux 0 x = proj 0 x`. -/
theorem prAux_apply_zero (hF : Monotone F) (x : V) : prAux F A hF 0 x = proj F A hF 0 x := rfl

/-- `prAux (n + 1) x = proj (n + 1) x - proj n x`. -/
theorem prAux_apply_succ (hF : Monotone F) (n : ℕ) (x : V) :
    prAux F A hF (n + 1) x = proj F A hF (n + 1) x - proj F A hF n x := rfl

/-- `prAux n x ∈ F n`. -/
theorem prAux_mem (hF : Monotone F) (n : ℕ) (x : V) : prAux F A hF n x ∈ F n := by
  cases n with
  | zero => exact proj_mem hF 0 x
  | succ n =>
      rw [prAux_apply_succ]
      exact Submodule.sub_mem _ (proj_mem hF (n + 1) x)
        (hF (Nat.le_succ n) (proj_mem hF n x))

/-- For `x ∈ F m` with `m < n`, `prAux n x = 0`. -/
theorem prAux_of_mem_lt (hF : Monotone F) {m n : ℕ} (hmn : m < n) {x : V} (hx : x ∈ F m) :
    prAux F A hF n x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [prAux_apply_succ, proj_eq_self hF (hF (by omega : m ≤ j + 1) hx),
    proj_eq_self hF (hF (by omega : m ≤ j) hx), sub_self]

/-- `proj m (proj n x) = proj (min m n) x`. -/
theorem proj_comp (hF : Monotone F) (m n : ℕ) (x : V) :
    proj F A hF m (proj F A hF n x) = proj F A hF (min m n) x := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, proj_proj hF h]
  · rw [min_eq_right h, proj_proj_of_le hF h]

/-- `prAux m (prAux n x)` is `prAux n x` if `m = n` and `0` otherwise. -/
theorem prAux_prAux (hF : Monotone F) (m n : ℕ) (x : V) :
    prAux F A hF m (prAux F A hF n x) = if m = n then prAux F A hF n x else 0 := by
  rcases m with _ | i <;> rcases n with _ | j
  · rw [ite_eq_left rfl, prAux_apply_zero, prAux_apply_zero, proj_comp, Nat.min_self]
  · rw [ite_eq_right (by omega), prAux_apply_zero, prAux_apply_succ, map_sub, proj_comp, proj_comp,
      Nat.zero_min, Nat.zero_min, sub_self]
  · rw [ite_eq_right (by omega), prAux_apply_zero, prAux_apply_succ, proj_comp, proj_comp,
      Nat.min_zero, Nat.min_zero, sub_self]
  · rw [prAux_apply_succ, prAux_apply_succ, map_sub, map_sub, proj_comp, proj_comp, proj_comp,
      proj_comp]
    rcases lt_trichotomy i j with h | h | h
    · rw [ite_eq_right (by omega), min_eq_left (Nat.succ_le_succ h.le),
        min_eq_left (Nat.succ_le_of_lt h), min_eq_left (Nat.le_succ_of_le h.le), min_eq_left h.le]
      abel
    · subst h
      rw [ite_eq_left rfl, min_self, min_eq_right (Nat.le_succ i), min_eq_left (Nat.le_succ i),
        min_self]
      abel
    · rw [ite_eq_right (by omega), min_eq_right (Nat.succ_le_succ h.le),
        min_eq_right (Nat.le_succ_of_le h.le), min_eq_right (Nat.succ_le_of_lt h),
        min_eq_right h.le]
      abel

/-- `∑ i ∈ Finset.range (n + 1), prAux i x = proj n x`. -/
theorem sum_prAux (hF : Monotone F) (n : ℕ) (x : V) :
    ∑ i ∈ Finset.range (n + 1), prAux F A hF i x = proj F A hF n x := by
  induction n with
  | zero => simp [prAux_apply_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, prAux_apply_succ]
      abel

/-- **Existence of an adapted split filtration.**  Every increasing filtration of a vector space
admits a splitting whose projections preserve a prescribed subspace. -/
theorem Split.exists_adapted (hF : Monotone F) :
    ∃ S : Split k V, S.F = F ∧ ∀ (n : ℕ), ∀ a ∈ A, S.pr n a ∈ A := by
  refine ⟨{ F := F
            pr := prAux F A hF
            mono := hF
            pr_mem := prAux_mem hF
            pr_of_mem_lt := fun hmn x hx => prAux_of_mem_lt hF hmn hx
            pr_pr := prAux_prAux hF
            sum_pr := fun n x hx => by
              rw [sum_prAux hF n x, proj_eq_self hF hx] }, rfl, ?_⟩
  intro n a ha
  dsimp only
  cases n with
  | zero => exact proj_mem_of_mem hF 0 ha
  | succ n =>
      rw [prAux_apply_succ]
      exact Submodule.sub_mem _ (proj_mem_of_mem hF (n + 1) ha) (proj_mem_of_mem hF n ha)

/-! ### Splittings adapted to a counit -/

section Counit

variable (e : V →ₗ[k] k) (w : V)

/-- The projection `x ↦ x - e x • w`; for `e w = 1` it projects onto the kernel of `e`. -/
noncomputable def counitProj : V →ₗ[k] V := LinearMap.id - e.smulRight w

/-- `counitProj e w` is `x ↦ x - e x • w`. -/
theorem counitProj_apply (x : V) : counitProj e w x = x - e x • w := rfl

variable {e w}

/-- For `e w = 1`, `counitProj e w` takes values in the kernel of `e`. -/
theorem counit_counitProj (hew : e w = 1) (x : V) : e (counitProj e w x) = 0 := by
  rw [counitProj_apply, map_sub, map_smul, hew, smul_eq_mul, mul_one, sub_self]

/-- `counitProj e w` is the identity on the kernel of `e`. -/
theorem counitProj_of_counit_eq_zero {x : V} (hx : e x = 0) : counitProj e w x = x := by
  rw [counitProj_apply, hx, zero_smul, sub_zero]

/-- For `e w = 1`, the line spanned by `w` meets the kernel of `e` trivially. -/
theorem span_inf_ker_eq_bot (hew : e w = 1) : Submodule.span k {w} ⊓ LinearMap.ker e = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨hxF, hxe⟩ := hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxF
  have hce : e (c • w) = 0 := hxe
  rw [map_smul, hew, smul_eq_mul, mul_one] at hce
  simp [hce]

variable (e w)

/-- The projections adapted to `e`: `x ↦ e x • w` in degree zero, and `T.pr n` after
`counitProj e w` in positive degrees. -/
noncomputable def adaptedPr (T : Split k V) (n : ℕ) : V →ₗ[k] V :=
  if n = 0 then e.smulRight w else T.pr n ∘ₗ counitProj e w

variable {e w}

/-- In degree zero, the adapted projection is `x ↦ e x • w`. -/
theorem adaptedPr_zero (T : Split k V) (x : V) : adaptedPr e w T 0 x = e x • w := by
  simp [adaptedPr]

/-- In positive degree `n`, the adapted projection is `T.pr n` after `counitProj e w`. -/
theorem adaptedPr_pos (T : Split k V) {n : ℕ} (hn : 1 ≤ n) (x : V) :
    adaptedPr e w T n x = T.pr n (counitProj e w x) := by
  simp [adaptedPr, show ¬ n = 0 by omega]

/-- The adapted projections are orthogonal idempotents, if those of `T` take values in the
kernel of `e`. -/
theorem adaptedPr_pr (T : Split k V) (hew : e w = 1) (hTe : ∀ n x, e (T.pr n x) = 0)
    (m n : ℕ) (x : V) :
    adaptedPr e w T m (adaptedPr e w T n x) = if m = n then adaptedPr e w T n x else 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm <;> rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hm; subst hn
    rw [ite_eq_left rfl, adaptedPr_zero, adaptedPr_zero, map_smul, hew, smul_eq_mul, mul_one]
  · rw [ite_eq_right (by omega), hm, adaptedPr_zero, adaptedPr_pos T hn, hTe, zero_smul]
  · rw [ite_eq_right (by omega), hn, adaptedPr_zero, adaptedPr_pos T hm]
    have : counitProj e w (e x • w) = 0 := by
      rw [counitProj_apply, map_smul, hew, smul_eq_mul, mul_one, sub_self]
    rw [this, map_zero]
  · rw [adaptedPr_pos T hm, adaptedPr_pos T hn, counitProj_of_counit_eq_zero (hTe n _), T.pr_pr]

/-- The adapted projections sum to `x` once those of `T` sum to `counitProj e w x` and kill
everything in degree zero. -/
theorem sum_adaptedPr (T : Split k V) (hT0 : ∀ x, T.pr 0 x = 0) (n : ℕ) (x : V)
    (hsum : ∑ i ∈ Finset.range (n + 1), T.pr i (counitProj e w x) = counitProj e w x) :
    ∑ i ∈ Finset.range (n + 1), adaptedPr e w T i x = x := by
  have h1 : ∑ i ∈ Finset.range (n + 1), adaptedPr e w T i x
      = (∑ i ∈ Finset.range n, T.pr (i + 1) (counitProj e w x)) + e x • w := by
    rw [Finset.sum_range_succ' (fun i => adaptedPr e w T i x) n, adaptedPr_zero]
    congr 1
  have h2 : ∑ i ∈ Finset.range (n + 1), T.pr i (counitProj e w x)
      = (∑ i ∈ Finset.range n, T.pr (i + 1) (counitProj e w x)) := by
    rw [Finset.sum_range_succ' (fun i => T.pr i (counitProj e w x)) n, hT0, add_zero]
  rw [h1, ← h2, hsum, counitProj_apply]
  abel

end Counit

/-- **Existence of a split filtration adapted to a submodule and to a linear form.**  If the
degree-zero part of the filtration is the line spanned by an element `w` with `e w = 1`, then the
splitting can be chosen so that all the projections of positive degree take values in the kernel
of `e`, while still preserving a prescribed submodule `A` containing `w`.

In the intended application `e` is the counit of a Hopf algebra, `w = 1`, `F` is the coradical
filtration of the irreducible component of the unit, and `A` is a sub-bialgebra. -/
theorem Split.exists_adapted_of_counit (hF : Monotone F) (e : V →ₗ[k] k) (w : V)
    (hew : e w = 1) (hF0 : F 0 = Submodule.span k {w}) (hwF : ∀ n, w ∈ F n) (hwA : w ∈ A) :
    ∃ S : Split k V, S.F = F ∧ (∀ n, ∀ a ∈ A, S.pr n a ∈ A) ∧
      (∀ n, 1 ≤ n → ∀ x, e (S.pr n x) = 0) ∧ (∀ x, S.pr 0 x = e x • w) := by
  classical
  -- Split the filtration `Fe n = F n ∩ ker e` adapted to `A ∩ ker e`, and project to it along
  -- `x ↦ x - e x • w`; in degree `0` the projection is `x ↦ e x • w`.
  set Fe : ℕ → Submodule k V := fun n => F n ⊓ LinearMap.ker e with hFedef
  have hFe : Monotone Fe := fun m n hmn => inf_le_inf_right _ (hF hmn)
  obtain ⟨T, hTF, hTA⟩ := Split.exists_adapted (F := Fe) (A := A ⊓ LinearMap.ker e) hFe
  have hπF : ∀ (n : ℕ) (x : V), x ∈ F n → counitProj e w x ∈ Fe n := fun n x hx =>
    ⟨Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hwF n)), by
      simpa using counit_counitProj hew x⟩
  have hTmem : ∀ (n : ℕ) (x : V), T.pr n x ∈ Fe n := by
    intro n x
    have := T.pr_mem n x
    rwa [hTF] at this
  have hTe : ∀ (n : ℕ) (x : V), e (T.pr n x) = 0 := fun n x => (hTmem n x).2
  have hT0 : ∀ x : V, T.pr 0 x = 0 := by
    intro x
    have := hTmem 0 x
    rw [show Fe 0 = ⊥ by rw [hFedef]; dsimp only; rw [hF0]; exact span_inf_ker_eq_bot hew] at this
    simpa using this
  have hpr_mem : ∀ (n : ℕ) (x : V), adaptedPr e w T n x ∈ F n := by
    intro n x
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [adaptedPr_zero]
      exact Submodule.smul_mem _ _ (hwF 0)
    · rw [adaptedPr_pos T hn]
      exact (hTmem n _).1
  have hpr_of_mem_lt : ∀ {m n : ℕ}, m < n → ∀ x ∈ F m, adaptedPr e w T n x = 0 := by
    intro m n hmn x hx
    rw [adaptedPr_pos T (by omega)]
    have hmem : counitProj e w x ∈ Fe m := hπF m x hx
    rw [← hTF] at hmem
    exact T.pr_of_mem_lt hmn _ hmem
  have hsum : ∀ (n : ℕ) (x : V), x ∈ F n →
      ∑ i ∈ Finset.range (n + 1), adaptedPr e w T i x = x := fun n x hx =>
    sum_adaptedPr T hT0 n x (T.sum_pr n _ (by rw [hTF]; exact hπF n x hx))
  -- The axioms of a splitting, then `A` and `ker e` preserved.
  refine ⟨{ F := F, pr := adaptedPr e w T, mono := hF, pr_mem := hpr_mem,
            pr_of_mem_lt := fun hmn x hx => hpr_of_mem_lt hmn x hx,
            pr_pr := adaptedPr_pr T hew hTe, sum_pr := hsum }, rfl, ?_, ?_, adaptedPr_zero T⟩
  · intro n a ha
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      dsimp only
      rw [adaptedPr_zero]
      exact Submodule.smul_mem _ _ hwA
    · dsimp only
      rw [adaptedPr_pos T hn]
      have hmem : counitProj e w a ∈ A ⊓ LinearMap.ker e :=
        ⟨Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hwA), by
          simpa using counit_counitProj hew a⟩
      exact (hTA n _ hmem).1
  · intro n hn x
    dsimp only
    rw [adaptedPr_pos T hn]
    exact hTe n _

end HopfAlgebra.Graded
