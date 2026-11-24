module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Hopf.Graded.Split
public import Hopf.Coradical.TensorSub

/-!
# The associated graded Hopf algebra of a filtered Hopf algebra

Mathlib has no associated-graded construction for filtered algebras.  This file builds the one
needed for Sweedler's freeness theorem: given a Hopf algebra `H` over a field `k` and an
increasing filtration `F` of a sub-bialgebra of `H` which is

* multiplicative (`F m * F n ⊆ F (m+n)`, `1 ∈ F 0`),
* comultiplicative (`Δ (F n) ⊆ Σ_{i+j=n} F i ⊗ F j`),
* antipode-stable,
* almost commutative (`[F m, F n] ⊆ F (m+n-1)`),

together with a *splitting* (`HopfAlgebra.Graded.Split`), the associated graded object
`HopfAlgebra.Graded.HopfSplit.Gr` is a connected graded commutative Hopf `k`-algebra.

Carrying the splitting explicitly means the graded object is `⨁ n, C n` with `C n` an honest
complement of `F (n-1)` in `F n`, so that *no* quotient is formed and there are no
well-definedness obligations; all the axioms reduce to statements about the projections `pr n`.

## Main results

* `HopfAlgebra.Graded.HopfSplit`: a split filtration of a Hopf algebra which is connected,
  multiplicative, comultiplicative, antipode-stable and almost commutative.
* `HopfAlgebra.Graded.HopfSplit.Gr`: the associated graded object `⨁ₙ Cₙ`, with its `CommRing` and
  `Algebra k` instances.
* `HopfAlgebra.Graded.HopfSplit.emb_injective`: the embedding `S.emb : S.Gr →ₗ[k] H` is injective.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [J. W. Milnor, J. C. Moore, *On the structure of Hopf algebras*][Milnor-Moore]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra

namespace HopfAlgebra.Graded

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-- A split filtration of a Hopf algebra which is multiplicative, comultiplicative,
antipode-stable and almost commutative. -/
structure HopfSplit (k H : Type u) [Field k] [Ring H] [HopfAlgebra k H] extends Split k H where
  /-- the filtration is connected: its degree-zero part is the line spanned by the unit -/
  F_zero : F 0 = Submodule.span k {(1 : H)}
  /-- the filtration is multiplicative -/
  mul_mem : ∀ m n, F m * F n ≤ F (m + n)
  /-- the filtration is comultiplicative -/
  comul_mem : ∀ (n : ℕ), ∀ x ∈ F n,
    comul (R := k) x ∈ ⨆ i ∈ Finset.range (n + 1), Coalgebra.Coradical.tens (F i) (F (n - i))
  /-- the filtration is antipode-stable -/
  antipode_mem : ∀ (n : ℕ), ∀ x ∈ F n, HopfAlgebra.antipode (R := k) x ∈ F n
  /-- the complements of positive degree lie in the augmentation ideal -/
  counit_pr : ∀ (n : ℕ), 1 ≤ n → ∀ x : H, counit (R := k) (pr n x) = 0
  /-- commutators drop the filtration degree -/
  commutator_mem : ∀ (m n : ℕ), ∀ x ∈ F m, ∀ y ∈ F n, x * y - y * x ∈ F (m + n - 1)

namespace HopfSplit

variable (S : HopfSplit k H)

/-- The homogeneous complements of the filtration. -/
def C (n : ℕ) : Submodule k H := S.toSplit.C n

/-- The projection `pr n` takes values in `Cₙ`. -/
theorem pr_mem_C (n : ℕ) (x : H) : S.pr n x ∈ S.C n := S.toSplit.pr_mem_C n x

/-- `Cₙ ⊆ Fₙ`. -/
theorem c_le_f (n : ℕ) : S.C n ≤ S.F n := S.toSplit.c_le_f n

/-- `1 ∈ F₀`. -/
theorem one_mem : (1 : H) ∈ S.F 0 := by
  rw [S.F_zero]; exact Submodule.subset_span rfl

/-- Elements of filtration degree `0` are scalars. -/
theorem exists_smul_one_of_mem_F_zero {x : H} (hx : x ∈ S.F 0) : ∃ c : k, x = c • (1 : H) := by
  rw [S.F_zero, Submodule.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

/-- Elements of `F₀` commute with each other. -/
theorem mul_comm_of_mem_F_zero {x y : H} (hx : x ∈ S.F 0) (hy : y ∈ S.F 0) : x * y = y * x := by
  obtain ⟨c, rfl⟩ := S.exists_smul_one_of_mem_F_zero hx
  obtain ⟨d, rfl⟩ := S.exists_smul_one_of_mem_F_zero hy
  have h : ∀ e : k, e • (1 : H) = algebraMap k H e := fun e =>
    (Algebra.algebraMap_eq_smul_one e).symm
  rw [h, h, ← map_mul, ← map_mul, mul_comm]

/-! ### Two basic consequences of the axioms -/

/-- Replacing an element of `F m` by its top graded component does not change the top graded
component of a product. -/
theorem pr_mul_left {m n : ℕ} {u : H} (hu : u ∈ S.F m) {v : H} (hv : v ∈ S.F n) :
    S.pr (m + n) ((u - S.pr m u) * v) = 0 := by
  cases m with
  | zero => simp [S.pr_zero_of_mem_F_zero hu]
  | succ j =>
      have h1 : u - S.pr (j + 1) u ∈ S.F j := S.sub_pr_mem hu
      have h2 : (u - S.pr (j + 1) u) * v ∈ S.F (j + n) :=
        S.mul_mem j n (Submodule.mul_mem_mul h1 hv)
      exact S.pr_of_mem_lt (by omega) _ h2

/-- Replacing the right factor `v ∈ F n` by its top graded component `pr n v` does not
change the top graded component `pr (m + n)` of a product with `u ∈ F m`. -/
theorem pr_mul_right {m n : ℕ} {u : H} (hu : u ∈ S.F m) {v : H} (hv : v ∈ S.F n) :
    S.pr (m + n) (u * (v - S.pr n v)) = 0 := by
  cases n with
  | zero => simp [S.pr_zero_of_mem_F_zero hv]
  | succ j =>
      have h1 : v - S.pr (j + 1) v ∈ S.F j := S.sub_pr_mem hv
      have h2 : u * (v - S.pr (j + 1) v) ∈ S.F (m + j) :=
        S.mul_mem m j (Submodule.mul_mem_mul hu h1)
      exact S.pr_of_mem_lt (by omega) _ h2

/-- **The graded product is well behaved**: the top graded component of a product only depends on
the top graded components of the factors. -/
theorem pr_mul_pr {m n : ℕ} {u : H} (hu : u ∈ S.F m) {v : H} (hv : v ∈ S.F n) :
    S.pr (m + n) (S.pr m u * S.pr n v) = S.pr (m + n) (u * v) := by
  have h1 : S.pr (m + n) (S.pr m u * v) = S.pr (m + n) (u * v) := by
    have := S.pr_mul_left hu hv
    rw [sub_mul, map_sub, sub_eq_zero] at this
    exact this.symm
  have h2 : S.pr (m + n) (S.pr m u * S.pr n v) = S.pr (m + n) (S.pr m u * v) := by
    have := S.pr_mul_right (S.pr_mem m u) hv
    rw [mul_sub, map_sub, sub_eq_zero] at this
    exact this.symm
  rw [h2, h1]

/-! ### The carrier of the associated graded object -/

/-- The carrier of the associated graded Hopf algebra: the direct sum of the homogeneous
complements. -/
def Gr (S : HopfSplit k H) : Type u := DirectSum ℕ (fun n => ↥(S.C n))

/-- The additive group structure of `Gr = ⨁ₙ Cₙ`. -/
instance : AddCommGroup S.Gr :=
  inferInstanceAs (AddCommGroup (DirectSum ℕ (fun n => ↥(S.C n))))

/-- The `k`-module structure of `Gr = ⨁ₙ Cₙ`. -/
instance : Module k S.Gr :=
  inferInstanceAs (Module k (DirectSum ℕ (fun n => ↥(S.C n))))

/-- The inclusion of the `n`-th homogeneous piece. -/
def ofC (n : ℕ) : ↥(S.C n) →ₗ[k] S.Gr := DirectSum.lof k ℕ (fun i => ↥(S.C i)) n

/-- The `n`-th graded component of an element of `H`. -/
def cmp (n : ℕ) : H →ₗ[k] S.Gr :=
  (S.ofC n) ∘ₗ (LinearMap.codRestrict (S.C n) (S.pr n) (S.pr_mem_C n))

/-- The inclusion of the associated graded object into `H` (a `k`-linear injection). -/
def emb : S.Gr →ₗ[k] H := DirectSum.toModule k ℕ H (fun n => (S.C n).subtype)

/-- `emb (ofC n a) = a`. -/
@[simp] theorem emb_ofC (n : ℕ) (a : ↥(S.C n)) : S.emb (S.ofC n a) = (a : H) :=
  DirectSum.toModule_lof k (φ := fun i => (S.C i).subtype) n a

/-- `emb (cmp n x) = pr n x`. -/
@[simp] theorem emb_cmp (n : ℕ) (x : H) : S.emb (S.cmp n x) = S.pr n x :=
  S.emb_ofC n _

/-- For `x ∈ Cₙ`, `cmp n x` is `x` placed in degree `n`. -/
theorem cmp_eq_ofC {n : ℕ} {x : H} (hx : x ∈ S.C n) : S.cmp n x = S.ofC n ⟨x, hx⟩ := by
  have : S.pr n x = x := S.toSplit.pr_eq_self_of_mem_C hx
  simp only [cmp, LinearMap.comp_apply]
  congr 1
  exact Subtype.ext this

/-- `ofC n a = cmp n a`. -/
theorem ofC_eq_cmp (n : ℕ) (a : ↥(S.C n)) : S.ofC n a = S.cmp n (a : H) :=
  (S.cmp_eq_ofC a.2).symm

/-- `cmp n x` depends only on `pr n x`. -/
theorem cmp_eq_cmp_of_pr_eq {n : ℕ} {x y : H} (h : S.pr n x = S.pr n y) :
    S.cmp n x = S.cmp n y := by
  simp only [cmp, LinearMap.comp_apply]
  congr 1
  exact Subtype.ext h

/-- `cmp n (pr n x) = cmp n x`. -/
@[simp] theorem cmp_pr (n : ℕ) (x : H) : S.cmp n (S.pr n x) = S.cmp n x :=
  S.cmp_eq_cmp_of_pr_eq (S.pr_self n x)

/-- Induction principle for the associated graded object. -/
@[elab_as_elim] theorem induction_on {motive : S.Gr → Prop} (x : S.Gr) (h0 : motive 0)
    (hof : ∀ (n : ℕ) (a : ↥(S.C n)), motive (S.ofC n a))
    (hadd : ∀ x y, motive x → motive y → motive (x + y)) : motive x :=
  DirectSum.induction_on (β := fun n => ↥(S.C n)) x h0 hof hadd

/-! ### The graded product -/

/-- The graded product on homogeneous pieces. -/
def mulAux (m n : ℕ) : ↥(S.C m) →ₗ[k] ↥(S.C n) →ₗ[k] S.Gr :=
  LinearMap.compr₂ ((LinearMap.mul k H).compl₁₂ (S.C m).subtype (S.C n).subtype) (S.cmp (m + n))

/-- Right multiplication by a homogeneous element. -/
def mulRight (n : ℕ) : ↥(S.C n) →ₗ[k] S.Gr →ₗ[k] S.Gr :=
  (DirectSum.toModule k ℕ (↥(S.C n) →ₗ[k] S.Gr) (fun m => S.mulAux m n)).flip

/-- The graded product. -/
def gmul : S.Gr →ₗ[k] S.Gr →ₗ[k] S.Gr :=
  (DirectSum.toModule k ℕ (S.Gr →ₗ[k] S.Gr) (fun i => S.mulRight i)).flip

/-- `gmul (ofC m a) (ofC n b) = cmp (m + n) (a * b)`. -/
theorem gmul_ofC (m n : ℕ) (a : ↥(S.C m)) (b : ↥(S.C n)) :
    S.gmul (S.ofC m a) (S.ofC n b) = S.cmp (m + n) ((a : H) * (b : H)) := by
  have hn := DirectSum.toModule_lof k (φ := fun i => S.mulRight i) n b
  have hm := DirectSum.toModule_lof k (φ := fun i => S.mulAux i n) m a
  exact (congr($hn (S.ofC m a))).trans congr($hm b)

/-- The graded multiplication of `Gr`. -/
instance : Mul S.Gr := ⟨fun x y => S.gmul x y⟩

/-- The product on `Gr` is `gmul`. -/
theorem mul_def (x y : S.Gr) : x * y = S.gmul x y := rfl

/-- The unit of `Gr` is `cmp 0 1`. -/
instance : One S.Gr := ⟨S.cmp 0 1⟩

/-- `1 = cmp 0 1` in `Gr`. -/
theorem one_def : (1 : S.Gr) = S.cmp 0 1 := rfl

/-- **The key computation**: the graded product of two graded components. -/
theorem cmp_mul_cmp {m n : ℕ} {u : H} (hu : u ∈ S.F m) {v : H} (hv : v ∈ S.F n) :
    (S.cmp m u) * (S.cmp n v) = S.cmp (m + n) (u * v) := by
  have h1 : S.cmp m u = S.ofC m ⟨S.pr m u, S.pr_mem_C m u⟩ := rfl
  have h2 : S.cmp n v = S.ofC n ⟨S.pr n v, S.pr_mem_C n v⟩ := rfl
  rw [mul_def, h1, h2, S.gmul_ofC]
  exact S.cmp_eq_cmp_of_pr_eq (S.pr_mul_pr hu hv)

/-! ### The ring structure -/

/-- `0 * x = 0` in `Gr`. -/
theorem zero_mul' (x : S.Gr) : (0 : S.Gr) * x = 0 := by
  rw [mul_def, map_zero, LinearMap.zero_apply]

/-- `x * 0 = 0` in `Gr`. -/
theorem mul_zero' (x : S.Gr) : x * (0 : S.Gr) = 0 := by
  rw [mul_def, map_zero]

/-- Right distributivity in `Gr`. -/
theorem add_mul' (x y z : S.Gr) : (x + y) * z = x * z + y * z := by
  rw [mul_def, mul_def, mul_def, map_add, LinearMap.add_apply]

/-- Left distributivity in `Gr`. -/
theorem mul_add' (x y z : S.Gr) : x * (y + z) = x * y + x * z := by
  rw [mul_def, mul_def, mul_def, map_add]

/-- Associativity on homogeneous elements. -/
theorem cmp_mul_assoc {m n p : ℕ} {u v w : H} (hu : u ∈ S.F m) (hv : v ∈ S.F n)
    (hw : w ∈ S.F p) :
    (S.cmp m u * S.cmp n v) * S.cmp p w = S.cmp m u * (S.cmp n v * S.cmp p w) := by
  rw [S.cmp_mul_cmp hu hv, S.cmp_mul_cmp (S.mul_mem m n (Submodule.mul_mem_mul hu hv)) hw,
    S.cmp_mul_cmp hv hw, S.cmp_mul_cmp hu (S.mul_mem n p (Submodule.mul_mem_mul hv hw)),
    mul_assoc, Nat.add_assoc]

/-- Associativity in `Gr` when the first two factors are homogeneous. -/
theorem gmul_assoc₁ {m n : ℕ} (a : ↥(S.C m)) (b : ↥(S.C n)) (z : S.Gr) :
    (S.ofC m a * S.ofC n b) * z = S.ofC m a * (S.ofC n b * z) := by
  refine S.induction_on z ?_ (fun p c => ?_) (fun z₁ z₂ h₁ h₂ => ?_)
  · rw [S.mul_zero', S.mul_zero', S.mul_zero']
  · rw [S.ofC_eq_cmp, S.ofC_eq_cmp, S.ofC_eq_cmp]
    exact S.cmp_mul_assoc (S.c_le_f m a.2) (S.c_le_f n b.2) (S.c_le_f p c.2)
  · rw [S.mul_add', h₁, h₂, S.mul_add', S.mul_add']

/-- Associativity in `Gr` when the first factor is homogeneous. -/
theorem gmul_assoc₂ {m : ℕ} (a : ↥(S.C m)) (y z : S.Gr) :
    (S.ofC m a * y) * z = S.ofC m a * (y * z) := by
  refine S.induction_on y ?_
    (fun n b => S.gmul_assoc₁ a b z) (fun y₁ y₂ h₁ h₂ => ?_)
  · rw [S.mul_zero', S.zero_mul', S.mul_zero']
  · rw [S.mul_add', S.add_mul', h₁, h₂, S.add_mul', S.mul_add']

/-- The product of `Gr` is associative. -/
theorem gmul_assoc (x y z : S.Gr) : x * y * z = x * (y * z) := by
  refine S.induction_on x ?_
    (fun m a => S.gmul_assoc₂ a y z) (fun x₁ x₂ h₁ h₂ => ?_)
  · rw [S.zero_mul', S.zero_mul', S.zero_mul']
  · rw [S.add_mul', S.add_mul', h₁, h₂, S.add_mul']

/-- For `u ∈ F m` and `v ∈ F n`, the graded components `cmp m u` and `cmp n v` commute. -/
theorem gmul_comm_hom {m n : ℕ} {u v : H} (hu : u ∈ S.F m) (hv : v ∈ S.F n) :
    S.cmp m u * S.cmp n v = S.cmp n v * S.cmp m u := by
  rw [S.cmp_mul_cmp hu hv, S.cmp_mul_cmp hv hu, Nat.add_comm n m]
  refine S.cmp_eq_cmp_of_pr_eq ?_
  rw [← sub_eq_zero, ← map_sub]
  rcases Nat.eq_zero_or_pos (m + n) with h | h
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm; subst hn
    rw [S.mul_comm_of_mem_F_zero hu hv, sub_self, map_zero]
  · exact S.pr_of_mem_lt (by omega) _ (S.commutator_mem m n u hu v hv)

/-- A homogeneous element `ofC m a` commutes with every element of `Gr`. -/
theorem gmul_comm₁ {m : ℕ} (a : ↥(S.C m)) (y : S.Gr) : S.ofC m a * y = y * S.ofC m a := by
  refine S.induction_on y ?_
    (fun n b => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · rw [S.zero_mul', S.mul_zero']
  · rw [S.ofC_eq_cmp, S.ofC_eq_cmp]
    exact S.gmul_comm_hom (S.c_le_f m a.2) (S.c_le_f n b.2)
  · rw [S.mul_add', h₁, h₂, S.add_mul']

/-- The product of `Gr` is commutative. -/
theorem gmul_comm (x y : S.Gr) : x * y = y * x := by
  refine S.induction_on x ?_
    (fun m a => S.gmul_comm₁ a y) (fun x₁ x₂ h₁ h₂ => ?_)
  · rw [S.zero_mul', S.mul_zero']
  · rw [S.add_mul', h₁, h₂, S.mul_add']

/-- `1 * x = x` in `Gr`. -/
theorem gone_mul (x : S.Gr) : (1 : S.Gr) * x = x := by
  refine S.induction_on x ?_ (fun n a => ?_)
    (fun x₁ x₂ h₁ h₂ => ?_)
  · exact S.mul_zero' 1
  · rw [S.ofC_eq_cmp, one_def, S.cmp_mul_cmp S.one_mem (S.c_le_f n a.2), one_mul, Nat.zero_add]
  · rw [S.mul_add', h₁, h₂]

/-- `x * 1 = x` in `Gr`. -/
theorem gmul_one (x : S.Gr) : x * (1 : S.Gr) = x := by
  rw [S.gmul_comm]; exact S.gone_mul x

/-- The commutative ring structure of the associated graded object `Gr`. -/
instance : CommRing S.Gr where
  __ := (inferInstance : AddCommGroup S.Gr)
  mul_assoc := S.gmul_assoc
  one_mul := S.gone_mul
  mul_one := S.gmul_one
  left_distrib := S.mul_add'
  right_distrib := S.add_mul'
  zero_mul := S.zero_mul'
  mul_zero := S.mul_zero'
  mul_comm := S.gmul_comm

/-- The `k`-algebra structure of `Gr`. -/
instance : Algebra k S.Gr :=
  Algebra.ofModule (fun r x y => by
      rw [mul_def, mul_def, map_smul, LinearMap.smul_apply])
    (fun r x y => by rw [mul_def, mul_def, map_smul])

/-- `algebraMap c = cmp 0 (c • 1)` in `Gr`. -/
theorem algebraMap_eq (c : k) : algebraMap k S.Gr c = S.cmp 0 (c • (1 : H)) := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, map_smul]

/-! ### Injectivity of the embedding -/

/-- The `m`-th component of an element of the graded object. -/
def comp (m : ℕ) : S.Gr →ₗ[k] ↥(S.C m) := DirectSum.component k ℕ (fun i => ↥(S.C i)) m

/-- `pr m (emb g)` is the `m`-th component `comp m g` of `g`. -/
theorem pr_emb (m : ℕ) (g : S.Gr) : S.pr m (S.emb g) = ((S.comp m g : ↥(S.C m)) : H) := by
  refine S.induction_on g ?_
    (fun n a => ?_) (fun g₁ g₂ h₁ h₂ => ?_)
  · rw [map_zero, map_zero, map_zero, ZeroMemClass.coe_zero]
  · rw [S.emb_ofC]
    have hc : S.comp m (S.ofC n a)
        = if h : n = m then Eq.recOn h a else 0 := by
      exact DirectSum.component.of (R := k) (ι := ℕ) (M := fun i => ↥(S.C i)) m n a
    by_cases h : n = m
    · subst h
      rw [S.toSplit.pr_eq_self_of_mem_C a.2, hc]
      simp
    · rw [S.toSplit.pr_of_mem_C (Ne.symm h) a.2, hc, dite_eq_right h, ZeroMemClass.coe_zero]
  · rw [map_add, map_add, map_add, h₁, h₂, AddMemClass.coe_add]

/-- The embedding `Gr → H` is injective. -/
theorem emb_injective : Function.Injective S.emb := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  refine DirectSum.ext_component k fun m => ?_
  have := S.pr_emb m g
  rw [hg, map_zero] at this
  exact Subtype.ext this.symm

end HopfSplit

end HopfAlgebra.Graded
