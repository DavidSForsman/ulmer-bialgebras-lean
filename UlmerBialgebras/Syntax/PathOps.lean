module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import UlmerBialgebras.Syntax.Syntax

/-!
# Operations on paths of the term graph

Auxiliary constructions on the term graph `G_σ` of a signature pair, used to write down the
theories of Examples 3.20:

* `UlmerBialgebras.OneSig.Path.comp` — concatenation of paths;
* `UlmerBialgebras.OneSig.Path.transport` — transport of a path along equalities of its endpoints;
* `UlmerBialgebras.OneSig.Path.slot` — the functorial image `B(t₀,…,p,…,tₙ)` of a path in one slot;
* `UlmerBialgebras.OneSig.pathApp` — the functorial image `B(p₁,…,pₙ)` of a family of paths, one in
  each argument, obtained by changing one argument at a time (the convention of
  Examples 3.20 (4) of the paper; cf. the footnote in Examples 3.20 (2)).

## Main results

* `UlmerBialgebras.OneSig.Path.comp`: concatenation of paths in the term graph.
* `UlmerBialgebras.OneSig.Path.transport`: transport of a path along equalities of its endpoints.
* `UlmerBialgebras.OneSig.Path.slot`: the image `B(t₀, …, p, …, tₙ)` of a path `p` in one slot.
* `UlmerBialgebras.OneSig.pathApp`: the image `B(p₁, …, pₙ)` of a family of paths, one in each
  argument (Examples 3.20).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.20
-/

@[expose] public section

namespace UlmerBialgebras

namespace OneSig

variable {Sg : TwoSig} {sg : OneSig Sg}

/-- Concatenation of paths in the term graph. -/
def Path.comp : ∀ {c : Sg.Cat} {t t' t'' : sg.CTrm c},
    sg.Path t t' → sg.Path t' t'' → sg.Path t t''
  | _, _, _, _, .nil _, q => q
  | _, _, _, _, .cons g p, q => .cons g (p.comp q)

/-- Transport of a path along equalities of its endpoints. -/
def Path.transport {c : Sg.Cat} {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    (p : sg.Path t₁ t₂) : sg.Path t₁' t₂' := h₁ ▸ h₂ ▸ p

/-- Target equality for the `nil` case of `Path.slotAux`. -/
lemma slotAux_nil_eq (B : Sg.Fun) (i : Fin (Sg.arn B)) (args : ∀ j, sg.CTrm (Sg.art B j))
    {t₀ : sg.CTrm (Sg.art B i)} (h : args i = t₀) :
    Trm.app B args = Trm.app B (Function.update args i t₀) := by
  rw [← h, Function.update_eq_self]

/-- Target equality for the `cons` case of `Path.slotAux`. -/
lemma slotAux_cons_eq (B : Sg.Fun) (i : Fin (Sg.arn B)) (args : ∀ j, sg.CTrm (Sg.art B j))
    (t' t : sg.CTrm (Sg.art B i)) :
    Trm.app B (Function.update (Function.update args i t') i t) =
      Trm.app B (Function.update args i t) := by
  rw [Function.update_idem]

/-- Auxiliary form of `Path.slot`, with the source of the path decoupled from `args i` so
that the recursion is structural in the path. -/
def Path.slotAux (B : Sg.Fun) (i : Fin (Sg.arn B)) :
    ∀ (args : ∀ j, sg.CTrm (Sg.art B j)) {t₀ t : sg.CTrm (Sg.art B i)},
      args i = t₀ → sg.Path t₀ t →
      sg.Path (Trm.app B args) (Trm.app B (Function.update args i t))
  | args, _, _, h, .nil _ =>
      Path.transport rfl (slotAux_nil_eq B i args h) (.nil _)
  | args, _, t, h, .cons (t' := t') g p =>
      Path.transport rfl (slotAux_cons_eq B i args t' t)
        (Path.comp
          (.cons (OneSig.Arr.app B i args (Function.update args i t')
            (fun _ hj => (Function.update_of_ne hj _ _).symm)
            (Arr.transport h.symm (Function.update_self i t' args).symm g)) (.nil _))
          (Path.slotAux B i (Function.update args i t') (Function.update_self i t' args) p))

/-- The functorial image `B(t₀, …, p, …, tₙ)` of a *path* `p` in the `i`-th slot. -/
def Path.slot (B : Sg.Fun) (i : Fin (Sg.arn B)) (args : ∀ j, sg.CTrm (Sg.art B j))
    {t : sg.CTrm (Sg.art B i)} (p : sg.Path (args i) t) :
    sg.Path (Trm.app B args) (Trm.app B (Function.update args i t)) :=
  Path.slotAux B i args rfl p


/-- The family of terms which is `args'` in the slots `< k` and `args` in the others. -/
def mix (B : Sg.Fun) (args args' : ∀ j, sg.CTrm (Sg.art B j)) (k : ℕ) :
    ∀ j, sg.CTrm (Sg.art B j) := fun j => if (j : ℕ) < k then args' j else args j

variable {B : Sg.Fun} {args args' : ∀ j, sg.CTrm (Sg.art B j)}

/-- `mix … 0` is `args`. -/
@[simp] lemma mix_zero : mix B args args' 0 = args := by
  funext j; simp [mix]

/-- `mix … (Sg.arn B)` is `args'`. -/
lemma mix_arn : mix B args args' (Sg.arn B) = args' := by
  funext j; simp [mix, j.is_lt]

/-- At slot `k`, `mix … k` still takes the value of `args`. -/
lemma mix_apply_self {k : ℕ} (h : k < Sg.arn B) : mix B args args' k ⟨k, h⟩ = args ⟨k, h⟩ := by
  simp [mix]

/-- `mix … (k + 1)` is `mix … k` with slot `k` updated to `args' k`. -/
lemma mix_succ {k : ℕ} (h : k < Sg.arn B) :
    mix B args args' (k + 1) = Function.update (mix B args args' k) ⟨k, h⟩ (args' ⟨k, h⟩) := by
  funext j
  by_cases hj : j = ⟨k, h⟩
  · subst hj; simp [mix]
  · have hjk : (j : ℕ) ≠ k := fun hh => hj (Fin.ext hh)
    rw [Function.update_of_ne hj]
    simp only [mix]
    by_cases hlt : (j : ℕ) < k
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · have : ¬ (j : ℕ) < k + 1 := by omega
      simp [hlt, this]

/-- `mix … (k + 1) = mix … k` once `k` is at least the arity. -/
lemma mix_succ_of_ge {k : ℕ} (h : Sg.arn B ≤ k) :
    mix B args args' (k + 1) = mix B args args' k := by
  funext j
  have h1 : (j : ℕ) < k := lt_of_lt_of_le j.is_lt h
  simp [mix, h1, Nat.lt_succ_of_lt h1]

/-- Target equality for the `0` case of `pathUpTo`. -/
lemma pathUpTo_zero_eq (B : Sg.Fun) (args args' : ∀ j, sg.CTrm (Sg.art B j)) :
    Trm.app B args = Trm.app B (mix B args args' 0) := by
  rw [mix_zero]

/-- Target equality for the `k + 1` (`k < arn B`) case of `pathUpTo`. -/
lemma pathUpTo_succ_lt_eq (B : Sg.Fun) (args args' : ∀ j, sg.CTrm (Sg.art B j))
    {k : ℕ} (h : k < Sg.arn B) :
    Trm.app B (Function.update (mix B args args' k) ⟨k, h⟩ (args' ⟨k, h⟩)) =
      Trm.app B (mix B args args' (k + 1)) := by
  rw [mix_succ (args := args) (args' := args') h]

/-- Target equality for the `k + 1` (`¬ k < arn B`) case of `pathUpTo`. -/
lemma pathUpTo_succ_ge_eq (B : Sg.Fun) (args args' : ∀ j, sg.CTrm (Sg.art B j))
    {k : ℕ} (h : ¬ k < Sg.arn B) :
    Trm.app B (mix B args args' k) = Trm.app B (mix B args args' (k + 1)) := by
  rw [mix_succ_of_ge (Nat.le_of_not_lt h)]

/-- The path `B(p₁,…,p_k, t_{k+1}, …, tₙ)` obtained by applying the given paths in the first
`k` slots. -/
def pathUpTo (p : ∀ j, sg.Path (args j) (args' j)) :
    ∀ k : ℕ, sg.Path (Trm.app B args) (Trm.app B (mix B args args' k))
  | 0 => Path.transport rfl (pathUpTo_zero_eq B args args') (.nil _)
  | k + 1 =>
      if h : k < Sg.arn B then
        Path.transport rfl (pathUpTo_succ_lt_eq B args args' h)
          (Path.comp (pathUpTo p k)
            (Path.slot B ⟨k, h⟩ (mix B args args' k)
              (Path.transport (mix_apply_self h).symm rfl (p ⟨k, h⟩))))
      else
        Path.transport rfl (pathUpTo_succ_ge_eq B args args' h) (pathUpTo p k)

/-- After all `arn B` steps every argument is replaced: `B (mix args args' (arn B)) = B args'`,
the target of `pathApp`. -/
lemma pathApp_eq (B : Sg.Fun) (args args' : ∀ j, sg.CTrm (Sg.art B j)) :
    Trm.app B (mix B args args' (Sg.arn B)) = Trm.app B args' := by
  rw [mix_arn]

/-- **The functorial image `B(p₁,…,pₙ)` of a family of paths**, one in each argument. -/
def pathApp (p : ∀ j, sg.Path (args j) (args' j)) :
    sg.Path (Trm.app B args) (Trm.app B args') :=
  Path.transport rfl (pathApp_eq B args args') (pathUpTo p (Sg.arn B))


end OneSig

end UlmerBialgebras
