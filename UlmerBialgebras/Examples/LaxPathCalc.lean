module

public import UlmerBialgebras.Models.ThyRep
public import UlmerBialgebras.Examples.LaxTheoryEx
public import UlmerBialgebras.Syntax.PathOps

/-!
# Path evaluation at an environment: calculations

Calculations with the evaluation `Model.pathCellAlg` of paths of the term graph at an environment
`ρ` and 2-cells `ψ` for the function symbols: concatenation, transport, the functorial image
`B(p₁, …, pₙ)` of a family of paths, and the canonical paths `f_t : t → s` of the lax-limit theory
`T_Lax` (Examples 3.20 (4) of [forsman2026syntactic]). At the inserter of `M^σ` this is the
evaluation `Model.pathCell` of Definition 3.14.

## Main results

* `UlmerBialgebras.LaxEx.pathCellAlg_pathApp`: `B(p₁, …, pₙ)` evaluates to the
  image under `B` of the evaluations of the `pᵢ`.
* `UlmerBialgebras.LaxEx.pathCellAlg_termPath`: the canonical path of
  `B(t₁, …, tₙ)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.14 and Examples 3.20 (4)
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.LaxEx

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig}

/-- The 2-cell of a transported arrow. -/
lemma arrCellAlg_transport (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    {c : Sg.Cat} {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (g : sg.Arr t₁ t₂) :
    M.arrCellAlg sg ρ ψ (g.transport h₁ h₂) =
      eqToHom (by rw [h₁]) ≫ M.arrCellAlg sg ρ ψ g ≫ eqToHom (by rw [h₂]) := by
  subst h₁; subst h₂; simp [OneSig.Arr.transport]

section General


/-- Path evaluation in a model `M` sends concatenation `p.comp q` to the composite of 2-cells. -/
lemma pathCellAlg_comp (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    {c : Sg.Cat} {t t' t'' : sg.CTrm c}
    (p : sg.Path t t') (q : sg.Path t' t'') :
    M.pathCellAlg sg ρ ψ (p.comp q) = M.pathCellAlg sg ρ ψ p ≫ M.pathCellAlg sg ρ ψ q := by
  induction p with
  | nil t => simp [OneSig.Path.comp]
  | cons g p ih => simp [OneSig.Path.comp, ih]

/-- Evaluating a path transported along equalities of its endpoints conjugates its 2-cell
    by `eqToHom`s. -/
lemma pathCellAlg_transport (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    {c : Sg.Cat}
    {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (p : sg.Path t₁ t₂) :
    M.pathCellAlg sg ρ ψ (OneSig.Path.transport h₁ h₂ p) =
      eqToHom (by rw [h₁]) ≫ M.pathCellAlg sg ρ ψ p ≫ eqToHom (by rw [h₂]) := by
  subst h₁; subst h₂; simp [OneSig.Path.transport]

/-- The evaluation of a transported path is `ConjEq` to the evaluation of the original path. -/
lemma pathCellAlg_transport_conjEq (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    {c : Sg.Cat}
    {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (p : sg.Path t₁ t₂) :
    ConjEq (M.pathCellAlg sg ρ ψ (OneSig.Path.transport h₁ h₂ p)) (M.pathCellAlg sg ρ ψ p) :=
  ⟨_, _, pathCellAlg_transport M sg ρ ψ h₁ h₂ p⟩

/-- The 2-cell of a transported arrow is `ConjEq` to the 2-cell of the original arrow. -/
lemma arrCellAlg_transport_conjEq (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    {c : Sg.Cat}
    {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (g : sg.Arr t₁ t₂) :
    ConjEq (M.arrCellAlg sg ρ ψ (g.transport h₁ h₂)) (M.arrCellAlg sg ρ ψ g) :=
  ⟨_, _, arrCellAlg_transport M sg ρ ψ h₁ h₂ g⟩

/-- The image under a functor symbol respects componentwise agreement up to `eqToHom`s. -/
lemma appCell_conjEq (M : Model Sg Obj) (B : Sg.Fun) {x : Obj}
    {g g' k k' : ∀ i, x ⟶ M.obj (Sg.art B i)} {γ : ∀ i, g i ⟶ g' i} {δ : ∀ i, k i ⟶ k' i}
    (h : ∀ i, ConjEq (γ i) (δ i)) : ConjEq (M.appCell B γ) (M.appCell B δ) := by
  have hg : g = k := funext fun i => by
    obtain ⟨p, _, _⟩ := h i
    exact p
  have hg' : g' = k' := funext fun i => by
    obtain ⟨_, q, _⟩ := h i
    exact q.symm
  subst hg hg'
  exact ConjEq.of_eq (M.appCell_congr B fun i => (h i).eq)

/-- The image under a functor symbol `B` of `γᵢ ≫ eqToHom eᵢ` is the image of `γ` followed
    by an `eqToHom`. -/
lemma appCell_comp_eqToHom (M : Model Sg Obj) (B : Sg.Fun) {x : Obj}
    {g g' g'' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) (e : ∀ i, g' i = g'' i) :
    M.appCell B (fun i => γ i ≫ eqToHom (e i)) =
      M.appCell B γ ≫ eqToHom (by rw [funext e]) := by
  rw [← M.appCell_eqToHom B e, M.appCell_comp B γ (fun i => eqToHom (e i))]

/-- The image under a functor symbol `B` of `γᵢ ≫ δᵢ ≫ eqToHom eᵢ` is the composite of the
    images of `γ` and `δ`, followed by an `eqToHom`. -/
lemma appCell_comp_comp_eqToHom (M : Model Sg Obj) (B : Sg.Fun) {x : Obj}
    {g g' g'' g''' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i)
    (δ : ∀ i, g' i ⟶ g'' i) (e : ∀ i, g'' i = g''' i) :
    M.appCell B (fun i => γ i ≫ δ i ≫ eqToHom (e i)) =
      M.appCell B γ ≫ M.appCell B δ ≫ eqToHom (by rw [funext e]) := by
  rw [← appCell_comp_eqToHom M B δ e, M.appCell_comp B γ (fun i => δ i ≫ eqToHom (e i))]

/-- The evaluation of the image `B(t₀, …, g, …, tₙ)` of an arrow in one slot. -/
lemma arrCellAlg_app_spec (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
    (hne : ∀ j, j ≠ i → args j = args' j) (g : sg.Arr (args i) (args' i)) :
    ∃ α : ∀ j, M.interp ρ (args j) ⟶ M.interp ρ (args' j),
      M.arrCellAlg sg ρ ψ (OneSig.Arr.app B i args args' hne g) = M.appCell B α ∧
        ConjEq (α i) (M.arrCellAlg sg ρ ψ g) ∧ ∀ j, j ≠ i → ∃ e, α j = eqToHom e := by
  refine ⟨_, Model.arrCellAlg_app M sg ρ ψ B i args args' hne g, ConjEq.of_eq ?_,
    fun j hj => ⟨_, dite_eq_right hj⟩⟩
  simp

/-- The evaluation of the image `B(t₀, …, p, …, tₙ)` of a path in one slot: the image under
`B` of a family of 2-cells which is the evaluation of `p` in the slot and an `eqToHom`
elsewhere. -/
theorem slotAux_spec (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    (B : Sg.Fun) (i : Fin (Sg.arn B)) :
    ∀ (args : ∀ j, sg.CTrm (Sg.art B j)) {t₀ t : sg.CTrm (Sg.art B i)} (h : args i = t₀)
      (p : sg.Path t₀ t),
      ∃ δ : ∀ j, M.interp ρ (args j) ⟶ M.interp ρ (Function.update args i t j),
        M.pathCellAlg sg ρ ψ (OneSig.Path.slotAux B i args h p) = M.appCell B δ ∧
          ConjEq (δ i) (M.pathCellAlg sg ρ ψ p) ∧ ∀ j, j ≠ i → ∃ e, δ j = eqToHom e
  | args, t₀, _, h, .nil _ => by
    have e : ∀ j, M.interp ρ (args j) = M.interp ρ (Function.update args i t₀ j) := fun j => by
      rw [← h, Function.update_eq_self]
    refine ⟨fun j => eqToHom (e j), ?_, ?_, fun j _ => ⟨_, rfl⟩⟩
    · rw [PreModel.appCell_eqToHom]
      simp only [OneSig.Path.slotAux, pathCellAlg_transport, Model.pathCellAlg_nil,
        Category.id_comp,
        eqToHom_trans]
    · refine ⟨congr(M.interp ρ $h), by rw [Function.update_self], ?_⟩
      simp
  | args, t₀, t, h, .cons (t' := t') g p => by
    obtain ⟨δ', hδ', hδ'i, hδ'j⟩ :=
      slotAux_spec M sg ρ ψ B i (Function.update args i t') (Function.update_self i t' args) p
    obtain ⟨α, hα, hαi, hαj⟩ := arrCellAlg_app_spec M sg ρ ψ B i args (Function.update args i t')
      (fun j hj => (Function.update_of_ne hj _ _).symm)
      (OneSig.Arr.transport h.symm (Function.update_self i t' args).symm g)
    have e : ∀ j, M.interp ρ (Function.update (Function.update args i t') i t j) =
        M.interp ρ (Function.update args i t j) := fun j => by
      rw [Function.update_idem]
    refine ⟨fun j => α j ≫ δ' j ≫ eqToHom (e j), ?_, ?_, ?_⟩
    · rw [appCell_comp_comp_eqToHom M B α δ' e, ← hα, ← hδ']
      simp only [OneSig.Path.slotAux, pathCellAlg_transport, pathCellAlg_comp,
        Model.pathCellAlg_cons,
        Model.pathCellAlg_nil, Category.comp_id, eqToHom_refl, Category.id_comp, Category.assoc]
    · rw [Model.pathCellAlg_cons]
      exact ConjEq.comp (hαi.trans (arrCellAlg_transport_conjEq M sg ρ ψ _ _ g))
        (hδ'i.comp_eqToHom (e i))
    · intro j hj
      obtain ⟨e₁, he₁⟩ := hαj j hj
      obtain ⟨e₂, he₂⟩ := hδ'j j hj
      exact ⟨e₁.trans (e₂.trans (e j)), by simp only [he₁, he₂, eqToHom_trans]⟩

/-- The evaluation of `B(t₀, …, p, …, tₙ)`, with a path `p` in slot `i`: the image under `B` of
    a family that is `ConjEq` to the evaluation of `p` at `i` and an `eqToHom` elsewhere. -/
lemma slot_spec (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args : ∀ j, sg.CTrm (Sg.art B j)) {t : sg.CTrm (Sg.art B i)} (p : sg.Path (args i) t) :
    ∃ δ : ∀ j, M.interp ρ (args j) ⟶ M.interp ρ (Function.update args i t j),
      M.pathCellAlg sg ρ ψ (OneSig.Path.slot B i args p) = M.appCell B δ ∧
        ConjEq (δ i) (M.pathCellAlg sg ρ ψ p) ∧ ∀ j, j ≠ i → ∃ e, δ j = eqToHom e :=
  slotAux_spec M sg ρ ψ B i args rfl p

/-- One step of `pathUpTo_spec`: a description of the evaluation of `pathUpTo p k` as an
    image under `B` yields one of the evaluation of `pathUpTo p (k + 1)`. -/
lemma pathUpTo_spec_succ (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    (B : Sg.Fun)
    {args args' : ∀ j, sg.CTrm (Sg.art B j)} (p : ∀ j, sg.Path (args j) (args' j)) (k : ℕ)
    (γ : ∀ j, M.interp ρ (args j) ⟶ M.interp ρ (OneSig.mix B args args' k j))
    (hγ : M.pathCellAlg sg ρ ψ (OneSig.pathUpTo p k) = M.appCell B γ)
    (hγj : ∀ j : Fin (Sg.arn B), ((j : ℕ) < k → ConjEq (γ j) (M.pathCellAlg sg ρ ψ (p j))) ∧
      (¬ (j : ℕ) < k → ∃ e, γ j = eqToHom e)) :
    ∃ γ' : ∀ j, M.interp ρ (args j) ⟶ M.interp ρ (OneSig.mix B args args' (k + 1) j),
      M.pathCellAlg sg ρ ψ (OneSig.pathUpTo p (k + 1)) = M.appCell B γ' ∧
        ∀ j : Fin (Sg.arn B), ((j : ℕ) < k + 1 → ConjEq (γ' j) (M.pathCellAlg sg ρ ψ (p j))) ∧
          (¬ (j : ℕ) < k + 1 → ∃ e, γ' j = eqToHom e) := by
  -- If slot `k` exists, compose `γ` with the cell `δ` that runs `p k` in that slot (`slot_spec`);
  -- otherwise `pathUpTo` does not change and `γ` is transported.
  by_cases hk : k < Sg.arn B
  · obtain ⟨δ, hδ, hδi, hδj⟩ := slot_spec M sg ρ ψ B ⟨k, hk⟩ (OneSig.mix B args args' k)
      (OneSig.Path.transport (OneSig.mix_apply_self (args := args) (args' := args') hk).symm
        rfl (p ⟨k, hk⟩))
    have e : ∀ j, M.interp ρ (Function.update (OneSig.mix B args args' k) ⟨k, hk⟩
        (args' ⟨k, hk⟩) j) = M.interp ρ (OneSig.mix B args args' (k + 1) j) := fun j => by
      rw [OneSig.mix_succ (args := args) (args' := args') hk]
    refine ⟨fun j => γ j ≫ δ j ≫ eqToHom (e j), ?_, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
    · rw [appCell_comp_comp_eqToHom M B γ δ e, ← hγ, ← hδ]
      simp only [OneSig.pathUpTo, dite_eq_left hk, pathCellAlg_transport, pathCellAlg_comp,
        eqToHom_refl, Category.id_comp, Category.assoc]
    · -- The family is a `fun`; reduce its application at `j` for the rewrites below.
      beta_reduce
      by_cases hjk : (j : ℕ) < k
      · have hji : j ≠ ⟨k, hk⟩ := fun h' => by
          subst h'
          exact lt_irrefl _ hjk
        obtain ⟨e₂, he₂⟩ := hδj j hji
        rw [he₂, eqToHom_trans]
        exact ((hγj j).1 hjk).comp_eqToHom _
      · have hjk' : j = ⟨k, hk⟩ := Fin.ext (show (j : ℕ) = k by omega)
        subst hjk'
        obtain ⟨e₁, he₁⟩ := (hγj ⟨k, hk⟩).2 hjk
        rw [he₁]
        exact ((hδi.trans (pathCellAlg_transport_conjEq M sg ρ ψ _ _ _)).comp_eqToHom _
          ).eqToHom_comp _
    · have hjk : ¬ (j : ℕ) < k := fun h' => hj (Nat.lt_succ_of_lt h')
      have hji : j ≠ ⟨k, hk⟩ := fun h' => hj (by subst h'; exact Nat.lt_succ_self k)
      obtain ⟨e₁, he₁⟩ := (hγj j).2 hjk
      obtain ⟨e₂, he₂⟩ := hδj j hji
      exact ⟨e₁.trans (e₂.trans (e j)), by simp only [he₁, he₂, eqToHom_trans]⟩
  · have e : ∀ j, M.interp ρ (OneSig.mix B args args' k j) =
        M.interp ρ (OneSig.mix B args args' (k + 1) j) := fun j => by
      rw [OneSig.mix_succ_of_ge (args := args) (args' := args') (Nat.le_of_not_lt hk)]
    refine ⟨fun j => γ j ≫ eqToHom (e j), ?_, fun j => ⟨fun _ => ?_, fun hj => ?_⟩⟩
    · rw [appCell_comp_eqToHom M B γ e, ← hγ]
      simp only [OneSig.pathUpTo, dite_eq_right hk, pathCellAlg_transport, eqToHom_refl,
        Category.id_comp]
    · exact ((hγj j).1 (lt_of_lt_of_le j.is_lt (Nat.le_of_not_lt hk))).comp_eqToHom _
    · exact absurd (Nat.lt_succ_of_lt (lt_of_lt_of_le j.is_lt (Nat.le_of_not_lt hk))) hj

/-- The evaluation of `B(p₁, …, p_k, t_{k+1}, …, tₙ)`. -/
lemma pathUpTo_spec (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    (B : Sg.Fun)
    {args args' : ∀ j, sg.CTrm (Sg.art B j)} (p : ∀ j, sg.Path (args j) (args' j)) (k : ℕ) :
    ∃ γ : ∀ j, M.interp ρ (args j) ⟶ M.interp ρ (OneSig.mix B args args' k j),
      M.pathCellAlg sg ρ ψ (OneSig.pathUpTo p k) = M.appCell B γ ∧
        ∀ j : Fin (Sg.arn B), ((j : ℕ) < k → ConjEq (γ j) (M.pathCellAlg sg ρ ψ (p j))) ∧
          (¬ (j : ℕ) < k → ∃ e, γ j = eqToHom e) := by
  induction k with
  | zero =>
    have e : ∀ j, M.interp ρ (args j) = M.interp ρ (OneSig.mix B args args' 0 j) := fun j => by
      rw [OneSig.mix_zero]
    refine ⟨fun j => eqToHom (e j), ?_,
      fun j => ⟨fun hj => absurd hj (Nat.not_lt_zero _), fun _ => ⟨_, rfl⟩⟩⟩
    rw [PreModel.appCell_eqToHom]
    simp only [OneSig.pathUpTo, pathCellAlg_transport, Model.pathCellAlg_nil, Category.id_comp,
      eqToHom_trans]
  | succ k ih =>
    obtain ⟨γ, hγ, hγj⟩ := ih
    exact pathUpTo_spec_succ M sg ρ ψ B p k γ hγ hγj

/-- **The functorial image of a family of paths evaluates to the image under the functor
symbol of their evaluations.** -/
theorem pathCellAlg_pathApp (M : Model Sg Obj) (sg : OneSig Sg) {x₀ : Obj}
    (ρ : ∀ s : sg.Srt, x₀ ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))
    (B : Sg.Fun)
    {args args' : ∀ j, sg.CTrm (Sg.art B j)} (p : ∀ j, sg.Path (args j) (args' j)) :
    M.pathCellAlg sg ρ ψ (OneSig.pathApp p) =
      M.appCell B (fun j => M.pathCellAlg sg ρ ψ (p j)) := by
  obtain ⟨γ, hγ, hγj⟩ := pathUpTo_spec M sg ρ ψ B p (Sg.arn B)
  have h1 : ConjEq (M.pathCellAlg sg ρ ψ (OneSig.pathApp p)) (M.appCell B γ) := by
    rw [← hγ]
    exact pathCellAlg_transport_conjEq M sg ρ ψ _ _ _
  exact (h1.trans (appCell_conjEq M B fun j => (hγj j).1 j.is_lt)).eq

/-- The canonical path `f_s : s → s` of a sort (a variable) evaluates to the identity. -/
lemma pathCellAlg_termPath_var (M : Model Sg Obj) {x₀ : Obj}
    (ρ : ∀ s : Sg.Cat, x₀ ⟶ M.obj s)
    (ψ : ∀ f : (LaxEx.oneSig Sg).Fn, M.interp ρ ((LaxEx.oneSig Sg).fndom f) ⟶
      M.interp ρ ((LaxEx.oneSig Sg).fncod f)) (c : Sg.Cat) :
    M.pathCellAlg (LaxEx.oneSig Sg) ρ ψ (LaxEx.termPath (Trm.var c)) = 𝟙 _ := by
  simp [LaxEx.termPath]

/-- **The canonical path of `B(t₁, …, tₙ)`** evaluates to the image under `B` of the
canonical paths of the `tᵢ`, followed by the 2-cell of the function symbol `f_B`. -/
theorem pathCellAlg_termPath (M : Model Sg Obj) {x₀ : Obj} (ρ : ∀ s : Sg.Cat, x₀ ⟶ M.obj s)
    (ψ : ∀ f : (LaxEx.oneSig Sg).Fn, M.interp ρ ((LaxEx.oneSig Sg).fndom f) ⟶
      M.interp ρ ((LaxEx.oneSig Sg).fncod f)) (B : Sg.Fun)
    (ts : ∀ i, (LaxEx.oneSig Sg).CTrm (Sg.art B i)) :
    M.pathCellAlg (LaxEx.oneSig Sg) ρ ψ (LaxEx.termPath (Trm.app B ts)) =
      M.appCell B (fun i => M.pathCellAlg (LaxEx.oneSig Sg) ρ ψ (LaxEx.termPath (ts i))) ≫
        ψ B := by
  simp only [LaxEx.termPath, pathCellAlg_comp, pathCellAlg_pathApp, Model.pathCellAlg_cons,
    Model.pathCellAlg_nil, Category.comp_id, Model.arrCellAlg_fn]

end General

end UlmerBialgebras.LaxEx
