module

public import UlmerBialgebras.Paper.Sec3DefsTransposedDatum

/-!
# Remark 3.2: the proof

The datum `B'` of Remark 3.2 is `UlmerBialgebras.Paper.Rem32.transposedDatum`
(`UlmerBialgebras/Paper/Sec3DefsTransposedDatum.lean`), on an arbitrary inserter `I'` of `r, id_c`.

## Main results

* `UlmerBialgebras.Paper.Rem32.comparison_iso_and_isoOver_transposed`: Remark 3.2: the comparison
  `I' ⟶ Ins(f, g)` is an isomorphism over `c`, an equifier of `α', β'` exists, and every such
  equifier is isomorphic over `c` to the given equifier `Bialg(B)` of `α, β`.
* `UlmerBialgebras.Paper.Rem32.transposedIns` — transposing the universal 2-cell turns an inserter
  of `f, g` into an inserter of `r, id_c` with the same object and the same `u`.
* `UlmerBialgebras.Paper.Rem32.comparisonInv` — the comparison `I' ⟶ Ins(f, g)` is an isomorphism
  over `c`: it is the comparison between the inserters `I'` and `transposedIns R I` of `r, id_c`.
* `UlmerBialgebras.Paper.Rem32.equif_iff` — a 1-cell `k` into `I'` equifies `α', β'` exactly when
  `k` followed by the comparison equifies `α, β`.
* `UlmerBialgebras.Paper.Rem32.equifOfTransposed`, `UlmerBialgebras.Paper.Rem32.isoOver_transposed`
  — an equifier of `α, β` gives one of `α', β'`, and any two such equifiers are isomorphic over `c`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.2
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras.Paper.Rem32

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

section Transpose

variable {c x : Obj} {f g : c ⟶ x} {r : c ⟶ c} (R : RelLeftAdj2 f g r)

/-- Naturality of `transpose` in the domain `z`. -/
lemma transpose_nat_z {z z' : Obj} (h : z' ⟶ z) (p q : z ⟶ c) (γ : p ≫ r ⟶ q ≫ 𝟙 c) :
    transpose R (h ≫ p) (h ≫ q) (eqToHom (Category.assoc h p r) ≫ (h ◁ γ) ≫
      eqToHom (Category.assoc h q _).symm)
      = eqToHom (Category.assoc h p f) ≫ (h ◁ transpose R p q γ) ≫
        eqToHom (Category.assoc h q g).symm := by
  simp only [transpose, Equiv.coe_fn_mk]
  rw [← R.nat_z]
  congr 1
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc,
    eqToHom_trans]

/-- `transpose` commutes with transport along equalities of 1-cells. -/
lemma transpose_cast {z : Obj} {p p' q q' : z ⟶ c} (hp : p = p') (hq : q = q')
    (γ : p ≫ r ⟶ q ≫ 𝟙 c) :
    transpose R p' q' (eqToHom (by rw [hp]) ≫ γ ≫ eqToHom (by rw [hq])) =
      eqToHom (by rw [hp]) ≫ transpose R p q γ ≫ eqToHom (by rw [hq]) := by
  subst hp; subst hq; simp

/-- `transpose` preserves the commutation of squares with a 2-cell `σ : p ⟶ p'`. -/
lemma transpose_square {z : Obj} {p p' : z ⟶ c} (σ : p ⟶ p') (γ : p ≫ r ⟶ p ≫ 𝟙 c)
    (γ' : p' ≫ r ⟶ p' ≫ 𝟙 c) :
    (σ ▷ r) ≫ γ' = γ ≫ (σ ▷ 𝟙 c) ↔
      (σ ▷ f) ≫ transpose R p' p' γ' = transpose R p p γ ≫ (σ ▷ g) := by
  have e1 : R.equiv p p' (((σ ▷ r) ≫ γ') ≫ eqToHom (Category.comp_id p')) =
      (σ ▷ f) ≫ transpose R p' p' γ' := by
    rw [Category.assoc, R.nat_left]; rfl
  have e2 : R.equiv p p' ((γ ≫ (σ ▷ 𝟙 c)) ≫ eqToHom (Category.comp_id p')) =
      transpose R p p γ ≫ (σ ▷ g) := by
    rw [Bicategory.Strict.whiskerRight_id]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc, R.nat_right]; rfl
  rw [← e1, ← e2, (R.equiv p p').injective.eq_iff]
  constructor
  · intro h; rw [h]
  · intro h; simpa using h =≫ eqToHom (Category.comp_id p').symm

end Transpose

section Ins

variable {c x : Obj} {f g : c ⟶ x} {r : c ⟶ c} (R : RelLeftAdj2 f g r) (I : Inserter f g)

/-- The inserter of `r, id_c` obtained from an inserter of `f, g` by transposition: same object,
same `u`, transposed universal 2-cell. -/
abbrev transposedIns : Inserter r (𝟙 c) where
  pt := I.pt
  u := I.u
  φ := (transpose R I.u I.u).symm I.φ
  lift h α := I.lift h (transpose R h h α)
  lift_u h α := I.lift_u h _
  lift_φ h α := by
    set L := I.lift h (transpose R h h α)
    have hL : L ≫ I.u = h := I.lift_u h _
    have k1 := transpose_nat_z R L I.u I.u ((transpose R I.u I.u).symm I.φ)
    rw [Equiv.apply_symm_apply, I.lift_φ] at k1
    have k2 := transpose_cast R hL.symm hL.symm α
    apply (transpose R (L ≫ I.u) (L ≫ I.u)).injective.comp
      (f := fun t => eqToHom (Category.assoc L I.u r) ≫ t ≫
        eqToHom (Category.assoc L I.u (𝟙 c)).symm)
    · intro a b hab
      simpa using congr(eqToHom (Category.assoc L I.u r).symm ≫ $hab ≫
        eqToHom (Category.assoc L I.u (𝟙 c)))
    · dsimp only [Function.comp]
      rw [k1]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      rw [← k2]
  lift_uniq k h α hu hφ := by
    refine I.lift_uniq k h _ hu ?_
    have k1 := transpose_nat_z R k I.u I.u ((transpose R I.u I.u).symm I.φ)
    rw [Equiv.apply_symm_apply, hφ] at k1
    have k2 := transpose_cast R hu.symm hu.symm α
    have k3 : k ◁ I.φ = eqToHom (Category.assoc k I.u f).symm ≫
        transpose R (k ≫ I.u) (k ≫ I.u) (eqToHom (Category.assoc k I.u r) ≫
          (eqToHom (by rw [← Category.assoc, hu]) ≫ α ≫ eqToHom (by rw [← Category.assoc, hu])) ≫
          eqToHom (Category.assoc k I.u (𝟙 c)).symm) ≫ eqToHom (Category.assoc k I.u g) := by
      rw [k1]; simp
    rw [k3]
    simp only [eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
    rw [k2]
    simp
  lift₂ {z k₁ k₂} α H := I.lift₂ α (by
    have hT := (transpose_square R α
      (eqToHom (Category.assoc k₁ I.u r) ≫ (k₁ ◁ (transpose R I.u I.u).symm I.φ) ≫
        eqToHom (Category.assoc k₁ I.u (𝟙 c)).symm)
      (eqToHom (Category.assoc k₂ I.u r) ≫ (k₂ ◁ (transpose R I.u I.u).symm I.φ) ≫
        eqToHom (Category.assoc k₂ I.u (𝟙 c)).symm)).1 H.symm
    rw [transpose_nat_z, transpose_nat_z, Equiv.apply_symm_apply] at hT
    exact hT.symm)
  lift₂_u α H := I.lift₂_u α _
  lift₂_uniq β γ h := I.lift₂_uniq β γ h

end Ins

section InsIso

variable {a b : Obj} {f g : a ⟶ b}

/-- The identity of an inserter object is the lift of the inserter's own cone. -/
lemma _root_.UlmerBialgebras.Inserter.id_eq_lift (I : Inserter f g) : 𝟙 I.pt = I.lift I.u I.φ :=
  I.lift_uniq _ _ _ (Category.id_comp _) (by rw [Bicategory.Strict.id_whiskerLeft])

/-- For two inserters of the same pair, the comparison lifts compose to the identity. -/
lemma _root_.UlmerBialgebras.Inserter.lift_comp_lift (I₁ I₂ : Inserter f g) :
    I₁.lift I₂.u I₂.φ ≫ I₂.lift I₁.u I₁.φ = 𝟙 I₂.pt := by
  rw [I₂.id_eq_lift]
  refine I₂.lift_uniq _ _ _ (by rw [Category.assoc, I₂.lift_u, I₁.lift_u]) ?_
  rw [Bicategory.Strict.comp_whiskerLeft, I₂.lift_φ]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc,
    eqToHom_trans,
    eqToHom_trans_assoc]
  rw [I₁.lift_φ]
  simp

end InsIso

/-- Conjugating by `eqToHom`s is injective. -/
lemma conj_eqToHom_iff {C : Type*} [Category C] {X X' Y Y' : C} (p : X = X') (q : Y' = Y)
    (a b : X' ⟶ Y') : eqToHom p ≫ a ≫ eqToHom q = eqToHom p ≫ b ≫ eqToHom q ↔ a = b :=
  ⟨fun h => (cancel_mono _).1 ((cancel_epi _).1 h), fun h => by rw [h]⟩

section Whisker

variable {a b z : Obj} {κ : a ⟶ b} {ψ : b ⟶ a}

/-- Right whiskering by a 1-cell `κ` with a retraction `ψ` (`κ ψ = id`) is injective. -/
lemma whiskerRight_cancel (h : κ ≫ ψ = 𝟙 a) {x₁ x₂ : z ⟶ a} (γ δ : x₁ ⟶ x₂)
    (H : γ ▷ κ = δ ▷ κ) : γ = δ := by
  have H' : (γ ▷ κ) ▷ ψ = (δ ▷ κ) ▷ ψ := by rw [H]
  rw [Bicategory.Strict.whiskerRight_comp', Bicategory.Strict.whiskerRight_comp',
    conj_eqToHom_iff] at H'
  have hid : γ ▷ 𝟙 a = δ ▷ 𝟙 a := by
    rw [Bicategory.whiskerRight_congr γ h, Bicategory.whiskerRight_congr δ h, H']
  rw [Bicategory.Strict.whiskerRight_id, Bicategory.Strict.whiskerRight_id, conj_eqToHom_iff] at hid
  exact hid

/-- Whiskering by `e ψ` and then by `κ` is whiskering by `e`, up to transport, when
`ψ κ = id`. -/
lemma whiskerRight_comp_inv {P : Obj} (h : ψ ≫ κ = 𝟙 b) {k₁ k₂ : z ⟶ P} (α : k₁ ⟶ k₂)
    (e : P ⟶ b) :
    (α ▷ (e ≫ ψ)) ▷ κ = eqToHom (by rw [Category.assoc, Category.assoc, h, Category.comp_id]) ≫
      (α ▷ e) ≫
      eqToHom (by rw [Category.assoc, Category.assoc, h, Category.comp_id]) := by
  rw [Bicategory.Strict.whiskerRight_comp',
    Bicategory.whiskerRight_congr α (show e = (e ≫ ψ) ≫ κ by rw [Category.assoc, h,
      Category.comp_id])]
  simp

end Whisker

section Comparison

variable {c x : Obj} {f g : c ⟶ x} {r : c ⟶ c} (R : RelLeftAdj2 f g r) (I : Inserter f g)
  (I' : Inserter r (𝟙 c))

/-- The inverse of the comparison: the lift through `I'` of `I.u` with the transposed universal
2-cell of `I`. -/
def comparisonInv : I.pt ⟶ I'.pt :=
  I'.lift I.u ((transpose R I.u I.u).symm I.φ)

/-- The comparison followed by its inverse is the identity of `I'`. -/
lemma comparison_comp_inv : comparison R I I' ≫ comparisonInv R I I' = 𝟙 I'.pt :=
  Inserter.lift_comp_lift (transposedIns R I) I'

/-- The inverse followed by the comparison is the identity of `Ins(f, g)`. -/
lemma inv_comp_comparison : comparisonInv R I I' ≫ comparison R I I' = 𝟙 I.pt :=
  Inserter.lift_comp_lift I' (transposedIns R I)

/-- The comparison lies over `c`. -/
lemma comparison_u : comparison R I I' ≫ I.u = I'.u := I.lift_u _ _

/-- The inverse of the comparison lies over `c`. -/
lemma comparisonInv_u : comparisonInv R I I' ≫ I'.u = I.u := I'.lift_u _ _

end Comparison

section Datum

variable (B : BialgDatum (Obj := Obj)) {r r' : B.c ⟶ B.c} (R : RelLeftAdj2 B.f B.g r)
  (R' : RelLeftAdj2 B.f' B.g' r') (I' : Inserter r (𝟙 B.c))

/-- Whiskering commutes with the inverse transposition, so it detects equality of transposes. -/
lemma whiskerLeft_transpose_symm_iff {z : Obj} (k : z ⟶ I'.pt)
    (X Y : I'.u ≫ B.f' ⟶ I'.u ≫ B.g') :
    k ◁ (transpose R' I'.u I'.u).symm X = k ◁ (transpose R' I'.u I'.u).symm Y ↔
      k ◁ X = k ◁ Y := by
  have h1 := transpose_nat_z R' k I'.u I'.u ((transpose R' I'.u I'.u).symm X)
  have h2 := transpose_nat_z R' k I'.u I'.u ((transpose R' I'.u I'.u).symm Y)
  rw [Equiv.apply_symm_apply] at h1 h2
  constructor
  · intro h
    rw [h, h2] at h1
    exact ((cancel_mono _).1 ((cancel_epi _).1 h1)).symm
  · intro h
    have : eqToHom (Category.assoc k I'.u r') ≫ (k ◁ (transpose R' I'.u I'.u).symm X) ≫
        eqToHom (Category.assoc k I'.u (𝟙 B.c)).symm =
        eqToHom (Category.assoc k I'.u r') ≫ (k ◁ (transpose R' I'.u I'.u).symm Y) ≫
        eqToHom (Category.assoc k I'.u (𝟙 B.c)).symm :=
      (transpose R' _ _).injective (by rw [h1, h2, h])
    exact (cancel_mono _).1 ((cancel_epi _).1 this)

/-- A 1-cell `k` into `I'` equifies the transposed equations of `γ, δ` exactly when `k` followed
by the comparison equifies `γ, δ`. -/
lemma whiskerLeft_transposedEqn_iff {z : Obj} (k : z ⟶ I'.pt)
    (γ δ : B.ins.u ≫ B.f' ⟶ B.ins.u ≫ B.g') :
    k ◁ transposedEqn B R R' I' γ = k ◁ transposedEqn B R R' I' δ ↔
      (k ≫ comparison R B.ins I') ◁ γ = (k ≫ comparison R B.ins I') ◁ δ := by
  rw [transposedEqn, transposedEqn, whiskerLeft_transpose_symm_iff]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  rw [conj_eqToHom_iff, Bicategory.Strict.comp_whiskerLeft', Bicategory.Strict.comp_whiskerLeft',
    conj_eqToHom_iff]

/-- A 1-cell `k` into `I'` equifies `α', β'` exactly when `k` followed by the comparison
equifies `α, β`. -/
lemma equif_iff {z : Obj} (k : z ⟶ I'.pt) :
    k ◁ (transposedDatum B R R' I').α = k ◁ (transposedDatum B R R' I').β ↔
      (k ≫ comparison R B.ins I') ◁ B.α = (k ≫ comparison R B.ins I') ◁ B.β :=
  whiskerLeft_transposedEqn_iff B R R' I' k B.α B.β

/-- An equifier of `α, β` gives an equifier of the transposed equations `α', β'`, through the
inverse of the comparison. -/
def equifOfTransposed (E : Equifier B.α B.β) :
    Equifier (transposedDatum B R R' I').α (transposedDatum B R R' I').β where
  pt := E.pt
  e := E.e ≫ comparisonInv R B.ins I'
  cond := (equif_iff B R R' I' _).2 (by
    have hw : (E.e ≫ comparisonInv R B.ins I') ≫ comparison R B.ins I' = E.e := by
      rw [Category.assoc, inv_comp_comparison, Category.comp_id]
    rw [hw]
    exact E.cond)
  lift h H := E.lift (h ≫ comparison R B.ins I') ((equif_iff B R R' I' h).1 H)
  lift_e h H := by rw [← Category.assoc, E.lift_e, Category.assoc, comparison_comp_inv,
    Category.comp_id]
  lift_uniq k h H hk := E.lift_uniq k _ _ (by
    rw [← hk, Category.assoc, Category.assoc, inv_comp_comparison, Category.comp_id])
  full {z k₁ k₂} β := by
    have hk : ∀ k : z ⟶ E.pt,
        (k ≫ (E.e ≫ comparisonInv R B.ins I')) ≫ comparison R B.ins I' = k ≫ E.e := by
      intro k
      rw [Category.assoc, Category.assoc, inv_comp_comparison, Category.comp_id]
    obtain ⟨α, hα⟩ := E.full (eqToHom (hk k₁).symm ≫ (β ▷ comparison R B.ins I') ≫
      eqToHom (hk k₂))
    refine ⟨α, whiskerRight_cancel (comparison_comp_inv R B.ins I') _ _ ?_⟩
    rw [whiskerRight_comp_inv (inv_comp_comparison R B.ins I'), hα]
    simp
  faithful α β h := by
    apply E.faithful
    have h' : (α ▷ (E.e ≫ comparisonInv R B.ins I')) ▷ comparison R B.ins I' =
        (β ▷ (E.e ≫ comparisonInv R B.ins I')) ▷ comparison R B.ins I' := by rw [h]
    rw [whiskerRight_comp_inv (inv_comp_comparison R B.ins I'),
      whiskerRight_comp_inv (inv_comp_comparison R B.ins I'), conj_eqToHom_iff] at h'
    exact h'

/-- Every equifier of the transposed equations is isomorphic over `c` to every equifier of
`α, β`. -/
theorem isoOver_transposed (E : Equifier B.α B.β)
    (E' : Equifier (transposedDatum B R R' I').α (transposedDatum B R R' I').β) :
    IsoOver (B.uB E) ((transposedDatum B R R' I').uB E') := by
  let φ : E.pt ⟶ E'.pt :=
    E'.lift (E.e ≫ comparisonInv R B.ins I') (equifOfTransposed B R R' I' E).cond
  let χ : E'.pt ⟶ E.pt :=
    E.lift (E'.e ≫ comparison R B.ins I') ((equif_iff B R R' I' E'.e).1 E'.cond)
  have hφ : φ ≫ E'.e = E.e ≫ comparisonInv R B.ins I' := E'.lift_e _ _
  have hχ : χ ≫ E.e = E'.e ≫ comparison R B.ins I' := E.lift_e _ _
  refine ⟨φ, χ, ?_, ?_, ?_⟩
  · have h : (φ ≫ χ) ≫ E.e = E.e := by
      rw [Category.assoc, hχ, ← Category.assoc, hφ, Category.assoc, inv_comp_comparison,
        Category.comp_id]
    exact (E.lift_uniq _ E.e E.cond h).trans (E.lift_uniq (𝟙 _) E.e E.cond (Category.id_comp
      _)).symm
  · have h : (χ ≫ φ) ≫ E'.e = E'.e := by
      rw [Category.assoc, hφ, ← Category.assoc, hχ, Category.assoc, comparison_comp_inv]
      exact Category.comp_id _
    exact (E'.lift_uniq _ E'.e E'.cond h).trans
      (E'.lift_uniq (𝟙 _) E'.e E'.cond (Category.id_comp _)).symm
  · change φ ≫ (E'.e ≫ I'.u) = E.e ≫ B.ins.u
    rw [← Category.assoc, hφ, Category.assoc, comparisonInv_u]

/-- **Remark 3.2**: the comparison `I' ⟶ Ins(f, g)` is an isomorphism over `c`, an equifier of
`α', β'` exists, and every one is isomorphic over `c` to `Bialg(B)`. -/
theorem comparison_iso_and_isoOver_transposed (E : Equifier B.α B.β) :
    (∃ ψ : B.ins.pt ⟶ I'.pt, comparison R B.ins I' ≫ ψ = 𝟙 I'.pt ∧
      ψ ≫ comparison R B.ins I' = 𝟙 B.ins.pt ∧ comparison R B.ins I' ≫ B.ins.u = I'.u) ∧
    (∃ E' : Equifier (transposedDatum B R R' I').α (transposedDatum B R R' I').β,
      IsoOver (B.uB E) ((transposedDatum B R R' I').uB E')) ∧
      ∀ E' : Equifier (transposedDatum B R R' I').α (transposedDatum B R R' I').β,
        IsoOver (B.uB E) ((transposedDatum B R R' I').uB E') :=
  ⟨⟨comparisonInv R B.ins I', comparison_comp_inv R B.ins I', inv_comp_comparison R B.ins I',
      comparison_u R B.ins I'⟩,
    ⟨equifOfTransposed B R R' I' E, isoOver_transposed B R R' I' E _⟩,
    isoOver_transposed B R R' I' E⟩

end Datum

end UlmerBialgebras.Paper.Rem32
