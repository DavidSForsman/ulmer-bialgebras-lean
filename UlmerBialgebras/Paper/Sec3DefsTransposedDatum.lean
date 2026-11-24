module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Basic.PIE
public import UlmerBialgebras.Density.AAdjointRep

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Remark 3.2: the transposed bialgebraic datum

Definitions for Remark 3.2. Let `r` be an `f`-relative left adjoint of `g` (`RelLeftAdj2 f g r`).
Then 2-cells `p f ⟶ q g` correspond to 2-cells `p r ⟶ q`, through
`UlmerBialgebras.Paper.Rem32.transpose`.

Let `I'` be any inserter of `r, id_c`. Its universal 2-cell, transposed, induces the canonical
comparison `UlmerBialgebras.Paper.Rem32.comparison : I' ⟶ Ins(f, g)` over `c`; Remark 3.2 asserts
that it is an isomorphism, `Ins(f, g) ≅ Ins(r, id_c)`. The bialgebraic datum `B'` of the remark
(`UlmerBialgebras.Paper.Rem32.transposedDatum`) has the inserter `I'` and the equations `α, β`
restricted along the comparison and transposed along the `f'`-relative adjunction `r'`. An
adjunction `l ⊣ g` makes `f l` an `f`-relative left adjoint of `g`
(`UlmerBialgebras.Paper.Rem32.relOfAdj`), which is the first case of the remark.

These are definitions only; the facts about them are proved in
`UlmerBialgebras/Proofs/Sec3/TransposedDatum.lean`.

## Main results

* `UlmerBialgebras.Paper.Rem32.transpose`: the bijection `(p r ⟶ q id) ≃ (p f ⟶ q g)`.
* `UlmerBialgebras.Paper.Rem32.comparison`: the canonical comparison `I' ⟶ Ins(f, g)`.
* `UlmerBialgebras.Paper.Rem32.transposedDatum`: the bialgebraic datum `B'` of Remark 3.2.
* `UlmerBialgebras.Paper.Rem32.relOfAdj`: an adjunction `l ⊣ g` makes `f l` an `f`-relative left
  adjoint of `g` (Remark 3.2).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Remark 3.2
-/

universe u v w

namespace UlmerBialgebras.Paper.Rem32

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

section Transpose

variable {c x : Obj} {f g : c ⟶ x} {r : c ⟶ c} (R : RelLeftAdj2 f g r)

/-- The bijection `(p r ⟶ q id) ≃ (p f ⟶ q g)`. -/
def transpose {z : Obj} (p q : z ⟶ c) : (p ≫ r ⟶ q ≫ 𝟙 c) ≃ (p ≫ f ⟶ q ≫ g) where
  toFun γ := R.equiv p q (γ ≫ eqToHom (Category.comp_id q))
  invFun δ := (R.equiv p q).symm δ ≫ eqToHom (Category.comp_id q).symm
  left_inv _ := (comp_eqToHom_iff _ _ _).2 ((R.equiv p q).symm_apply_apply _)
  right_inv δ :=
    (congrArg (R.equiv p q) ((comp_eqToHom_iff _ _ _).2 rfl)).trans
      ((R.equiv p q).apply_symm_apply δ)

end Transpose

section Comparison

variable {c x : Obj} {f g : c ⟶ x} {r : c ⟶ c} (R : RelLeftAdj2 f g r) (I : Inserter f g)
  (I' : Inserter r (𝟙 c))

/-- The canonical comparison `I' ⟶ Ins(f, g)` from an inserter `I'` of `r, id_c`: the lift of
`I'.u` through `I` along the transposed universal 2-cell of `I'`. It lies over `c` (`I.lift_u`). -/
def comparison : I'.pt ⟶ I.pt :=
  I.lift I'.u (transpose R I'.u I'.u I'.φ)

end Comparison

section Datum

variable (B : BialgDatum (Obj := Obj)) {r r' : B.c ⟶ B.c} (R : RelLeftAdj2 B.f B.g r)
  (R' : RelLeftAdj2 B.f' B.g' r') (I' : Inserter r (𝟙 B.c))

/-- A 2-cell `u f' ⟶ u g'` on `Ins(f, g)`, restricted along the comparison from `I'` and
transposed along `r'`: a 2-cell `u' r' ⟶ u'` on `I'`. -/
def transposedEqn (γ : B.ins.u ≫ B.f' ⟶ B.ins.u ≫ B.g') : I'.u ≫ r' ⟶ I'.u ≫ 𝟙 B.c :=
  (transpose R' I'.u I'.u).symm
    (eqToHom (show I'.u ≫ B.f' = comparison R B.ins I' ≫ B.ins.u ≫ B.f' from
        (eq_whisker (B.ins.lift_u _ _).symm B.f').trans (Category.assoc _ _ _)) ≫
      (comparison R B.ins I' ◁ γ) ≫
      eqToHom (show comparison R B.ins I' ≫ B.ins.u ≫ B.g' = I'.u ≫ B.g' from
        (Category.assoc _ _ _).symm.trans (eq_whisker (B.ins.lift_u _ _) B.g')))

/-- The bialgebraic datum `B'` of Remark 3.2 of [forsman2026syntactic], with supports `r, id_c`
and `r', id_c`, on an arbitrary inserter `I'` of `r, id_c`. Its equations are those of `B`,
restricted along `Rem32.comparison` and transposed (`Rem32.transposedEqn`). -/
abbrev transposedDatum : BialgDatum (Obj := Obj) where
  c := B.c
  x := B.c
  y := B.c
  f := r
  g := 𝟙 B.c
  f' := r'
  g' := 𝟙 B.c
  ins := I'
  α := transposedEqn B R R' I' B.α
  β := transposedEqn B R R' I' B.β

end Datum

section Adj

variable {c x : Obj} {l : x ⟶ c} {g : c ⟶ x} (A : TwoAdj l g) (f : c ⟶ x)

/-- An adjunction `l ⊣ g` makes `f l` an `f`-relative left adjoint of `g` (the first case of
Remark 3.2 of [forsman2026syntactic]). -/
def relOfAdj : RelLeftAdj2 f g (f ≫ l) where
  equiv p q := A.relEquiv f p q
  nat_left σ γ := A.relEquiv_nat_left f σ γ
  nat_right γ τ := A.relEquiv_nat_right f γ τ
  nat_z h _ _ γ := A.relEquiv_nat_z f h γ

end Adj

end UlmerBialgebras.Paper.Rem32
