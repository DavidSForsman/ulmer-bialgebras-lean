module

public import UlmerBialgebras.Paper.Sec6DefsTheoryMorphism

/-!
# The single-sorted theories of monoids, commutative monoids and groups

Definitions for `Companion/Statements/ExtrasClassical.lean` (an addition beyond the paper). The
equations
are written as the axioms of Mathlib's `MonObj`, `IsCommMonObj` and `GrpObj`, in the syntax of
`MSLanguage`, so that their models can be compared directly with Mathlib's `Mon C`, `CommMon C`
and `Grp C`.

* `restrict`: the sublanguage with some of the function symbols, and its inclusion
  `LangMorphism.ofRestrict` (each symbol is itself).
* `monLanguage`: the language of groups at one sort without the inverse: a binary `mul` and a
  constant `one`.
* `monTheory`: `one_mul`, `mul_one`, `mul_assoc` (the axioms of `MonObj`).
* `cmonTheory`: `monTheory` and `mul_comm` (the axiom of `IsCommMonObj`), so
  `monTheory ⊆ cmonTheory`.
* The single-sorted theory of groups is `grpEqTheory Unit` of
`UlmerBialgebras/Paper/Sec6DefsAlgTheory.lean`;
  its equations are those of `MonObj` and `GrpObj` (`left_inv`, `right_inv`).
* `monTheory_ofRestrict_mem`: the axioms of monoids are axioms of groups.
* `monCMonMorphism : T_Mon → T_CMon` (the inclusion) and `monGrpMorphism : T_Mon → T_Grp` (the
  sublanguage without the inverse), morphisms of theories (`TheoryMorphism`), whose
  induced functors are the forgetful functors `CommMon C ⥤ Mon C` and `Grp C ⥤ Mon C`.

## Main results

* `UlmerBialgebras.Paper.MSLanguage.monTheory`, `UlmerBialgebras.Paper.MSLanguage.cmonTheory`
* `UlmerBialgebras.Paper.MSLanguage.monCMonMorphism`
* `UlmerBialgebras.Paper.MSLanguage.monGrpMorphism`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapter 1
-/

@[expose] public section

universe v u u₄ u₅

namespace UlmerBialgebras.Paper.MSLanguage

open CategoryTheory Limits

/-- The **language of monoids**: the language of groups at one sort, without the inverse. -/
abbrev monLanguage : MSLanguage.{0, 0} := (grpLanguage Unit).restrict (fun f => f.2 ≠ .inv)

/-- `x * y`. -/
abbrev monMul {n : ℕ} {Γ : Fin n → Unit} (x y : monLanguage.Term Γ ()) : monLanguage.Term Γ () :=
  .func (L := monLanguage) ⟨((), .mul), nofun⟩ ![x, y]

/-- `1`. -/
abbrev monOne {n : ℕ} {Γ : Fin n → Unit} : monLanguage.Term Γ () :=
  .func (L := monLanguage) ⟨((), .one), nofun⟩ (fun j => (j : Fin 0).elim0)

/-- The variable `xᵢ`. -/
abbrev monVar {n : ℕ} (i : Fin n) : monLanguage.Term (fun _ : Fin n => ()) () :=
  .var (L := monLanguage) i

/-- The axioms of monoids. -/
inductive MonEqn | one_mul | mul_one | mul_assoc
  deriving DecidableEq

/-- The axioms of `MonObj`: `1 * x = x`, `x * 1 = x`, `(x * y) * z = x * (y * z)`. -/
def monEquation : MonEqn → monLanguage.Equation
  | .one_mul => ⟨1, fun _ => (), (), monMul monOne (monVar 0), monVar 0⟩
  | .mul_one => ⟨1, fun _ => (), (), monMul (monVar 0) monOne, monVar 0⟩
  | .mul_assoc => ⟨3, fun _ => (), (), monMul (monMul (monVar 0) (monVar 1)) (monVar 2),
      monMul (monVar 0) (monMul (monVar 1) (monVar 2))⟩

/-- The axiom of `IsCommMonObj`: `y * x = x * y` (the braiding followed by `mul` is `mul`). -/
def mulCommEquation : monLanguage.Equation :=
  ⟨2, fun _ => (), (), monMul (monVar 1) (monVar 0), monMul (monVar 0) (monVar 1)⟩

/-- **The theory of monoids.** -/
def monTheory : monLanguage.Theory := Set.range monEquation

/-- **The theory of commutative monoids.** -/
def cmonTheory : monLanguage.Theory := insert mulCommEquation monTheory

/-- The theory of monoids is contained in that of commutative monoids. -/
lemma monTheory_subset_cmonTheory : monTheory ⊆ cmonTheory := Set.subset_insert _ _

/-- The axioms of monoids are axioms of groups (along the inclusion of the language of
monoids). -/
lemma monTheory_ofRestrict_mem : ∀ φ ∈ monTheory,
    (LangMorphism.ofRestrict (L := grpLanguage Unit) (fun f => f.2 ≠ .inv)).translateEquation φ ∈
      grpEqTheory Unit := by
  rintro _ ⟨e, rfl⟩
  refine ⟨((), match e with
    | .one_mul => .oneMul | .mul_one => .mulOne | .mul_assoc => .assoc), ?_⟩
  cases e <;>
  · simp only [grpEquation, monEquation, LangMorphism.translateEquation, LangMorphism.translate,
      LangMorphism.ofRestrict, Term.subst]
    congr 1 <;>
    repeat' first
      | rfl
      | (refine congrArg (Term.func _) (funext fun i => ?_); fin_cases i)

/-- **The morphism of theories `T_Mon → T_CMon`**: the inclusion `monTheory ⊆ cmonTheory`. -/
def monCMonMorphism : TheoryMorphism monTheory cmonTheory :=
  TheoryMorphism.ofLE monTheory_subset_cmonTheory

/-- **The morphism of theories `T_Mon → T_Grp`**: the inclusion of the language of monoids into
that of groups, which sends the axioms of monoids to axioms of groups. -/
def monGrpMorphism : TheoryMorphism monTheory (grpEqTheory Unit) :=
  TheoryMorphism.ofRestrict monTheory_ofRestrict_mem

end UlmerBialgebras.Paper.MSLanguage
