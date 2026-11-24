module

public import Hopf.Basic.ComoduleTransl

/-!
# Local finiteness of comodules

The *fundamental theorem of comodules*: over a field, every element of a comodule lies in a
finite-dimensional subcomodule.  This is the input to Takeuchi's Corollary 2.3
(*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972)),
where it is quoted from Sweedler's book as "a finite dimensional subspace of a comodule generates
a finite dimensional subcomodule".

The subcomodule in question is described explicitly in `Hopf/Basic/ComoduleTransl.lean`:
it is the span `Coalgebra.Comodule.translSpan m` of all translates `u ⇀ m` of `m` by functionals on
the coalgebra, the smallest subcomodule containing `m`.  (The notion of a subcomodule itself,
`Coalgebra.Comodule.IsSubcomodule`, is defined in `Hopf/Basic/Comodule.lean`.)

## Main results

* `Coalgebra.Comodule.exists_fg_subcomodule`: every element of a comodule over a field lies in a
  finitely generated subcomodule.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter II
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Corollary 2.3
-/

@[expose] public section

section
namespace Coalgebra.Comodule

variable {k C M : Type*} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup M] [Module k M] [RightComodule k C M]

/-- **Fundamental theorem of comodules**: every element of a comodule over a field lies in a
finitely generated subcomodule, namely in the span of its translates.
([waterhouseIntroductionAffineGroup1979], Section 3.3.) -/
theorem exists_fg_subcomodule (m : M) :
    ∃ N : Submodule k M, m ∈ N ∧ N.FG ∧ IsSubcomodule (C := C) N :=
  ⟨translSpan (k := k) (C := C) m, self_mem_translSpan m, translSpan_fg m,
    isSubcomodule_translSpan m⟩

end Coalgebra.Comodule
end
