module

public import Hopf.Cocommutative.DescentFreeBasis

/-!
# A right `K`-linear retraction `H ↠ K` for a sub-Hopf algebra `K`

Sweedler's freeness theorem, via the graded Sweedler bases of `Hopf/Graded/` (see
`Hopf/Cocommutative/DescentFreeBasis.lean`), provides a right `(K ∩ H₁)`-linear retraction of
`K ∩ H₁ ⊆ H₁` for every sub-Hopf algebra `K` of a pointed cocommutative Hopf algebra `H`
(`HopfAlgebra.Cocommutative.exists_rightRetraction_of_rightCompl`).  The translation machinery of
`Hopf/Cocommutative/DescentTranslates.lean` extends it, along the Kostant decomposition
`K = ⨆_{d ∈ G(K)} d · (K ∩ H₁)`, to a right `K`-linear retraction `H ↠ K`; this is what
Masuoka's coring argument needs.

## Main result

* `HopfAlgebra.Cocommutative.exists_rightRetraction_subHopf` — for a pointed cocommutative Hopf
  algebra `H` over a field and a sub-Hopf algebra `K`, there is a `k`-linear `E : H → H` with values
  in `K`, restricting to the identity on `K` and satisfying `E (x a) = E x · a` for `a ∈ K`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [D. E. Radford, *Pointed Hopf algebras are free over Hopf
  subalgebras*][radfordPointedHopfAlgebras1977]
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
-/

@[expose] public section


open TensorProduct Coalgebra Coalgebra.Coradical HopfAlgebra

namespace HopfAlgebra.Cocommutative

universe u

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- **The retraction `H ↠ K`.**  For a pointed cocommutative Hopf algebra `H` over a field and a
sub-Hopf algebra `K`, the algebra `K` is a direct summand of `H` as a right `K`-module. -/
theorem exists_rightRetraction_subHopf (hpt : Coalgebra.Coradical.IsPointed k H)
    {K : Subalgebra k H}
    (hK : HopfAlgebra.IsSubHopfAlgebra k K) :
    ∃ E : H →ₗ[k] H, (∀ x : H, E x ∈ K) ∧ (∀ a ∈ K, E a = a) ∧
      (∀ (x : H), ∀ a ∈ K, E (x * a) = E x * a) := by
  classical
  rcases subsingleton_or_nontrivial H with hsub | hnt
  · refine ⟨LinearMap.id, fun x => ?_, fun a _ => rfl, fun x a _ => ?_⟩
    · have : x = 0 := Subsingleton.elim _ _
      rw [this]; exact K.zero_mem
    · exact Subsingleton.elim _ _
  · -- the retraction onto `A = K ∩ H₁`, from Sweedler's freeness theorem
    obtain ⟨N, hsup, hdisj, hstable⟩ :=
      exists_leftCompl_of_hasGradedFreeBasis (Coalgebra.Coradical.toSubmodule_irrPart_le K)
        (HopfAlgebra.Cocommutative.hasGradedFreeBasis_irrPart hK)
    obtain ⟨N', hsup', hdisj', hstable'⟩ :=
      exists_rightCompl_of_leftCompl (fun _ ha => antipode_mem_irrPart hK ha)
        hsup hdisj hstable
    obtain ⟨pA, hpAmem, hpAid, hpAmul⟩ :=
      HopfAlgebra.Cocommutative.exists_rightRetraction_of_rightCompl hpt hsup' hdisj' hstable'
    -- extend it along the Kostant decomposition of `K`
    have hconj := Coalgebra.Coradical.conjStable_glSubgroup hK
    have hKeq := Coalgebra.Coradical.toSubmodule_eq_transComponent hpt hK
    refine ⟨transProj (Coalgebra.Coradical.glSubgroup K hK) pA hpt, fun x => ?_,
      fun a ha => ?_,
      fun x a ha => ?_⟩
    · have := HopfAlgebra.Cocommutative.transProj_mem hconj hpAmem hpt x
      rw [← hKeq] at this
      exact this
    · refine transProj_id hconj (Coalgebra.Coradical.toSubmodule_irrPart_le K) hpAid hpt ?_
      rw [← hKeq]
      exact ha
    · refine transProj_mul hconj (Coalgebra.Coradical.toSubmodule_irrPart_le K) hpAmul hpt
        x ?_
      rw [← hKeq]
      exact ha

end HopfAlgebra.Cocommutative
