module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Monadicity.BigMonadicity

/-!
# From `κ_≤`-cocompleteness to colimits of all short well-ordered chains

The paper's `κ_≤`-cocompleteness (`HasChainColimitsUpTo κ C`: colimits of the chains
`μ.ord.ToType` for infinite cardinals `μ ≤ κ`) gives colimits of every nonempty well-ordered
chain of cardinality at most `κ` (`HasChainColimitsLE κ C`, the hypothesis of the
development's monadicity theorems):

* a chain with a largest element has that element as a terminal object;
* otherwise it has no maximal element, its cofinality `μ := Order.cof J` is an infinite
  cardinal at most `κ`, and a cofinal subset of order type `μ.ord` gives a final functor
  `μ.ord.ToType ⥤ J`.

## Main results

* `UlmerBialgebras.Paper.hasChainColimitsLE_of_upTo`: `HasChainColimitsUpTo κ C` implies
  `HasChainColimitsLE κ C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 5.4, used in Theorems 5.5 and 5.7
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Ordinal Cardinal

/-- A `κ_≤`-cocomplete category (Definition 5.4 of [forsman2026syntactic]) has colimits of all
nonempty well-ordered chains of cardinality at most `κ`: such a chain either has a largest
element or contains a cofinal `μ`-chain for its cofinality `μ`, an infinite cardinal `≤ κ`. -/
theorem hasChainColimitsLE_of_upTo {κ : Cardinal.{w}} {C : Type u} [Category.{v} C]
    (h : HasChainColimitsUpTo κ C) : HasChainColimitsLE κ C := by
  intro J _ _ _ hJ
  by_cases hmax : ∃ m : J, ∀ j, j ≤ m
  · obtain ⟨m, hm⟩ := hmax
    have ht : IsTerminal m :=
      IsTerminal.ofUniqueHom (fun j => homOfLE (hm j)) (fun _ _ => Subsingleton.elim _ _)
    exact ⟨fun F => ⟨⟨⟨_, colimitOfDiagramTerminal ht F⟩⟩⟩⟩
  push Not at hmax
  have : NoMaxOrder J := ⟨fun m => by
    obtain ⟨j, hj⟩ := hmax m
    exact ⟨j, hj⟩⟩
  -- `J` has no largest element, so its cofinality `μ` is infinite
  let μ : Cardinal.{w} := Order.cof J
  have hμ : ℵ₀ ≤ μ := Order.aleph0_le_cof
  have hμκ : μ ≤ κ := (Order.cof_le_cardinalMk J).trans hJ
  have : HasColimitsOfShape μ.ord.ToType C := h _ hμ hμκ
  -- a cofinal subset of order type `μ.ord`, as a final functor
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq J
  have hiso : Nonempty ((· < · : μ.ord.ToType → μ.ord.ToType → Prop) ≃r
      (· < · : s → s → Prop)) := by
    rw [← type_eq, type_toType, hs']
  let e : μ.ord.ToType ≃o s := OrderIso.ofRelIsoLT hiso.some
  let G : μ.ord.ToType → J := fun x => (e x).1
  have hGmono : Monotone G := fun x y hxy => e.monotone hxy
  have : hGmono.functor.Final := by
    rw [Monotone.final_functor_iff]
    intro j
    obtain ⟨t, ht, hjt⟩ := hs j
    exact ⟨e.symm ⟨t, ht⟩, by simpa [G] using hjt⟩
  exact Functor.Final.hasColimitsOfShape_of_final hGmono.functor

end UlmerBialgebras.Paper
