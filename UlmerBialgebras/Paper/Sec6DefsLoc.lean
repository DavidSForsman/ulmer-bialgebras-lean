module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Examples.SignatureEx
public import UlmerBialgebras.Examples.MonModel
public import AffineGroupSchemes.VonNeumannRegular
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import UlmerBialgebras.Paper.Sec3DefsLoc

/-!
# Challenge definitions for Lemma 6.10

* `UlmerBialgebras.Paper.Loc.smonModel C`: a symmetric monoidal category `C` as a model of the
  2-signature `Σ_SMon` (`UlmerBialgebras.SigEx.smonSig`) in `CAT`. The seven transformation symbols
  go to the associator, the two unitors, their inverses, and the symmetry.
* `UlmerBialgebras.Paper.Loc.ModU R`: the category of `R`-modules with its hom-sets lifted to
  `Type (u + 1)`, so that it is an object of `Cat.{u + 1, u + 1}`. The symmetric monoidal
  structure is transported from `ModuleCat.{u} R`.
* `UlmerBialgebras.Paper.Loc.modModel R`: `Mod_R` as a `Σ_SMon`-model.
* `UlmerBialgebras.Paper.Loc.locFunctor R p`: the localization `M ↦ R_p ⊗_R M`.
* `UlmerBialgebras.Paper.Loc.locSig R sg p`: localization on `M₀ = ∏_{s ∈ S} Mod_R`, componentwise.
* `UlmerBialgebras.Paper.Loc.modCatModel R`, `UlmerBialgebras.Paper.Loc.locSigCat R sg p`: the same
  for `ModuleCat.{u} R` itself, in `Cat.{u, u + 1}` (Lemma 6.10 is stated for these; `modModel`
  is its change of universe, used by the old form).

## Main results

* `UlmerBialgebras.Paper.Loc.smonModel`: a symmetric monoidal category as a `Σ_SMon`-model in `CAT`.
* `UlmerBialgebras.Paper.Loc.ModU`, `UlmerBialgebras.Paper.Loc.modModel`: `R`-modules with lifted
  hom-sets, and `Mod_R` as a `Σ_SMon`-model.
* `UlmerBialgebras.Paper.Loc.locFunctor`: the localization `M ↦ R_p ⊗_R M` (Lemma 6.10).
* `UlmerBialgebras.Paper.Loc.locSig`: the localization on `∏_{s ∈ S} Mod_R`, componentwise.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 (`Σ_SMon`), Lemma 6.10
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*]
  [atiyah_introduction_1969], Chapter 3
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory MonoidalCategory

/-! ## The model `Mod_R` and localizations -/

section Mod

variable (R : Type u) [CommRing R]

/-- `R`-modules, with hom-sets lifted to `Type (u + 1)`, carrying the symmetric monoidal
structure transported from `ModuleCat.{u} R`. -/
abbrev ModU : Type (u + 1) :=
  Monoidal.Transported (ULiftHom.equiv : ModuleCat.{u} R ≌ ULiftHom.{u + 1} (ModuleCat.{u} R))

/-- The identification of `ModuleCat.{u} R` with `ModU R`. -/
abbrev modEquiv : ModuleCat.{u} R ≌ ModU R :=
  Monoidal.equivalenceTransported
    (ULiftHom.equiv : ModuleCat.{u} R ≌ ULiftHom.{u + 1} (ModuleCat.{u} R))

/-- **`Mod_R` as a `Σ_SMon`-model in `CAT`.** -/
abbrev modModel : Model SigEx.smonSig Cat.{u + 1, u + 1} := smonModel (ModU R)

/-- The localization `L_p : Mod_R → Mod_{R_p}`, `M ↦ R_p ⊗_R M` (Lemma 6.10 of
[forsman2026syntactic]; Atiyah–Macdonald [atiyah_introduction_1969], Chapter 3). -/
noncomputable def locFunctor (p : Ideal R) [p.IsPrime] : ModU R ⥤ ModU (Localization.AtPrime p) :=
  (modEquiv R).inverse ⋙ ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p)) ⋙
    (modEquiv (Localization.AtPrime p)).functor

/-- The localization `L_p^S : M₀ → N₀` on the product `∏_{s ∈ S} Mod_R`, componentwise. -/
noncomputable def locSig (sg : OneSig SigEx.smonSig) (p : Ideal R) [p.IsPrime] :
    ((modModel R).P0 sg).pt ⟶ ((modModel (Localization.AtPrime p)).P0 sg).pt :=
  ((modModel (Localization.AtPrime p)).P0 sg).lift fun s =>
    (((modModel R).P0 sg).π s ≫
        (locFunctor R p).toCatHom)

/-- **`Mod_R` at its own size, as a `Σ_SMon`-model in `CAT`**: `ModuleCat.{u} R`, an object of
`Cat.{u, u + 1}` (objects in `Type (u + 1)`, morphisms in `Type u`). -/
abbrev modCatModel : Model SigEx.smonSig Cat.{u, u + 1} := smonModel (ModuleCat.{u} R)

/-- The localization `L_p^S : M₀ → N₀` on the product `∏_{s ∈ S} Mod_R` for `modCatModel`,
componentwise `M ↦ R_p ⊗_R M` (`ModuleCat.extendScalars`). -/
noncomputable def locSigCat (sg : OneSig SigEx.smonSig) (p : Ideal R) [p.IsPrime] :
    ((modCatModel R).P0 sg).pt ⟶ ((modCatModel (Localization.AtPrime p)).P0 sg).pt :=
  ((modCatModel (Localization.AtPrime p)).P0 sg).lift fun s =>
    (((modCatModel R).P0 sg).π s ≫
        (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).toCatHom)

end Mod

end UlmerBialgebras.Paper.Loc
