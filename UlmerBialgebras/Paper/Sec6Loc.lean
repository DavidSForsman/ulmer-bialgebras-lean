module

public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc

/-!
# Challenge: Lemma 6.10 (localizations)

`R` is a commutative ring in `Type u`. `Mod_R` is the `Σ_SMon`-model `Loc.modCatModel R`, that is
`ModuleCat.{u} R` in `Cat.{u, u + 1}` (see `UlmerBialgebras/Paper/Sec3DefsLoc.lean`). The form in
`Cat.{u + 1, u + 1}` with lifted hom-sets (`Loc.modModel R`) is kept as a test in
the development repository's `UlmerBialgebrasTest/Specializations/Sec6Loc.lean`. `T` is any theory
over a 1-signature `sg`
relative to `Σ_SMon`; its sorts are `sg.Srt`.

## Main results

* `UlmerBialgebras.Paper.lem_6_10`: lifts `L_p^T : Mod_R^T → Mod_{R_p}^T` of the localizations at
  the maximal ideals exist; every such family is jointly conservative and preserves small sifted
  colimits, and if `R` is von Neumann regular each member preserves finite cosifted limits and
  each `R_p` is a field (Lemma 6.10).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.10
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*]
  [atiyah_introduction_1969], Chapter 3; Chapter 2, Exercise 27; Chapter 3, Exercise 10
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Loc

/-- **Lemma 6.10** ([forsman2026syntactic], §6).

```latex
Let $T$ be a bialgebraic theory, with $S$ as the set of sorts, over the $2$-signature for
symmetric monoidal categories. Then the localizations at maximal ideals $\alpha$ determine a
jointly conservative family 
$$
(L_\alpha^T\colon \Mod_R^T\to\Mod_{R_\alpha}^T)_\alpha
$$
of functors preserving sifted colimits. In the case $R$ is a regular ring, the localization
$L^T_\alpha$ preserves finite cosifted limits and $R_\alpha$ is a field for each maximal ideal
$\alpha$ of $R$.
```

**Reading.**
* $R$ commutative ring ↦ `R : Type u` with `[CommRing R]`.
* $T$ over 1-signature relative to $\Sigma_{\mathrm{SMon}}$ ↦ `sg : OneSig SigEx.smonSig`,
  `T : Theory sg`.
* $\Mod_R^T$ and $\Mod_{R_\alpha}^T$ ↦ `Model.thyObj (modCatModel R) sg T` and
  `Model.thyObj (modCatModel (Localization.AtPrime p)) sg T` in `Cat.{u, u + 1}`, for maximal
  ideals `p : Ideal R` with `[p.IsMaximal]`.
* "localizations at maximal ideals" ↦ existence of localization functors `L p` lifting
  `locSigCat R sg p` along `Model.thyForget`.
* "jointly conservative" ↦ `IsIso f` whenever each localized morphism is an isomorphism.
* "preserving sifted colimits" ↦ `PreservesColimitsOfShape J` for the underlying functor of `L p`
  and any sifted category `J : Type u` with `[SmallCategory J] [IsSifted J]`.
* regular ring clause ↦ `IsVonNeumannRegularRing R` implies `PreservesLimitsOfShape J` for finite
  cosifted shapes `J : Type` and `IsField (Localization.AtPrime p)`.

**Deviations.**
- stronger: proves existence and the stated properties for every family of lifts of the
  localizations, not only for the induced one (CHALLENGE.md, *Stronger than the paper*).
-/
theorem lem_6_10 (R : Type u) [CommRing R] (sg : OneSig SigEx.smonSig) (T : Theory sg) :
    (∃ L : ∀ (p : Ideal R) [p.IsMaximal],
        (modCatModel R).thyObj sg T ⟶ (modCatModel (Localization.AtPrime p)).thyObj sg T,
      ∀ (p : Ideal R) [p.IsMaximal],
        L p ≫ (modCatModel (Localization.AtPrime p)).thyForget sg T =
          (modCatModel R).thyForget sg T ≫ locSigCat R sg p) ∧
    ∀ L : ∀ (p : Ideal R) [p.IsMaximal],
        (modCatModel R).thyObj sg T ⟶ (modCatModel (Localization.AtPrime p)).thyObj sg T,
      (∀ (p : Ideal R) [p.IsMaximal],
        L p ≫ (modCatModel (Localization.AtPrime p)).thyForget sg T =
          (modCatModel R).thyForget sg T ≫ locSigCat R sg p) →
      (∀ ⦃X Y : ((modCatModel R).thyObj sg T : Type (u + 1))⦄ (f : X ⟶ Y),
        (∀ (p : Ideal R) [p.IsMaximal],
          IsIso ((L p).toFunctor.map f)) → IsIso f) ∧
      (∀ (p : Ideal R) [p.IsMaximal] (J : Type u) [SmallCategory J] [IsSifted J],
        PreservesColimitsOfShape J (L p).toFunctor) ∧
      (IsVonNeumannRegularRing R → ∀ (p : Ideal R) [p.IsMaximal],
        (∀ (J : Type) [SmallCategory J] [FinCategory J] [IsCosifted J],
          PreservesLimitsOfShape J (L p).toFunctor) ∧
        IsField (Localization.AtPrime p)) := sorry

end UlmerBialgebras.Paper
