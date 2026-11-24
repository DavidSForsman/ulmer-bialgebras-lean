module

public import InternalGroups.GrpImageFactorization

/-!
# Base change of regular epimorphisms of `Grp C` along monomorphisms

Standing hypotheses, as everywhere in this part of the development: `C` is cartesian monoidal with
finite limits and reflexive coequalizers which the binary product preserves, so that `Grp C` is
pointed, protomodular, finitely complete and has reflexive coequalizers computed in `C`.

`InternalGroups/GrpImageFactorization.lean` produced, from the effectivity of the coset
relations of `C` alone, the **extremal epi–mono factorization** of every morphism of `Grp C`.  This
file adds the one remaining ingredient needed for regularity, in the following form.

> **`InternalGroups.RegularEpiCompHom C`** — for every regular epimorphism `f : X ⟶ Y` of `Grp C`
> and every regular epimorphism `k : U Y ⟶ M` of `C`, the composite `U f ≫ k` is again a regular
> epimorphism of `C`.

The hypothesis is a statement about `C`, not about `Grp C`.  It holds as soon as regular
epimorphisms of `C` are stably epimorphic, hence in particular when `C` is regular (this
implication is not formalized here); but it is weaker, since it only constrains the underlying
morphisms of the regular epimorphisms of `Grp C`.

## Main results

* `InternalGroups.isRegularEpi_quot_p_hom`: the coset quotient of a subgroup object is a regular
  epimorphism of `C`.
* `InternalGroups.RegularEpiCosetCompHom`: the hypothesis that `U f` composed with a coset
  quotient of `C` is a regular epimorphism of `C`, for every regular epimorphism `f` of `Grp C`.
* `InternalGroups.isExtremalEpi_of_isPullback_of_mono`: given effective coset relations and
  `RegularEpiCosetCompHom C`, the base change of a regular epimorphism of `Grp C` along a
  monomorphism is an extremal epimorphism.
* `InternalGroups.isBarrExact_grp_of_comp`: given effective coset relations and
  `RegularEpiCosetCompHom C`, `Grp C` is Barr exact.

## The argument

Let `f : X ⟶ Y` be a regular epimorphism of `Grp C`, `n : N ⟶ Y` a monomorphism, and

```
P ---p₂--> N
|          |
p₁         n
v          v
X ---f---> Y
```

a pullback square.  Write `s ≤ Y` for the subgroup object `n`, `p : U Y ⟶ U Y / N` for its coset
quotient — a regular epimorphism *of `C`*, since the coset quotient is a reflexive coequalizer
computed in `C` (`InternalGroups.isRegularEpi_quot_p_hom`) — and `p'` for the quotient of `U Y`
by the image of `p₁ ≫ f`.

* By the hypothesis, `v := U f ≫ p` is a regular epimorphism of `C`, hence the coequalizer of its
  kernel pair `a, b : R ⇉ U X`.
* The "difference" `δ := (a ≫ U f)⁻¹ * (b ≫ U f)` is killed by `p`
  (`InternalGroups.kills_inv_mul_iff`), so — and this is the only place where the effectivity of
  the coset relations enters — it factors through `N`; the pullback square then lifts it to
  `R ⟶ U P`, so it is also killed by `p'`.
* Therefore `a` and `b` agree after `U f ≫ p'`, which descends along the coequalizer `v` to a map
  `h` with `p ≫ h = p'`, whence `n` is killed by `p'`: the subgroup object `N` is **contained in
  the image of `p₁ ≫ f`** (`InternalGroups.le_grpImage_of_isPullback`).
* The reverse inclusion is the minimality of the image, so the two agree and `p₂` is, up to that
  isomorphism, the corestriction of `p₁ ≫ f` to its image: an **extremal epimorphism**
  (`InternalGroups.isExtremalEpi_of_isPullback_of_mono`).

## Consequences

Kernels are monomorphisms, so regular epimorphisms of `Grp C` are stable along kernels
(`InternalGroups.regularEpiStableAlongKernels_grp_of_comp`) and hence **closed under
composition**; extremal epimorphisms are then regular
(`InternalGroups.isRegularEpi_of_isExtremalEpi_grp_of_comp`), sections are monomorphisms, and the
reduction of the development repository's `InternalGroups/GrpRegularFromCoset.lean` applies:

* `InternalGroups.extremalEpiStableAlongSections_grp_of_comp`;
* `InternalGroups.isBarrExact_grp_of_comp`: **`Grp C` is Barr exact** (in particular regular).

Whether the regularity of `Grp C` gives back `RegularEpiCompHom C` — a statement about regular
epimorphisms of `C` that need not be of the form `U f` — is not settled here, so
`RegularEpiCompHom` is offered as a *sufficient* condition only.

Everything below is in fact run on the weaker hypothesis `InternalGroups.RegularEpiCosetCompHom C`,
which asks the same only of the composites of `U f` with the *coset quotients* of `C`; these are
the only regular epimorphisms of `C` the argument ever composes with.  That weakening matters,
because the coset form *is* equivalent to the exactness of `Grp C`; the converse (not formalized)
is discussed in the development repository's `InternalGroups/GrpExactMainTheorem.lean`, where the
main theorem is also
assembled into a single statement.

## References

* [M. Barr, *Exact categories*][Ba]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory CategoryTheory.LiftedOFS

open CategoryTheory.LiftedOFS

/-! ## Composition of regular epimorphisms from stable epimorphy -/

section RegularEpiComp

variable {D : Type u} [Category.{v} D] [HasPullbacks D]

end RegularEpiComp


/-! ## Differences and the quotient map -/

section Difference

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G : C} [GrpObj G]

/-- **Two generalized elements have the same image in a quotient module exactly when their
"difference" is killed.** -/
lemma kills_inv_mul_iff (q : QuotMod G) {T : C} (x y : T ⟶ G) :
    Kills q (x⁻¹ * y) ↔ x ≫ q.p.hom = y ≫ q.p.hom := by
  constructor
  · intro h
    conv_rhs => rw [show y = x * (x⁻¹ * y) from (mul_inv_cancel_left x y).symm]
    rw [comp_p_eq_act, comp_p_eq_act, act_mul, (kills_iff_act q _).1 h]
  · intro h
    rw [kills_iff_act, act_mul, ← comp_p_eq_act, ← h, comp_p_eq_act, ← act_mul, inv_mul_cancel,
      act_one]

end Difference

/-! ## The coset quotient as a regular epimorphism of `C` -/

section CosetQuotRegular

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

/-- **The coset quotient of a subgroup object is a regular epimorphism of `C`.**  It is the
coequalizer, in `C`, of the coset relation (`InternalGroups.isColimitCoforkQuot`). -/
theorem isRegularEpi_quot_p_hom {G : C} [GrpObj G] (s : SubGrp G) :
    IsRegularEpi (s.quot).p.hom := by
  have hpres := CategoryTheory.Mod_.preservesReflexiveCoequalizers_forget (A := G)
    (fun _ => inferInstance)
  exact ⟨⟨{ W := G ⊗ s.N
            left := cosetMul s
            right := fst G s.N
            w := cosetMul_comp_quot_p s
            isColimit := isColimitCoforkQuot s hpres }⟩⟩

end CosetQuotRegular

section Main

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

variable (C)

/-- **Regular epimorphisms of `Grp C` compose, in `C`, with regular epimorphisms of `C`.**  This
is the hypothesis isolated in this file: for a regular epimorphism `f : X ⟶ Y` of `Grp C` and a
regular epimorphism `k : U Y ⟶ M` of `C`, the composite `U f ≫ k` is a regular epimorphism
of `C`. -/
def RegularEpiCompHom : Prop :=
  ∀ ⦃X Y : Grp C⦄ {f : X ⟶ Y}, IsRegularEpi f →
    ∀ ⦃M : C⦄ {k : Y.X ⟶ M}, IsRegularEpi k → IsRegularEpi (f.hom.hom ≫ k)

/-- **The coset form of the hypothesis**, which is all that the argument of this file uses: for a
regular epimorphism `f : X ⟶ Y` of `Grp C` and a subgroup object `s ≤ Y`, the composite of `U f`
with the coset quotient `U Y ⟶ U Y / s` is a regular epimorphism of `C`.

Unlike `InternalGroups.RegularEpiCompHom`, this condition is *equivalent* to the exactness of
`Grp C`; see the discussion of the (unformalized) converse in
the development repository's `InternalGroups/GrpExactMainTheorem.lean`. -/
def RegularEpiCosetCompHom : Prop :=
  ∀ ⦃X Y : Grp C⦄ {f : X ⟶ Y}, IsRegularEpi f → ∀ s : SubGrp Y.X,
    IsRegularEpi (f.hom.hom ≫ (s.quot).p.hom)

variable {C}

/-- The coset form of the hypothesis is weaker: coset quotients are regular epimorphisms of `C`,
so this is an instance of `InternalGroups.RegularEpiCompHom`. -/
theorem regularEpiCosetCompHom_of_comp (h : RegularEpiCompHom C) : RegularEpiCosetCompHom C :=
  fun _X _Y _f hf s => h hf (isRegularEpi_quot_p_hom s)

variable [HasFiniteLimits C] [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-! ## The key computation -/

/-- **The subgroup object along which a regular epimorphism is pulled back is contained in the
image of the other projection.**

Concretely: if `f : X ⟶ Y` is a regular epimorphism of `Grp C`, `n : N ⟶ Y` a monomorphism and
`p₁, p₂` a pullback of `f` along `n`, then `N`, viewed as a subgroup object of `Y`, is contained
in the image of `p₁ ≫ f`.  This is the heart of the file. -/
theorem le_grpImage_of_isPullback (hinj : CosetInjective C) (hcomp : RegularEpiCosetCompHom C)
    {X Y N P : Grp C} {f : X ⟶ Y} {n : N ⟶ Y} {p₁ : P ⟶ X} {p₂ : P ⟶ N}
    (hf : IsRegularEpi f) [Mono n] (hsq : IsPullback p₁ p₂ f n) :
    ∃ w : N.X ⟶ (grpImage (p₁ ≫ f)).N, w ≫ (grpImage (p₁ ≫ f)).i = n.hom.hom := by
  have := hf
  have : Mono n.hom.hom := mono_hom_of_mono n
  -- the coset quotient of the subgroup object `N ≤ Y`, packaged by the three properties used
  obtain ⟨q, hqreg, hqn, hqfac⟩ : ∃ q : QuotMod Y.X, IsRegularEpi (f.hom.hom ≫ q.p.hom) ∧
      Kills q n.hom.hom ∧
      ∀ {T : C} {g : T ⟶ Y.X}, Kills q g → ∃ k : T ⟶ N.X, k ≫ n.hom.hom = g :=
    ⟨(⟨N.X, n.hom.hom⟩ : SubGrp Y.X).quot,
      hcomp hf _, kills_quot_i _,
      fun {_T _g} hg => factors_of_kills_quot _ (hinj Y.X _) hg⟩
  -- the quotient of `Y` by the image of `p₁ ≫ f`
  obtain ⟨q', hq'kill, hq'fac⟩ : ∃ q' : QuotMod Y.X, Kills q' (p₁ ≫ f).hom.hom ∧
      ∀ {T : C} {g : T ⟶ Y.X}, Kills q' g →
        ∃ k : T ⟶ (grpImage (p₁ ≫ f)).N, k ≫ (grpImage (p₁ ≫ f)).i = g :=
    ⟨homQuot isTerminalTensorUnit (p₁ ≫ f).hom.hom, kills_grpImage (p₁ ≫ f),
      fun {_T g} hg => (kills_iff_factors _ g).1 hg⟩
  -- `U f ≫ p` is a regular epimorphism of `C`, hence the coequalizer of its kernel pair
  have hv : IsRegularEpi (f.hom.hom ≫ q.p.hom) := hqreg
  obtain ⟨R, a, b, hkp⟩ : ∃ (R : C) (a b : R ⟶ X.X), IsKernelPair (f.hom.hom ≫ q.p.hom) a b :=
    ⟨_, _, _, IsKernelPair.of_hasPullback _⟩
  have hcolim : IsColimit (Cofork.ofπ (f.hom.hom ≫ q.p.hom) hkp.w) := hkp.toCoequalizer'
  have halbe : (a ≫ f.hom.hom) ≫ q.p.hom = (b ≫ f.hom.hom) ≫ q.p.hom := by
    rw [Category.assoc, Category.assoc]; exact hkp.w
  -- the difference of the two legs is killed by the coset quotient, so it factors through `N`
  obtain ⟨psi, hpsi⟩ := hqfac ((kills_inv_mul_iff q _ _).2 halbe)
  have hdeX : (a⁻¹ * b : R ⟶ X.X) ≫ f.hom.hom = (a ≫ f.hom.hom)⁻¹ * (b ≫ f.hom.hom) := by
    rw [MonObj.mul_comp, GrpObj.inv_comp]
  have hsqC : IsPullback p₁.hom.hom p₂.hom.hom f.hom.hom n.hom.hom := hsq.map (Grp.forget C)
  obtain ⟨d, hd₁⟩ : ∃ d : R ⟶ P.X, d ≫ p₁.hom.hom = a⁻¹ * b :=
    ⟨hsqC.lift (a⁻¹ * b) psi (hdeX.trans hpsi.symm), hsqC.lift_fst _ _ _⟩
  -- hence it is also killed by the quotient by the image of `p₁ ≫ f`
  have hdeq' : Kills q' ((a ≫ f.hom.hom)⁻¹ * (b ≫ f.hom.hom)) := by
    have hk := hq'kill.comp d
    have hdd : d ≫ (p₁ ≫ f).hom.hom = (a ≫ f.hom.hom)⁻¹ * (b ≫ f.hom.hom) := by
      rw [show (p₁ ≫ f).hom.hom = p₁.hom.hom ≫ f.hom.hom from rfl, ← Category.assoc, hd₁, hdeX]
    rwa [hdd] at hk
  have hab : a ≫ (f.hom.hom ≫ q'.p.hom) = b ≫ (f.hom.hom ≫ q'.p.hom) := by
    rw [← Category.assoc, ← Category.assoc]
    exact (kills_inv_mul_iff q' _ _).1 hdeq'
  -- descend along the coequalizer
  have hdesc : (f.hom.hom ≫ q.p.hom) ≫ hcolim.desc (Cofork.ofπ (f.hom.hom ≫ q'.p.hom) hab)
      = f.hom.hom ≫ q'.p.hom := Cofork.IsColimit.π_desc hcolim
  have := isRegularEpi_hom_of_isRegularEpi f hf
  have : Epi f.hom.hom := inferInstance
  have hpp : q.p.hom ≫ hcolim.desc (Cofork.ofπ (f.hom.hom ≫ q'.p.hom) hab) = q'.p.hom := by
    refine (cancel_epi f.hom.hom).1 ?_
    rw [← Category.assoc]
    exact hdesc
  -- so `n` is killed by the quotient by the image of `p₁ ≫ f`
  have hqn' : n.hom.hom ≫ q.p.hom = pt q N.X := hqn
  refine hq'fac (?_ : n.hom.hom ≫ q'.p.hom = pt q' N.X)
  rw [← hpp, ← Category.assoc, hqn', pt, pt, Category.assoc]
  congr 1
  rw [QuotMod.basePoint, QuotMod.basePoint, Category.assoc, hpp]

/-- **The base change of a regular epimorphism of `Grp C` along a monomorphism is an extremal
epimorphism**, granting effective coset relations and `InternalGroups.RegularEpiCompHom`. -/
theorem isExtremalEpi_of_isPullback_of_mono (hinj : CosetInjective C)
    (hcomp : RegularEpiCosetCompHom C)
    {X Y N P : Grp C} {f : X ⟶ Y} {n : N ⟶ Y} {p₁ : P ⟶ X} {p₂ : P ⟶ N}
    (hf : IsRegularEpi f) [Mono n] (hsq : IsPullback p₁ p₂ f n) : IsExtremalEpi p₂ := by
  have : Mono n.hom.hom := mono_hom_of_mono n
  obtain ⟨w, hw⟩ := le_grpImage_of_isPullback hinj hcomp hf hsq
  have hp₂ : p₂.hom.hom ≫ n.hom.hom = (p₁ ≫ f).hom.hom :=
    (congrArg (fun t : P ⟶ Y => t.hom.hom) hsq.w).symm
  -- the image of `p₁ ≫ f` is contained in `N` by minimality
  obtain ⟨gg, hgn⟩ : ∃ gg : (grpImageObj (p₁ ≫ f)).X ⟶ N.X,
      gg ≫ n.hom.hom = (grpImage (p₁ ≫ f)).i :=
    grpImage_le hinj (p₁ ≫ f) ⟨N.X, n.hom.hom⟩ p₂.hom.hom hp₂
  -- the two inclusions are mutually inverse
  have hwg : w ≫ gg = 𝟙 N.X := by
    refine (cancel_mono n.hom.hom).1 ?_
    rw [Category.assoc, hgn, hw]
    simp
  have hgw : gg ≫ w = 𝟙 (grpImageObj (p₁ ≫ f)).X := by
    refine (cancel_mono (grpImage (p₁ ≫ f)).i).1 ?_
    rw [Category.assoc, hw, hgn]
    simp
  have : IsIso gg := ⟨w, hgw, hwg⟩
  have : IsMonHom gg := by
    have : IsMonHom (gg ≫ n.hom.hom) := by rw [hgn]; infer_instance
    exact Internal.isMonHom_of_comp_mono gg n.hom.hom
  have : IsIso (Grp.homMk gg : grpImageObj (p₁ ≫ f) ⟶ N) :=
    isIso_of_isIso_hom _ (id (inferInstance : IsIso gg))
  have hfac : grpImageFactor (p₁ ≫ f) ≫ (Grp.homMk gg : grpImageObj (p₁ ≫ f) ⟶ N) = p₂ := by
    ext
    change grpImageHom (p₁ ≫ f) ≫ gg = p₂.hom.hom
    refine (cancel_mono n.hom.hom).1 ?_
    rw [Category.assoc, hgn, grpImageHom_comp (p₁ ≫ f)]
    exact hp₂.symm
  rw [← hfac]
  exact isExtremalEpi_comp_isIso (isExtremalEpi_grpImageFactor hinj (p₁ ≫ f))

end Main

end InternalGroups
