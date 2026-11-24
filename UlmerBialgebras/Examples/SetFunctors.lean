module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Foundations.CategoryTheory.Limits.OpTranslate
public import Foundations.CategoryTheory.Limits.PiColimits

/-!
# The functors interpreting `Σ` in `(Set, ×, 1, (−) + 1)`

This file collects the functors used in Examples 3.20 (3) to interpret the cartesian
2-signature of the theory of fields in `Set = Type u`, together with the preservation
properties needed for **Corollary 4.21**:

* `UlmerBialgebras.prodFunctor` — the binary product `× : Set² → Set`; it preserves **all** limits
  (`UlmerBialgebras.preservesLimitsOfShape_prodFunctor`) since it is a right adjoint, and it
  preserves all colimits in each variable separately (`UlmerBialgebras.prodRightAdj`,
  `UlmerBialgebras.prodLeftAdj`), each one-variable functor being a left adjoint;
* `UlmerBialgebras.unitFunctor` — the constant functor at a singleton, on the empty power of `Set`;
* `UlmerBialgebras.optionFunctor` — the maybe functor `(−) + 1`; it preserves **connected** limits
  (`UlmerBialgebras.preservesLimitsOfShape_option`) and **connected** colimits
  (`UlmerBialgebras.preservesColimitsOfShape_option`).

Note that `(−) + 1` really does *not* preserve all colimits (the empty colimit is not
preserved), which is why only connected — in particular sifted — colimits are considered.

## Main results

* `UlmerBialgebras.preservesLimitsOfShape_prodFunctor`: the binary product of sets preserves limits.
* `UlmerBialgebras.prodRightAdj`, `UlmerBialgebras.prodLeftAdj`: the product with a fixed set, in
  either variable, is a left adjoint.
* `UlmerBialgebras.preservesLimitsOfShape_option`: the functor `(−) + 1` preserves connected limits.
* `UlmerBialgebras.preservesColimitsOfShape_option`: the functor `(−) + 1` preserves connected
  colimits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.20
  (3), Corollary 4.21
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## The binary product -/

/-- The binary product of types, as a functor on the two-fold power of `Type u`. -/
@[simps]
def prodFunctor : (∀ _ : Fin 2, Type u) ⥤ Type u where
  obj p := p 0 × p 1
  map f := ↾fun x => (f 0 x.1, f 1 x.2)

/-- The functor `X ↦ X × a`. -/
@[simps]
def prodRight (a : Type u) : Type u ⥤ Type u where
  obj X := X × a
  map f := ↾fun p => (f p.1, p.2)

/-- The functor `X ↦ a × X`. -/
@[simps]
def prodLeft (a : Type u) : Type u ⥤ Type u where
  obj X := a × X
  map f := ↾fun p => (p.1, f p.2)

/-- `X ↦ X × a` is left adjoint to `Z ↦ (a → Z)`. -/
def prodRightAdj (a : Type u) : prodRight a ⊣ coyoneda.obj (Opposite.op a) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾fun x => ↾fun y => f (x, y)
          invFun := fun g => ↾fun p => (show a ⟶ _ from g p.1) p.2
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } }

/-- `X ↦ a × X` is left adjoint to `Z ↦ (a → Z)`. -/
def prodLeftAdj (a : Type u) : prodLeft a ⊣ coyoneda.obj (Opposite.op a) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾fun x => ↾fun y => f (y, x)
          invFun := fun g => ↾fun p => (show a ⟶ _ from g p.2) p.1
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } }

/-- The constant functor at a singleton, on the empty power of `Type u`. -/
@[reducible] def unitFunctor : (∀ _ : Fin 0, Type u) ⥤ Type u :=
  (Functor.const (∀ _ : Fin 0, Type u)).obj PUnit

/-- The maybe functor `(−) + 1` on `Type u`. -/
@[simps]
def optionFunctor : Type u ⥤ Type u where
  obj X := Option X
  map f := ↾Option.map f
  map_id X := by ext x; cases x <;> rfl
  map_comp f g := by ext x; cases x <;> rfl

/-- The maybe functor on the one-fold power of `Type u`. -/
@[reducible] def succFunctor : (∀ _ : Fin 1, Type u) ⥤ Type u :=
  Pi.eval (fun _ : Fin 1 => Type u) 0 ⋙ optionFunctor

variable {J : Type v} [Category.{w} J]

/-! ## Preservation properties -/

/-- `X ↦ X × a` preserves colimits: it is left adjoint to `Hom(a, −)`. -/
noncomputable instance prodRightPreservesColimitsOfShape (a : Type u) :
    PreservesColimitsOfShape J (prodRight a) :=
  (prodRightAdj a).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- `X ↦ a × X` preserves colimits: it is left adjoint to `Hom(a, −)`. -/
noncomputable instance prodLeftPreservesColimitsOfShape (a : Type u) :
    PreservesColimitsOfShape J (prodLeft a) :=
  (prodLeftAdj a).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- The binary product of sets preserves all limits: it is right adjoint to the diagonal. -/
theorem preservesLimitsOfShape_prodFunctor : PreservesLimitsOfShape J prodFunctor.{u} := by
  constructor
  intro K
  constructor
  intro c hc
  have h0 := (Types.isLimit_iff _).mp
    ⟨isLimitOfPreserves (Pi.eval (fun _ : Fin 2 => Type u) 0) hc⟩
  have h1 := (Types.isLimit_iff _).mp
    ⟨isLimitOfPreserves (Pi.eval (fun _ : Fin 2 => Type u) 1) hc⟩
  rw [Types.isLimit_iff]
  rintro s hs
  obtain ⟨x0, hx0, hu0⟩ := h0 (fun j => (s j).1) (fun f => (Prod.ext_iff.mp (hs f)).1)
  obtain ⟨x1, hx1, hu1⟩ := h1 (fun j => (s j).2) (fun f => (Prod.ext_iff.mp (hs f)).2)
  refine ⟨(x0, x1), fun j => Prod.ext (hx0 j) (hx1 j), ?_⟩
  rintro ⟨y0, y1⟩ hy
  rw [hu0 y0 (fun j => (Prod.ext_iff.mp (hy j)).1), hu1 y1 (fun j => (Prod.ext_iff.mp (hy j)).2)]

/-- Along a morphism of the shape, the `isSome`-ness of a section of `K ⋙ (−) + 1` is
preserved; on a connected shape it is therefore constant. -/
lemma option_isSome_constant [IsPreconnected J] (K : J ⥤ Type u)
    {s : ∀ j, (K ⋙ optionFunctor).obj j}
    (hs : ∀ {j j' : J} (f : j ⟶ j'), (K ⋙ optionFunctor).map f (s j) = s j') (j k : J) :
    (s j).isSome = (s k).isSome := by
  refine constant_of_preserves_morphisms (fun j => (s j).isSome) ?_ j k
  intro a b f
  exact Option.isSome_map.symm.trans congr(Option.isSome $(hs f))

/-- **The maybe functor preserves connected limits.** -/
theorem preservesLimitsOfShape_option [IsConnected J] :
    PreservesLimitsOfShape J optionFunctor.{u} := by
  classical
  constructor
  intro K
  constructor
  intro c hc
  -- A compatible family is either `none` everywhere, or, the shape being connected, `some` of a
  -- compatible family of `K` everywhere; in each case it has a unique lift.
  rw [Types.isLimit_iff]
  rintro s hs
  by_cases hall : ∀ j, s j = none
  · refine ⟨none, fun j => (hall j).symm, ?_⟩
    intro y hy
    cases y with
    | none => rfl
    | some a =>
        have := hy (Classical.arbitrary J)
        rw [hall (Classical.arbitrary J)] at this
        cases this
  · push Not at hall
    obtain ⟨j₀, hj₀⟩ := hall
    have hsome : ∀ j, (s j).isSome := by
      intro j
      have h := option_isSome_constant K (s := s) (fun {a b} f => hs f) j₀ j
      rw [← h]
      cases hx : s j₀ with
      | none => exact absurd hx hj₀
      | some x => simp
    set t : ∀ j, K.obj j := fun j => (s j).get (hsome j) with ht_def
    have ht : ∀ j, s j = some (t j) := fun j => (Option.some_get (hsome j)).symm
    have hts : t ∈ K.sections := by
      intro j j' f
      have h := hs f
      rw [ht j, ht j'] at h
      simp only [Functor.comp_map, optionFunctor_map] at h
      exact Option.some.inj h
    obtain ⟨x, hx, hxu⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ t hts
    refine ⟨some x, fun j => by rw [ht j, ← hx j]; rfl, ?_⟩
    intro y hy
    cases y with
    | none =>
        have := hy j₀
        rw [ht j₀] at this
        cases this
    | some a =>
        have hax : a = x := by
          refine hxu a (fun j => ?_)
          have h := hy j
          rw [ht j] at h
          exact Option.some.inj h
        rw [hax]

/-- **The maybe functor preserves connected colimits.** -/
theorem preservesColimitsOfShape_option [IsConnected J] :
    PreservesColimitsOfShape J optionFunctor.{u} := by
  classical
  constructor
  intro K
  constructor
  intro c hc
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  rw [((K ⋙ optionFunctor).isColimit_coconeTypes).iff_bijective
    ((K ⋙ optionFunctor).descColimitType _) (fun _ _ => rfl)]
  -- The comparison map is injective (the `none`s are identified by connectedness, the `some`s by
  -- the colimit of `K`) and surjective.
  have hcT : (K.coconeTypesEquiv.symm c).IsColimit :=
    (Types.isColimit_iff_coconeTypesIsColimit c).mp ⟨hc⟩
  have hf : ∀ (j : J) (a : (K ⋙ optionFunctor).obj j),
      (K ⋙ optionFunctor).descColimitType
        ((K ⋙ optionFunctor).coconeTypesEquiv.symm (optionFunctor.mapCocone c))
          ((K ⋙ optionFunctor).ιColimitType j a) = Option.map (c.ι.app j) a := fun _ _ => rfl
  let sc : K.CoconeTypes :=
    { pt := (K ⋙ optionFunctor).ColimitType
      ι := fun j x => (K ⋙ optionFunctor).ιColimitType j (some x)
      ι_naturality := by
        intro j j' g
        funext x
        exact Functor.ιColimitType_map (F := K ⋙ optionFunctor) g (some x) }
  have hnone : ∀ j k : J, (K ⋙ optionFunctor).ιColimitType j (none : Option (K.obj j))
      = (K ⋙ optionFunctor).ιColimitType k none := by
    intro j k
    refine constant_of_preserves_morphisms
      (fun j => (K ⋙ optionFunctor).ιColimitType j (none : Option (K.obj j))) ?_ j k
    intro a b g
    exact (Functor.ιColimitType_map (F := K ⋙ optionFunctor) g (none : Option (K.obj a))).symm
  constructor
  · intro z₁ z₂ hz
    obtain ⟨j, a, rfl⟩ := (K ⋙ optionFunctor).ιColimitType_jointly_surjective z₁
    obtain ⟨k, b, rfl⟩ := (K ⋙ optionFunctor).ιColimitType_jointly_surjective z₂
    rw [hf, hf] at hz
    cases a with
    | none =>
        cases b with
        | none => exact hnone j k
        | some y => cases hz
    | some x =>
        cases b with
        | none => cases hz
        | some y =>
            simp only [Option.map_some] at hz
            have h1 : K.ιColimitType j x = K.ιColimitType k y :=
              hcT.bijective.1 (Option.some.inj hz)
            exact congr(K.descColimitType sc $h1)
  · intro y
    cases y with
    | none => exact ⟨(K ⋙ optionFunctor).ιColimitType (Classical.arbitrary J) none, rfl⟩
    | some y =>
        obtain ⟨j, x, rfl⟩ := hcT.ι_jointly_surjective y
        exact ⟨(K ⋙ optionFunctor).ιColimitType j (some x), rfl⟩

/-! ## Componentwise descriptions -/

end UlmerBialgebras
