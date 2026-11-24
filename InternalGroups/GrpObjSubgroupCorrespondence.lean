module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import InternalGroups.SubMonQuotGalois
public import Foundations.CategoryTheory.Exact.SemiAbelian

/-!
# Newman's correspondence for group objects

Let `C` be a cartesian monoidal category with pullbacks and reflexive coequalizers of modules,
and let `G` be a group object of `C`.  This file studies the Galois connection

  `Sub(G) ⇆ Quot(G)`

of `InternalGroups/SubMonQuotGalois.lean` in the case of a *group* object, where `Sub(G)` is
the collection of **subgroup objects** of `G` and `Quot(G)` the collection of quotient `G`-modules,
and shows that a subgroup object is recovered from its coset quotient as soon as its coset
relation is effective.

The classical case `C = Set` is the elementary correspondence between subgroups `N ≤ G` and
quotient `G`-sets of `G` (coset spaces `G/N`); for `C` the category of cocommutative comonoids of
a symmetric monoidal abelian category, `Grp C` is the category of cocommutative Hopf monoids and
this is **Newman's correspondence** between sub-Hopf-monoids of `H` and quotient `H`-module
comonoids of `H`.

The results of this file were announced by the author and will appear in a forthcoming
preprint.

## Main definitions

* `InternalGroups.act`: the action of a generalized element of a monoid object on a generalized
  element of a module, and its calculus (`act_one`, `act_mul`, ...);
* `InternalGroups.SubGrp`: subgroup objects of a group object;
* `InternalGroups.stab`: the *stabiliser* of the base point of a quotient module, as a subgroup
  object;
* `InternalGroups.cosetMul`: the right translation `G ⊗ N ⟶ G`, `(x, n) ↦ x · n`, which together
  with the first projection is the coset relation of a subgroup object;
* `InternalGroups.SubGrp.quot`: the coset quotient `G ⟶ G / N`.

## Main results

* `InternalGroups.galoisConnection_quot_stab`: the Galois connection between subgroup objects and
  quotient modules;
* `InternalGroups.le_stab_quot`: a subgroup object is contained in the stabiliser of its coset
  quotient;
* `InternalGroups.stab_quot_le`: the stabiliser of the coset quotient of a subgroup object `N` is
  `N` again provided the coset relation of `N` is effective;
* `InternalGroups.isColimitCoforkQuot`: the coset quotient is also the coequalizer, in `C`, of
  the coset relation when the forgetful functor of `G`-modules preserves reflexive
  coequalizers.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## The action on generalized elements -/

section Act

variable {G : C} [MonObj G] {V : C} [ModObj G V]

/-- The action of a generalized element `x : T ⟶ G` of a monoid object on a generalized element
`v : T ⟶ V` of a module. -/
noncomputable def act {T : C} (x : T ⟶ G) (v : T ⟶ V) : T ⟶ V := lift x v ≫ γ[G, V]

/-- Unit law of the action: `η[G] ▷ V ≫ γ[G, V] = (λ_ V).hom`. -/
lemma one_whiskerRight_comp_smul : (η[G] ▷ V ≫ γ[G, V] : 𝟙_ C ⊗ V ⟶ V) = (λ_ V).hom := by
  have := ModObj.one_smul (M := G) V
  simpa only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso] using this

/-- Associativity of the action: `μ[G] ▷ V ≫ γ = (α_ G G V).hom ≫ G ◁ γ ≫ γ`. -/
lemma mul_whiskerRight_comp_smul :
    (μ[G] ▷ V ≫ γ[G, V] : (G ⊗ G) ⊗ V ⟶ V) = (α_ G G V).hom ≫ G ◁ γ[G, V] ≫ γ[G, V] := by
  have := ModObj.mul_smul (M := G) V
  simpa only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
    selfLeftAction_actionAssocIso] using this

/-- The unit acts trivially: `1 · v = v`. -/
@[simp]
lemma act_one {T : C} (v : T ⟶ V) : act (1 : T ⟶ G) v = v := by
  rw [act, Hom.one_def, ← lift_whiskerRight, Category.assoc, one_whiskerRight_comp_smul]
  exact lift_leftUnitor_hom (toUnit T) v

/-- The action is associative: `(x y) · v = x · (y · v)`. -/
lemma act_mul {T : C} (x y : T ⟶ G) (v : T ⟶ V) : act (x * y) v = act x (act y v) := by
  rw [act, act, act, show x * y = lift x y ≫ μ[G] from rfl, ← lift_whiskerRight,
    Category.assoc, mul_whiskerRight_comp_smul, ← Category.assoc, lift_lift_associator_hom,
    lift_whiskerLeft_assoc]

end Act

/-! ## Subgroup objects -/

variable {G : C} [GrpObj G]

/-- A **subgroup object** of a group object `G`: a group object `N` together with a monomorphism
`N ⟶ G` which is a morphism of monoid objects. -/
structure SubGrp (G : C) [GrpObj G] where
  /-- the underlying object -/
  N : C
  [grpObj : GrpObj N]
  /-- the inclusion -/
  i : N ⟶ G
  [mono_i : Mono i]
  [isMonHom_i : IsMonHom i]

attribute [instance] SubGrp.grpObj SubGrp.mono_i SubGrp.isMonHom_i

/-- The submonoid object underlying a subgroup object. -/
def SubGrp.toSubMon (s : SubGrp G) : SubMon G := { N := ⟨s.N⟩, i := s.i }

/-- The inclusion of the underlying submonoid object is that of the subgroup object. -/
@[simp] lemma SubGrp.toSubMon_i (s : SubGrp G) : s.toSubMon.i = s.i := rfl

/-- Subgroup objects are preordered by factorisation of the inclusions. -/
instance : Preorder (SubGrp G) := Preorder.lift SubGrp.toSubMon

/-- A submonoid object of a group object which is closed under inversion is a subgroup
object. -/
@[instance_reducible]
def grpObjOfMono {K : C} [MonObj K] (i : K ⟶ G) [Mono i] [IsMonHom i] (inv : K ⟶ K)
    (hinv : inv ≫ i = (i)⁻¹) : GrpObj K where
  inv := inv
  left_inv := by
    rw [← cancel_mono i]
    have h1 : (lift inv (𝟙 K) ≫ μ) ≫ i = (inv ≫ i) * (𝟙 K ≫ i) := by
      rw [show lift inv (𝟙 K) ≫ μ = inv * 𝟙 K from rfl, MonObj.mul_comp]
    have h2 : (toUnit K ≫ η[K]) ≫ i = (1 : K ⟶ G) := by
      rw [← Hom.one_def, MonObj.one_comp]
    rw [h1, hinv, Category.id_comp, inv_mul_cancel, h2]
  right_inv := by
    rw [← cancel_mono i]
    have h1 : (lift (𝟙 K) inv ≫ μ) ≫ i = (𝟙 K ≫ i) * (inv ≫ i) := by
      rw [show lift (𝟙 K) inv ≫ μ = 𝟙 K * inv from rfl, MonObj.mul_comp]
    have h2 : (toUnit K ≫ η[K]) ≫ i = (1 : K ⟶ G) := by
      rw [← Hom.one_def, MonObj.one_comp]
    rw [h1, hinv, Category.id_comp, mul_inv_cancel, h2]

/-! ## The stabiliser of the base point of a quotient module -/

section Stabiliser

open QuotMod

/-- The morphism to the terminal object `𝟙_ C` is `toUnit T`. -/
lemma isTerminalTensorUnit_from (T : C) :
    (isTerminalTensorUnit (C := C)).from T = toUnit T :=
  isTerminalTensorUnit.hom_ext _ _

/-- The base point of a quotient module, as a generalized element. -/
noncomputable def pt (q : QuotMod G) (T : C) : T ⟶ q.V.X := toUnit T ≫ basePoint q

/-- The base point is natural in the stage: `f ≫ pt q T = pt q T'`. -/
@[reassoc]
lemma comp_pt {T T' : C} (f : T' ⟶ T) (q : QuotMod G) : f ≫ pt q T = pt q T' := by
  rw [pt, pt, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

/-- **The quotient map is the orbit map of the base point**: `p (g) = g · p (1)`. -/
lemma comp_p_eq_act (q : QuotMod G) {T : C} (g : T ⟶ G) :
    g ≫ q.p.hom = act g (pt q T) := by
  have h := QuotMod.mul_comp_p q
  calc g ≫ q.p.hom = (g * 1) ≫ q.p.hom := by rw [MulOneClass.mul_one]
    _ = lift g (1 : T ⟶ G) ≫ μ[G] ≫ q.p.hom := by rw [← Category.assoc]; rfl
    _ = lift g ((1 : T ⟶ G) ≫ q.p.hom) ≫ γ[G, q.V.X] := by
        rw [h, ← Category.assoc]
        simp only [lift_whiskerLeft]
    _ = act g (pt q T) := by
        rw [act, pt, Hom.one_def, Category.assoc, basePoint]

/-- A generalized element `g : T ⟶ G` **kills** the quotient module `q` if the quotient map
sends it to the base point.  In `Set`: `g` lies in the stabiliser of the base point. -/
def Kills (q : QuotMod G) {T : C} (g : T ⟶ G) : Prop := g ≫ q.p.hom = pt q T

/-- `g` kills `q` iff `g` fixes the base point: `g · pt = pt`. -/
lemma kills_iff_act (q : QuotMod G) {T : C} (g : T ⟶ G) :
    Kills q g ↔ act g (pt q T) = pt q T := by rw [Kills, comp_p_eq_act]

/-- The unit kills every quotient module. -/
lemma Kills.one (q : QuotMod G) (T : C) : Kills q (1 : T ⟶ G) := by
  rw [kills_iff_act, act_one]

/-- If `g` kills `q`, so does `g⁻¹`. -/
lemma Kills.inv {q : QuotMod G} {T : C} {g : T ⟶ G} (hg : Kills q g) : Kills q g⁻¹ := by
  rw [kills_iff_act] at *
  conv_lhs => rw [← hg]
  rw [← act_mul, inv_mul_cancel, act_one]

/-- If `g` kills `q`, so does its restriction `f ≫ g` to any earlier stage. -/
lemma Kills.comp {q : QuotMod G} {T T' : C} {g : T ⟶ G} (hg : Kills q g) (f : T' ⟶ T) :
    Kills q (f ≫ g) := by
  rw [Kills, Category.assoc, hg, comp_pt]

variable [HasPullbacks C]

/-- The stabiliser of the base point is exactly the collection of generalized elements which
factor through `InternalGroups.QuotMod.subIncl`. -/
lemma kills_iff_factors (q : QuotMod G) {T : C} (g : T ⟶ G) :
    Kills q g ↔ ∃ h : T ⟶ subObj q, h ≫ subIncl q = g := by
  constructor
  · intro hg
    exact ⟨pullback.lift g (toUnit T) hg, pullback.lift_fst _ _ _⟩
  · rintro ⟨h, rfl⟩
    have h2 := subIncl_comp_p (isTerminalTensorUnit (C := C)) q
    rw [isTerminalTensorUnit_from] at h2
    rw [Kills, Category.assoc, h2, ← Category.assoc, toUnit_unique (h ≫ toUnit _) (toUnit T)]
    rfl

/-- The inclusion `subIncl q` kills `q`. -/
lemma kills_subIncl (q : QuotMod G) : Kills q (subIncl q) :=
  (kills_iff_factors q _).2 ⟨𝟙 _, Category.id_comp _⟩

/-- The inverse morphism of the stabiliser of the base point. -/
noncomputable def stabInv (q : QuotMod G) : subObj q ⟶ subObj q :=
  ((kills_iff_factors q _).1 (kills_subIncl q).inv).choose

/-- `stabInv q ≫ subIncl q = (subIncl q)⁻¹`. -/
@[reassoc (attr := simp)]
lemma stabInv_comp (q : QuotMod G) : stabInv q ≫ subIncl q = (subIncl q)⁻¹ :=
  ((kills_iff_factors q _).1 (kills_subIncl q).inv).choose_spec

/-- The monoid structure of the stabiliser of the base point, as in `InternalGroups.QuotMod.sub`. -/
@[instance_reducible]
noncomputable def stabMonObj (q : QuotMod G) : MonObj (subObj q) :=
  letI := mono_subIncl (isTerminalTensorUnit (C := C)) q
  monObjOfMono (subIncl q) (subOne q) (subMul isTerminalTensorUnit q) (subOne_comp q)
    (subMul_comp isTerminalTensorUnit q)

/-- With the monoid structure `stabMonObj q`, `subIncl q` is a morphism of monoid objects. -/
lemma isMonHom_subIncl (q : QuotMod G) :
    letI := mono_subIncl (isTerminalTensorUnit (C := C)) q
    letI := stabMonObj q
    IsMonHom (subIncl q) :=
  letI := mono_subIncl (isTerminalTensorUnit (C := C)) q
  isMonHom_monObjOfMono (subIncl q) (subOne q) (subMul isTerminalTensorUnit q)
    (subOne_comp q) (subMul_comp isTerminalTensorUnit q)

/-- **The stabiliser of the base point of a quotient module is a subgroup object.** -/
noncomputable def stab (q : QuotMod G) : SubGrp G :=
  letI := mono_subIncl (isTerminalTensorUnit (C := C)) q
  letI := stabMonObj q
  letI := isMonHom_subIncl q
  letI : GrpObj (subObj q) := grpObjOfMono (subIncl q) (stabInv q) (stabInv_comp q)
  { N := subObj q
    i := subIncl q }

/-- The inclusion of the stabiliser `stab q` is `subIncl q`. -/
@[simp]
lemma stab_i (q : QuotMod G) : (stab q).i = subIncl q := rfl

end Stabiliser

/-! ## The coset relation of a subgroup object -/

section CosetRel

open QuotMod

/-- The right translation map `G ⊗ N ⟶ G`, `(x, n) ↦ x · n`.  Together with the first projection
it forms the **coset relation** of the subgroup object `N ≤ G`, whose quotient is the coset
object `G / N`. -/
noncomputable def cosetMul (s : SubGrp G) : G ⊗ s.N ⟶ G := fst G s.N * (snd G s.N ≫ s.i)

/-- On generalized elements: `f ≫ cosetMul s = (f ≫ fst) * ((f ≫ snd) ≫ s.i)`. -/
@[reassoc]
lemma comp_cosetMul {T : C} (s : SubGrp G) (f : T ⟶ G ⊗ s.N) :
    f ≫ cosetMul s = (f ≫ fst G s.N) * ((f ≫ snd G s.N) ≫ s.i) := by
  rw [cosetMul, MonObj.comp_mul, Category.assoc]

/-- The coset relation is the pair of adjoint transposes used in
`InternalGroups/SubMonQuotGalois.lean`. -/
lemma mulTranspose_hom_eq (s : SubGrp G) :
    (SubMon.mulTranspose s.toSubMon).hom = cosetMul s := by
  have h : (G ◁ s.i : G ⊗ s.N ⟶ G ⊗ G) = lift (fst G s.N) (snd G s.N ≫ s.i) := by
    apply hom_ext <;> simp
  rw [SubMon.mulTranspose_hom]
  exact h =≫ μ[G]

/-- The underlying morphism of `SubMon.oneTranspose` of `s` is the first projection `G ⊗ N ⟶ G`. -/
lemma oneTranspose_hom_eq (s : SubGrp G) :
    (SubMon.oneTranspose isTerminalTensorUnit s.toSubMon).hom = fst G s.N := by
  have h : (G ◁ (toUnit s.N ≫ η[G]) : G ⊗ s.N ⟶ G ⊗ G)
      = lift (fst G s.N) (snd G s.N ≫ toUnit s.N ≫ η[G]) := by apply hom_ext <;> simp
  rw [SubMon.oneTranspose_hom, isTerminalTensorUnit_from]
  change G ◁ (toUnit s.N ≫ η[G]) ≫ μ[G] = fst G s.N
  rw [h, show lift (fst G s.N) (snd G s.N ≫ toUnit s.N ≫ η[G]) ≫ μ[G]
      = fst G s.N * (snd G s.N ≫ toUnit s.N ≫ η[G]) from rfl,
    ← Category.assoc, toUnit_unique (snd G s.N ≫ toUnit s.N) (toUnit (G ⊗ s.N)),
    ← Hom.one_def, MulOneClass.mul_one]

/-- Multiplying by an element of the stabiliser does not change the quotient map. -/
lemma mul_comp_p_of_kills {q : QuotMod G} {T : C} (x : T ⟶ G) {k : T ⟶ G} (hk : Kills q k) :
    (x * k) ≫ q.p.hom = x ≫ q.p.hom := by
  rw [comp_p_eq_act, comp_p_eq_act, act_mul, (kills_iff_act q k).1 hk]

end CosetRel

/-! ## Newman's correspondence -/

section Correspondence

open QuotMod

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

/-- **The coset quotient of a subgroup object**: the quotient module `G / N`, the coequalizer of
the coset relation. -/
noncomputable def SubGrp.quot (s : SubGrp G) : QuotMod G :=
  SubMon.quot isTerminalTensorUnit s.toSubMon

/-- The defining coequalizer property of the coset quotient, at the level of `C`. -/
lemma cosetMul_comp_quot_p (s : SubGrp G) :
    cosetMul s ≫ (s.quot).p.hom = fst G s.N ≫ (s.quot).p.hom := by
  have h := coequalizer.condition (SubMon.mulTranspose s.toSubMon)
      (SubMon.oneTranspose (isTerminalTensorUnit (C := C)) s.toSubMon)
  have h' := congr(($h).hom)
  rw [CategoryTheory.Mod.comp_hom', CategoryTheory.Mod.comp_hom', mulTranspose_hom_eq,
    oneTranspose_hom_eq] at h'
  exact h'

variable [HasPullbacks C]

/-- **The Galois connection between subgroup objects and quotient modules.** -/
theorem galoisConnection_quot_stab :
    GaloisConnection (fun s : SubGrp G => s.quot) (fun q : QuotMod G => stab q) := by
  intro s q
  exact galoisConnection_quot_sub isTerminalTensorUnit s.toSubMon q

/-- Half of the correspondence, from the Galois connection: a subgroup object is contained in the
stabiliser of the coset quotient it determines. -/
theorem le_stab_quot (s : SubGrp G) : s ≤ stab s.quot :=
  galoisConnection_quot_stab.le_u_l s

/-- **The stabiliser of the coset quotient of a subgroup object `N` is `N` again**, provided the
coset relation of `N` is effective, i.e. is the kernel pair of the coset quotient.  This is the
injectivity of Newman's correspondence. -/
theorem stab_quot_le (s : SubGrp G)
    (heff : IsKernelPair (s.quot).p.hom (cosetMul s) (fst G s.N)) : stab s.quot ≤ s := by
  have h1 : (subIncl (s.quot) : subObj (s.quot) ⟶ G) ≫ (s.quot).p.hom
      = (1 : subObj (s.quot) ⟶ G) ≫ (s.quot).p.hom := by
    rw [kills_subIncl (s.quot), Kills.one (s.quot)]
  obtain ⟨t, ht₁, ht₂⟩ :=
    heff.lift' (subIncl s.quot : subObj (s.quot) ⟶ G) (1 : subObj (s.quot) ⟶ G) h1
  refine ⟨t ≫ snd G s.N, ?_⟩
  have h2 : t ≫ cosetMul s = (t ≫ fst G s.N) * ((t ≫ snd G s.N) ≫ s.i) := comp_cosetMul s t
  rw [ht₁, ht₂, MulOneClass.one_mul] at h2
  exact h2.symm

/-! ### The correspondence as a bijection -/

/-! ### Effectivity of the coset relation -/

section Effectivity

/-- **The coset quotient, computed in `C`.**  If the forgetful functor of `G`-modules preserves
reflexive coequalizers — as it does whenever tensoring preserves them — then the coset quotient
is also the coequalizer, in `C`, of the coset relation. -/
noncomputable def isColimitCoforkQuot (s : SubGrp G)
    (hpres : CategoryTheory.PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) G)) :
    IsColimit (Cofork.ofπ (s.quot).p.hom (cosetMul_comp_quot_p s)) := by
  set u := SubMon.mulTranspose s.toSubMon with hu
  set v := SubMon.oneTranspose (isTerminalTensorUnit (C := C)) s.toSubMon with hv
  haveI := hpres.preserves u v (SubMon.isReflexivePair isTerminalTensorUnit s.toSubMon)
  have h1 := (isColimitMapCoconeCoforkEquiv (CategoryTheory.Mod.forget (D := C) G)
    (coequalizer.condition u v))
      (isColimitOfPreserves (CategoryTheory.Mod.forget (D := C) G)
        (coequalizerIsCoequalizer u v))
  have hue : (CategoryTheory.Mod.forget (D := C) G).map u = cosetMul s := mulTranspose_hom_eq s
  have hve : (CategoryTheory.Mod.forget (D := C) G).map v = fst G s.N := oneTranspose_hom_eq s
  refine Cofork.IsColimit.mk _
    (fun t => h1.desc (Cofork.ofπ (Cofork.π t) (by rw [hue, hve]; exact Cofork.condition t)))
    (fun t => Cofork.IsColimit.π_desc h1) (fun t m hm => Cofork.IsColimit.hom_ext h1 ?_)
  rw [Cofork.IsColimit.π_desc h1]
  exact hm

end Effectivity

end Correspondence


end InternalGroups
