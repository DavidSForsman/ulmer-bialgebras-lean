module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Foundations.CategoryTheory.Limits.CoalgebraColimits

/-!
# The transfinite chain of an endofunctor and its initial algebra

Let `S : C ⥤ C` be an endofunctor.  A *coalgebra chain* of `S` indexed by a well-ordered
type `J` (`UlmerBialgebras.CoalgChain S J`) consists of a functor `W : J ⥤ C` together with
coalgebra structures `str j : W j ⟶ S (W j)`, natural in `j`, such that

* `W (j+1) ≅ S (W j)`, the transition `W j ⟶ W (j+1)` being `str j`;
* the coalgebra structure of `W (j+1)` is `S (str j)`;
* `W` is continuous at limit stages.

This is the classical *initial chain* `X₀ ⟶ S X₀ ⟶ S² X₀ ⟶ ⋯` of `S`, started at an
arbitrary coalgebra `X₀ ⟶ S X₀`.

The main theorem `UlmerBialgebras.CoalgChain.isInitialAlgebra` states that if `C` has colimits of
shape `J`, if `S` preserves them, and if the initial stage `W ⊥` has the expected
universal property (`hbase` below, which holds for instance when `W ⊥` is an initial
object of `C`), then the colimit `A` of the chain carries a structure of `S`-algebra which
is an **initial object** of the category of `S`-algebras.

The argument avoids any transfinite recursion: for an `S`-algebra `(Z, b)`, one shows by
transfinite *induction* that for every `j` there is a unique morphism `k : W j ⟶ Z`
satisfying `k = str j ≫ S k ≫ b` (`UlmerBialgebras.CoalgChain.Cond`); these assemble into the
unique algebra morphism `A ⟶ Z`.

This is the initial-algebra chain used in the proof of Theorem 5.5 (1).

## Main results

* `UlmerBialgebras.CoalgChain`: coalgebra chains of an endofunctor `S` indexed by `J`.
* `UlmerBialgebras.CoalgChain.algebra`: the `S`-algebra structure on the colimit of a coalgebra
  chain.
* `UlmerBialgebras.CoalgChain.isInitialAlgebra`: under the hypotheses above (colimits of shape `J`
  preserved by `S`, and the base condition `hbase`), this algebra is initial.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits Endofunctor

variable {C : Type u} [Category.{v} C]

/-- A transfinite chain of coalgebras of an endofunctor `S`, indexed by a well-ordered
type `J`: the initial chain `X₀ ⟶ S X₀ ⟶ S² X₀ ⟶ ⋯` of `S`. -/
structure CoalgChain (S : C ⥤ C) (J : Type w) [LinearOrder J] [SuccOrder J] where
  /-- The underlying chain. -/
  W : J ⥤ C
  /-- The coalgebra structures, natural in `j`. -/
  str : W ⟶ W ⋙ S
  /-- The stage `j+1` is `S` of the stage `j`. -/
  succIso (j : J) : W.obj (Order.succ j) ≅ S.obj (W.obj j)
  /-- The transition `W j ⟶ W (j+1)` is the coalgebra structure of `W j`. -/
  map_succ (j : J) : W.map (homOfLE (Order.le_succ j)) ≫ (succIso j).hom = str.app j
  /-- The coalgebra structure of the stage `j+1` is `S` of the coalgebra structure at `j`. -/
  str_succ (j : J) : (succIso j).hom ≫ S.map (str.app j)
      = str.app (Order.succ j) ≫ S.map (succIso j).hom
  /-- Continuity at limit stages. -/
  continuous : W.IsWellOrderContinuous

namespace CoalgChain

attribute [instance] CoalgChain.continuous

variable {S : C ⥤ C} {J : Type w} [LinearOrder J] [SuccOrder J] (ch : CoalgChain S J)

/-- The transition morphism of the chain. -/
abbrev t {i j : J} (h : i ≤ j) : ch.W.obj i ⟶ ch.W.obj j := ch.W.map (homOfLE h)

/-- Transition morphisms compose: `t hij ≫ t hjk = t (hij.trans hjk)`. -/
@[reassoc]
lemma t_trans {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) :
    ch.t hij ≫ ch.t hjk = ch.t (hij.trans hjk) := by
  rw [← ch.W.map_comp, homOfLE_comp]

/-- The transition morphism along `i ≤ i` is the identity. -/
@[simp]
lemma t_refl (i : J) : ch.t (le_refl i) = 𝟙 _ := ch.W.map_id i

/-- Naturality of the coalgebra structures: `t hij ≫ str j = str i ≫ S.map (t hij)`. -/
@[reassoc]
lemma t_str {i j : J} (hij : i ≤ j) :
    ch.t hij ≫ ch.str.app j = ch.str.app i ≫ S.map (ch.t hij) :=
  ch.str.naturality (homOfLE hij)

/-- The transition to the successor stage, in terms of the coalgebra structure. -/
@[reassoc]
lemma t_succ_eq (j : J) :
    ch.t (Order.le_succ j) = ch.str.app j ≫ (ch.succIso j).inv := by
  rw [← ch.map_succ j, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The coalgebra structure at a successor stage. -/
lemma str_succ_eq (j : J) :
    ch.str.app (Order.succ j)
      = (ch.succIso j).hom ≫ S.map (ch.str.app j) ≫ S.map (ch.succIso j).inv := by
  rw [← Category.assoc, ch.str_succ j, Category.assoc, ← S.map_comp, Iso.hom_inv_id,
    S.map_id]
  simp

/-- Applying `S` to a transition morphism gives, up to the identifications
`W (j+1) ≅ S (W j)`, the transition morphism between the successor stages. -/
lemma succIso_map_t {i j : J} (hij : i ≤ j) :
    (ch.succIso i).hom ≫ S.map (ch.t hij) ≫ (ch.succIso j).inv
      = ch.t (Order.succ_le_succ hij) := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · simp
  · have hsucc : Order.succ i ≤ j := Order.succ_le_of_lt hlt
    have h1 : ch.t (Order.succ_le_succ hij)
        = ch.t hsucc ≫ ch.str.app j ≫ (ch.succIso j).inv := by
      rw [← ch.t_succ_eq j, ch.t_trans]
    have h2 : ch.t hsucc ≫ ch.str.app j ≫ (ch.succIso j).inv
        = (ch.succIso i).hom ≫ S.map (ch.t hij) ≫ (ch.succIso j).inv := by
      rw [← Category.assoc, ch.t_str hsucc, ch.str_succ_eq i]
      simp only [Category.assoc, ← S.map_comp]
      rw [← ch.t_succ_eq_assoc i, ch.t_trans]
    rw [h1, h2]

section Cond

variable (Z : Endofunctor.Algebra S)

/-- The defining condition of the (unique) morphism from the stage `j` of the chain to an
algebra `Z`. -/
def Cond (j : J) (k : ch.W.obj j ⟶ Z.a) : Prop := k = ch.str.app j ≫ S.map k ≫ Z.str

variable {ch Z}

/-- If `k` satisfies `Cond` at stage `j`, then `t hij ≫ k` satisfies `Cond` at stage `i ≤ j`. -/
lemma cond_restrict {i j : J} (hij : i ≤ j) {k : ch.W.obj j ⟶ Z.a} (hk : ch.Cond Z j k) :
    ch.Cond Z i (ch.t hij ≫ k) := by
  dsimp [Cond]
  conv_lhs => rw [hk]
  simp only [S.map_comp, Category.assoc]
  rw [ch.t_str_assoc hij]

/-- `Cond` at a successor stage `j+1`, rewritten via `succIso j` and the transition
`j ⟶ j+1`. -/
lemma cond_succ_iff (j : J) (k : ch.W.obj (Order.succ j) ⟶ Z.a) :
    ch.Cond Z (Order.succ j) k ↔
      k = (ch.succIso j).hom ≫ S.map (ch.t (Order.le_succ j) ≫ k) ≫ Z.str := by
  rw [Cond, ch.str_succ_eq j, ch.t_succ_eq j]
  simp only [S.map_comp, Category.assoc]

variable [OrderBot J]

/-- Transport of the base condition along an isomorphism of coalgebras. -/
lemma existsUnique_cond_bot_of_iso {V₀ : Endofunctor.Coalgebra S} (e : ch.W.obj (⊥ : J) ≅ V₀.V)
    (he : ch.str.app ⊥ ≫ S.map e.hom = e.hom ≫ V₀.str)
    (h : ∃! k : V₀.V ⟶ Z.a, k = V₀.str ≫ S.map k ≫ Z.str) :
    ∃! k : ch.W.obj (⊥ : J) ⟶ Z.a, ch.Cond Z ⊥ k := by
  obtain ⟨k₀, hk₀, huniq⟩ := h
  have hstr : ch.str.app ⊥ = e.hom ≫ V₀.str ≫ S.map e.inv := by
    rw [← Category.assoc, ← he, Category.assoc, ← S.map_comp, Iso.hom_inv_id, S.map_id]
    simp
  have key : ∀ k₁ : V₀.V ⟶ Z.a,
      ch.Cond Z ⊥ (e.hom ≫ k₁) ↔ (k₁ = V₀.str ≫ S.map k₁ ≫ Z.str) := by
    intro k₁
    have hrhs : ch.str.app ⊥ ≫ S.map (e.hom ≫ k₁) ≫ Z.str
        = e.hom ≫ (V₀.str ≫ S.map k₁ ≫ Z.str) := by
      rw [hstr, S.map_comp]
      simp only [Category.assoc]
      rw [← S.map_comp_assoc, Iso.inv_hom_id, S.map_id, Category.id_comp]
    constructor
    · intro hcond
      have h' : e.hom ≫ k₁ = e.hom ≫ (V₀.str ≫ S.map k₁ ≫ Z.str) := by
        rw [← hrhs]; exact hcond
      exact (cancel_epi e.hom).1 h'
    · intro h'
      rw [Cond, hrhs, ← h']
  refine ⟨e.hom ≫ k₀, (key k₀).2 hk₀, ?_⟩
  intro k hk
  have hk' : ch.Cond Z ⊥ (e.hom ≫ (e.inv ≫ k)) := by rwa [Iso.hom_inv_id_assoc]
  rw [← huniq _ ((key _).1 hk'), Iso.hom_inv_id_assoc]

variable (ch Z) [WellFoundedLT J]

/-- For every stage `j`, there is a unique morphism `W j ⟶ Z` satisfying `Cond`. -/
lemma existsUnique_cond (hbase : ∃! k : ch.W.obj (⊥ : J) ⟶ Z.a, ch.Cond Z ⊥ k) (j : J) :
    ∃! k : ch.W.obj j ⟶ Z.a, ch.Cond Z j k := by
  -- Transfinite induction on `j`. At `j + 1` the condition determines `k` from its restriction
  -- to `j` (`cond_succ_iff`); at a limit, the unique morphisms at the earlier stages are
  -- compatible (`cond_restrict`) and glue along the colimit `W j`.
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      obtain rfl : j = ⊥ := hj.eq_bot
      exact hbase
  | succ j hj IH =>
      obtain ⟨kj, hkj, huniq⟩ := IH
      have hres : ch.t (Order.le_succ j) ≫ (ch.succIso j).hom ≫ S.map kj ≫ Z.str = kj := by
        rw [← Category.assoc, ch.map_succ j]
        exact hkj.symm
      refine ⟨(ch.succIso j).hom ≫ S.map kj ≫ Z.str, ?_, ?_⟩
      · beta_reduce
        rw [cond_succ_iff, hres]
      · intro k hk
        have hk' : ch.Cond Z (Order.succ j) k := hk
        have hres' : ch.t (Order.le_succ j) ≫ k = kj := huniq _ (cond_restrict _ hk')
        rw [(cond_succ_iff j k).1 hk', hres']
  | isSuccLimit j hj IH =>
      classical
      have hcolim := ch.W.isColimitOfIsWellOrderContinuous j hj
      set k : ∀ (i : J), i < j → (ch.W.obj i ⟶ Z.a) := fun i hi => (IH i hi).choose with hk_def
      have hkc : ∀ (i : J) (hi : i < j), ch.Cond Z i (k i hi) := fun i hi => (IH i hi).choose_spec.1
      have hku : ∀ (i : J) (hi : i < j) (m : ch.W.obj i ⟶ Z.a), ch.Cond Z i m → m = k i hi :=
        fun i hi m hm => (IH i hi).choose_spec.2 m hm
      have hcompat : ∀ (i i' : J) (hi : i < j) (hi' : i' < j) (hii' : i ≤ i'),
          ch.t hii' ≫ k i' hi' = k i hi := fun i i' hi hi' hii' =>
        hku i hi _ (cond_restrict hii' (hkc i' hi'))
      let cocone : Cocone ((Set.principalSegIio j).monotone.functor ⋙ ch.W) :=
        { pt := Z.a
          ι :=
            { app := fun i => k i.1 i.2
              naturality := by
                rintro ⟨i, hi⟩ ⟨i', hi'⟩ f
                dsimp
                rw [Category.comp_id]
                exact hcompat i i' hi hi' (leOfHom f) } }
      refine ⟨hcolim.desc cocone, ?_, ?_⟩
      · beta_reduce
        dsimp only [Cond]
        refine hcolim.hom_ext fun i => ?_
        have hfac : ch.t i.2.le ≫ hcolim.desc cocone = k i.1 i.2 := hcolim.fac cocone i
        change ch.t i.2.le ≫ hcolim.desc cocone
            = ch.t i.2.le ≫ ch.str.app j ≫ S.map (hcolim.desc cocone) ≫ Z.str
        rw [hfac, ch.t_str_assoc i.2.le, ← S.map_comp_assoc, hfac]
        exact hkc i.1 i.2
      · intro m hm
        have hm' : ch.Cond Z j m := hm
        refine hcolim.hom_ext fun i => ?_
        rw [hcolim.fac]
        exact hku i.1 i.2 _ (cond_restrict i.2.le hm')

end Cond

section ToAlg

variable [OrderBot J] [WellFoundedLT J]
  (hbase : ∀ Z : Endofunctor.Algebra S, ∃! k : ch.W.obj (⊥ : J) ⟶ Z.a, ch.Cond Z ⊥ k)

/-- The canonical morphism from the stage `j` of the chain to an algebra `Z`. -/
noncomputable def toAlg (Z : Endofunctor.Algebra S) (j : J) : ch.W.obj j ⟶ Z.a :=
  (ch.existsUnique_cond Z (hbase Z) j).choose

/-- `toAlg hbase Z j` satisfies `Cond` at stage `j`. -/
lemma cond_toAlg (Z : Endofunctor.Algebra S) (j : J) : ch.Cond Z j (ch.toAlg hbase Z j) :=
  (ch.existsUnique_cond Z (hbase Z) j).choose_spec.1

/-- Any `m : W j ⟶ Z.a` satisfying `Cond` at stage `j` equals `toAlg hbase Z j`. -/
lemma toAlg_uniq (Z : Endofunctor.Algebra S) (j : J) (m : ch.W.obj j ⟶ Z.a)
    (hm : ch.Cond Z j m) : m = ch.toAlg hbase Z j :=
  (ch.existsUnique_cond Z (hbase Z) j).choose_spec.2 m hm

/-- The morphisms `toAlg` are compatible with the transitions: `t hij ≫ toAlg j = toAlg i`. -/
@[reassoc]
lemma t_toAlg (Z : Endofunctor.Algebra S) {i j : J} (hij : i ≤ j) :
    ch.t hij ≫ ch.toAlg hbase Z j = ch.toAlg hbase Z i :=
  ch.toAlg_uniq hbase Z i _ (cond_restrict hij (ch.cond_toAlg hbase Z j))

/-- At a successor stage, `toAlg (j+1) = (succIso j).hom ≫ S.map (toAlg j) ≫ Z.str`. -/
lemma toAlg_succ (Z : Endofunctor.Algebra S) (j : J) :
    ch.toAlg hbase Z (Order.succ j)
      = (ch.succIso j).hom ≫ S.map (ch.toAlg hbase Z j) ≫ Z.str := by
  have h := (cond_succ_iff (ch := ch) (Z := Z) j (ch.toAlg hbase Z (Order.succ j))).1
    (ch.cond_toAlg hbase Z (Order.succ j))
  rw [ch.t_toAlg hbase Z (Order.le_succ j)] at h
  exact h

end ToAlg

section Colimit

variable [HasColimitsOfShape J C]

/-- The colimit of the chain. -/
noncomputable def pt : C := colimit ch.W

/-- The colimit injections of the chain. -/
noncomputable def ι (j : J) : ch.W.obj j ⟶ ch.pt := colimit.ι ch.W j

/-- The colimit injections are compatible with the transitions: `t hij ≫ ι j = ι i`. -/
@[reassoc (attr := simp)]
lemma t_ι {i j : J} (hij : i ≤ j) : ch.t hij ≫ ch.ι j = ch.ι i :=
  colimit.w ch.W (homOfLE hij)

/-- Morphisms out of the colimit of the chain are determined by the colimit injections. -/
lemma hom_ext {Y : C} {f g : ch.pt ⟶ Y} (h : ∀ j, ch.ι j ≫ f = ch.ι j ≫ g) : f = g :=
  colimit.hom_ext h

/-- The coalgebra structure on the colimit of the chain. -/
noncomputable def strPt : ch.pt ⟶ S.obj ch.pt :=
  colimit.desc ch.W
    { pt := S.obj ch.pt
      ι :=
        { app := fun j => ch.str.app j ≫ S.map (ch.ι j)
          naturality := by
            intro i j f
            dsimp
            rw [show ch.W.map f = ch.t (leOfHom f) from rfl, Category.assoc,
              ch.t_str_assoc (leOfHom f), ← S.map_comp, t_ι, Category.comp_id] } }

/-- The coalgebra structure on the colimit restricts along `ι j` to `str j ≫ S.map (ι j)`. -/
@[reassoc (attr := simp)]
lemma ι_strPt (j : J) : ch.ι j ≫ ch.strPt = ch.str.app j ≫ S.map (ch.ι j) :=
  colimit.ι_desc _ _

variable [PreservesColimitsOfShape J S]

/-- The cocone, with vertex the colimit of the chain, over the diagram `W ⋙ S`. -/
@[simps]
noncomputable def algCocone : Cocone (ch.W ⋙ S) where
  pt := ch.pt
  ι :=
    { app := fun j => (ch.succIso j).inv ≫ ch.ι (Order.succ j)
      naturality := by
        intro i j f
        have hij : i ≤ j := leOfHom f
        have key : (ch.succIso i).hom ≫ S.map (ch.t hij) ≫ (ch.succIso j).inv ≫
            ch.ι (Order.succ j) = ch.ι (Order.succ i) := by
          rw [← Category.assoc (S.map (ch.t hij)), ← Category.assoc, ch.succIso_map_t hij, t_ι]
        dsimp
        rw [← cancel_epi (ch.succIso i).hom, Category.comp_id, Iso.hom_inv_id_assoc]
        exact key }

/-- The algebra structure on the colimit of the chain. -/
noncomputable def algStr : S.obj ch.pt ⟶ ch.pt :=
  (isColimitOfPreserves S (colimit.isColimit ch.W)).desc ch.algCocone

/-- The algebra structure on the colimit restricts along `S.map (ι j)` to
`(succIso j).inv ≫ ι (j+1)`. -/
@[reassoc (attr := simp)]
lemma map_ι_algStr (j : J) :
    S.map (ch.ι j) ≫ ch.algStr = (ch.succIso j).inv ≫ ch.ι (Order.succ j) :=
  (isColimitOfPreserves S (colimit.isColimit ch.W)).fac ch.algCocone j

/-- Morphisms out of `S.obj ch.pt` are determined by their composites with the `S.map (ι j)`. -/
lemma map_hom_ext {Y : C} {f g : S.obj ch.pt ⟶ Y} (h : ∀ j, S.map (ch.ι j) ≫ f = S.map (ch.ι j) ≫ g)
    :
    f = g :=
  (isColimitOfPreserves S (colimit.isColimit ch.W)).hom_ext h

/-- The coalgebra structure on the colimit is a section of the algebra structure:
`strPt ≫ algStr = 𝟙`. -/
@[reassoc (attr := simp)]
lemma strPt_algStr : ch.strPt ≫ ch.algStr = 𝟙 ch.pt := by
  refine ch.hom_ext fun j => ?_
  rw [← Category.assoc, ι_strPt, Category.assoc, map_ι_algStr, ← Category.assoc,
    ← ch.t_succ_eq j, t_ι, Category.comp_id]

/-- The `S`-algebra structure on the colimit of the chain. -/
@[implicit_reducible]
noncomputable def algebra : Endofunctor.Algebra S where
  a := ch.pt
  str := ch.algStr

section Initial

variable [OrderBot J] [WellFoundedLT J]
  (hbase : ∀ Z : Endofunctor.Algebra S, ∃! k : ch.W.obj (⊥ : J) ⟶ Z.a, ch.Cond Z ⊥ k)

/-- The underlying morphism of the unique algebra morphism from the colimit of the chain. -/
noncomputable def descAlg (Z : Endofunctor.Algebra S) : ch.pt ⟶ Z.a :=
  colimit.desc ch.W
    { pt := Z.a
      ι :=
        { app := fun j => ch.toAlg hbase Z j
          naturality := by
            intro i j f
            dsimp
            rw [Category.comp_id]
            exact ch.t_toAlg hbase Z (leOfHom f) } }

omit [PreservesColimitsOfShape J S] in
/-- `descAlg hbase Z` restricts along `ι j` to `toAlg hbase Z j`. -/
@[reassoc (attr := simp)]
lemma ι_descAlg (Z : Endofunctor.Algebra S) (j : J) :
    ch.ι j ≫ ch.descAlg hbase Z = ch.toAlg hbase Z j :=
  colimit.ι_desc _ _

/-- The unique algebra morphism from the colimit of the chain to an arbitrary algebra. -/
noncomputable def homAlg (Z : Endofunctor.Algebra S) : ch.algebra ⟶ Z where
  f := ch.descAlg hbase Z
  h := by
    refine ch.map_hom_ext fun j => ?_
    have hl : S.map (ch.ι j) ≫ S.map (ch.descAlg hbase Z) ≫ Z.str
        = S.map (ch.toAlg hbase Z j) ≫ Z.str := by
      rw [← S.map_comp_assoc, ι_descAlg]
    have hr : S.map (ch.ι j) ≫ ch.algStr ≫ ch.descAlg hbase Z
        = S.map (ch.toAlg hbase Z j) ≫ Z.str := by
      rw [map_ι_algStr_assoc, ι_descAlg, toAlg_succ, Iso.inv_hom_id_assoc]
    exact hl.trans hr.symm

/-- The underlying morphism of `homAlg hbase Z` is `descAlg hbase Z`. -/
@[simp]
lemma homAlg_f (Z : Endofunctor.Algebra S) : (ch.homAlg hbase Z).f = ch.descAlg hbase Z := rfl

/-- Every algebra morphism `ch.algebra ⟶ Z` equals `homAlg hbase Z`. -/
lemma homAlg_uniq (Z : Endofunctor.Algebra S) (m : ch.algebra ⟶ Z) : m = ch.homAlg hbase Z := by
  ext
  rw [homAlg_f]
  refine ch.hom_ext fun j => ?_
  rw [ι_descAlg]
  refine ch.toAlg_uniq hbase Z j _ ?_
  have hm : S.map m.f ≫ Z.str = ch.algStr ≫ m.f := m.h
  rw [Cond]
  refine Eq.symm ?_
  calc ch.str.app j ≫ S.map (ch.ι j ≫ m.f) ≫ Z.str
      = (ch.str.app j ≫ S.map (ch.ι j)) ≫ S.map m.f ≫ Z.str := by
        simp only [S.map_comp, Category.assoc]
    _ = (ch.ι j ≫ ch.strPt) ≫ ch.algStr ≫ m.f := by rw [hm, ι_strPt]
    _ = ch.ι j ≫ m.f := by
        rw [Category.assoc, ← Category.assoc ch.strPt, strPt_algStr, Category.id_comp]

/-- **The initial algebra of an endofunctor as the colimit of its initial chain.**  If the
chain `ch` converges (i.e. `S` preserves its colimit) and its initial stage has the
expected universal property, then the colimit of the chain is an initial `S`-algebra. -/
noncomputable def isInitialAlgebra : IsInitial ch.algebra :=
  IsInitial.ofUniqueHom (fun Z => ch.homAlg hbase Z) (fun Z m => ch.homAlg_uniq hbase Z m)

end Initial

end Colimit

end CoalgChain

end UlmerBialgebras
