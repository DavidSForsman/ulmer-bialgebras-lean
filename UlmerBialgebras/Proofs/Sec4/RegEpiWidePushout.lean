module

public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import UlmerBialgebras.Kan.Sifted
public import UlmerBialgebras.Kan.SiftedPi

/-!
# Wide pushouts of regular epimorphisms

The primal engine for componentwise preservation; the regular-mono forms apply these
results in opposite categories (`OpTranslateWide.lean`). The argument uses only existing
colimits. Reflexive coequalizers give codiagonal presentations, which allow descent in the second
variable after descent in the first.

## Main results

* `UlmerBialgebras.RegEpiWide.preservesColimit_prod_of_componentwise`: a functor `F : A × B ⥤ D`
  preserving wide pushouts of the given classes of epimorphisms in each variable, the second
  class having codiagonal presentations, preserves wide pushouts of componentwise such legs.
* `UlmerBialgebras.RegEpiWide.RegularEpisAreCodiagonalCoequalizers`: the property that every regular
  epimorphism has a codiagonal coequalizer presentation by a pair of regular epimorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.18
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace UlmerBialgebras.RegEpiWide

open CategoryTheory Limits

variable {K : Type w} [Nontrivial K]

section Defs

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]

/-- The class of regular epimorphisms of `X`, as a morphism property. -/
def regEpi (X : Type u₁) [Category.{v₁} X] : MorphismProperty X :=
  fun _ _ f => IsRegularEpi f

/-- A wide span `Dg` (a wide pushout diagram) has all its legs `Dg(none) ⟶ Dg(some k)` in `M`. -/
def IsWideSpanIn (M : MorphismProperty X) (Dg : WidePushoutShape K ⥤ X) : Prop :=
  ∀ k, M (Dg.map (WidePushoutShape.Hom.init k))

/-- `G` preserves the wide pushouts, indexed by `K`, of wide spans with legs in `M`. -/
def PreservesWidePushoutsIn (K : Type w) (M : MorphismProperty X) (G : X ⥤ Y) : Prop :=
  ∀ Dg : WidePushoutShape K ⥤ X, IsWideSpanIn M Dg → PreservesColimit Dg G

/-- A coequalizer presentation whose two legs also force equality of any
compatible pair of maps out of their common codomain. -/
structure IsCodiagonalCoequalizer {a c q : X} (m : c ⟶ a) (f g : q ⟶ c) : Prop where
  condition : f ≫ m = g ≫ m
  codiag : ∀ ⦃T : X⦄ (t t' : c ⟶ T), f ≫ t = g ≫ t' → t = t'
  factor : ∀ ⦃T : X⦄ (t : c ⟶ T), f ≫ t = g ≫ t → ∃ u : a ⟶ T, m ≫ u = t

/-- Every regular epimorphism `m` of `X` has a codiagonal coequalizer presentation by a pair of
regular epimorphisms `f, g`. -/
def RegularEpisAreCodiagonalCoequalizers (X : Type u₁) [Category.{v₁} X] : Prop :=
  ∀ ⦃a c : X⦄ (m : c ⟶ a), IsRegularEpi m →
    ∃ (q : X) (f g : q ⟶ c), IsRegularEpi f ∧ IsRegularEpi g ∧
      IsCodiagonalCoequalizer m f g

/-- The coequalizer of a reflexive pair `f, g` is a codiagonal coequalizer presentation. -/
lemma isCodiagonalCoequalizer_of_reflexive {a c q : X} {m : c ⟶ a} {f g : q ⟶ c}
    [IsReflexivePair f g] {w : f ≫ m = g ≫ m} (hl : IsColimit (Cofork.ofπ m w)) :
    IsCodiagonalCoequalizer m f g where
  condition := w
  codiag T t t' h := by
    obtain ⟨r, hrf, hrg⟩ := IsReflexivePair.common_section f g
    calc
      t = r ≫ f ≫ t := by rw [← Category.assoc, hrf, Category.id_comp]
      _ = r ≫ g ≫ t' := by rw [h]
      _ = t' := by rw [← Category.assoc, hrg, Category.id_comp]
  factor T t h := ⟨(Cofork.IsColimit.desc' hl t h).1, (Cofork.IsColimit.desc' hl t h).2⟩

end Defs

section Wide

variable {Y : Type u₂} [Category.{v₂} Y]

omit [Nontrivial K] in
/-- For a colimiting wide pushout cocone `s`, a compatible family `z, (w k)` factors through the
apex `s.pt`. -/
lemma exists_desc_wide {Dg : WidePushoutShape K ⥤ Y} {s : Cocone Dg} (hs : IsColimit s)
    {T : Y} (z : Dg.obj none ⟶ T) (w : ∀ k, Dg.obj (some k) ⟶ T)
    (hw : ∀ k, Dg.map (WidePushoutShape.Hom.init k) ≫ w k = z) :
    ∃ v : s.pt ⟶ T, s.ι.app none ≫ v = z ∧ ∀ k, s.ι.app (some k) ≫ v = w k :=
  ⟨hs.desc (WidePushoutShape.mkCocone z w hw), hs.fac _ none, fun k => hs.fac _ (some k)⟩

omit [Nontrivial K] in
/-- If all legs of a wide span are epimorphisms, the colimit injection of `Dg(none)` is an
epimorphism. -/
lemma epi_apex {Dg : WidePushoutShape K ⥤ Y} {s : Cocone Dg} (hs : IsColimit s)
    (hm : ∀ k, Epi (Dg.map (WidePushoutShape.Hom.init k))) : Epi (s.ι.app none) := by
  constructor
  intro T u v h
  refine hs.hom_ext (fun j => ?_)
  cases j with
  | none => exact h
  | some k =>
    rw [← cancel_epi (Dg.map (WidePushoutShape.Hom.init k)), ← Category.assoc,
      ← Category.assoc, s.w, h]

/-- A cocone `s` over a wide span with epimorphic legs, with `s.ι none` epi, is colimiting as soon
as every compatible family factors through `s.ι none`. -/
noncomputable def isColimitOfWideCriterion {Dg : WidePushoutShape K ⥤ Y} (s : Cocone Dg)
    (hepi : Epi (s.ι.app none)) (hm : ∀ k, Epi (Dg.map (WidePushoutShape.Hom.init k)))
    (hex : ∀ (T : Y) (z : Dg.obj none ⟶ T) (w : ∀ k, Dg.obj (some k) ⟶ T),
      (∀ k, Dg.map (WidePushoutShape.Hom.init k) ≫ w k = z) →
        ∃ v : s.pt ⟶ T, s.ι.app none ≫ v = z) : IsColimit s where
  desc t := (hex t.pt (t.ι.app none) (fun k => t.ι.app (some k))
    (fun k => t.w (WidePushoutShape.Hom.init k))).choose
  fac t j := by
    have hv := (hex t.pt (t.ι.app none) (fun k => t.ι.app (some k))
      (fun k => t.w (WidePushoutShape.Hom.init k))).choose_spec
    cases j with
    | none => exact hv
    | some k =>
      rw [← cancel_epi (Dg.map (WidePushoutShape.Hom.init k)), ← Category.assoc, s.w, hv,
        t.w]
  uniq t m hm' := by
    have hv := (hex t.pt (t.ι.app none) (fun k => t.ι.app (some k))
      (fun k => t.w (WidePushoutShape.Hom.init k))).choose_spec
    rw [← cancel_epi (s.ι.app none), hv, hm' none]

end Wide

section OneVariable

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]

/-- If `G` preserves wide pushouts (with at least two legs) of spans with legs in `M`, then `G`
sends epimorphisms in `M` to epimorphisms (via the wide cokernel pair of `g`). -/
lemma epi_map_of_preservesWide {M : MorphismProperty X}
    {G : X ⥤ Y} (hG : PreservesWidePushoutsIn K M G) {b c : X} (g : c ⟶ b) (hg : M g)
    [Epi g] : Epi (G.map g) := by
  obtain ⟨k₁, k₂, hk⟩ := exists_pair_ne K
  classical
  let Dg := WidePushoutShape.wideSpan c (fun _ : K => b) (fun _ => g)
  let s : Cocone Dg := WidePushoutShape.mkCocone (X := b) g (fun _ => 𝟙 b) (fun _ => by
    simp [Dg])
  have hs : IsColimit s := isColimitOfWideCriterion s
    (by simpa [s] using (inferInstance : Epi g))
    (fun _ => by simpa [Dg] using (inferInstance : Epi g))
    (fun T z w hw => ⟨w k₁, by simpa [s, Dg] using hw k₁⟩)
  have := hG Dg (fun _ => by simpa [Dg] using hg)
  have hs' : IsColimit (G.mapCocone s) := (PreservesColimit.preserves hs).some
  constructor
  intro T u v huv
  obtain ⟨l, -, hl⟩ := exists_desc_wide hs' (G.map g ≫ u)
    (fun k => if k = k₁ then u else v) (fun k => by
      by_cases h : k = k₁
      · simp [h, Dg]
      · simp [h, Dg, huv])
  have h1 := hl k₁
  have h2 := hl k₂
  simp only [Functor.comp_obj, Functor.mapCocone_pt, WidePushoutShape.mkCocone_pt,
      Functor.const_obj_obj, Functor.mapCocone_ι_app, WidePushoutShape.mkCocone_ι_app, ↓reduceIte,
      Ne.symm hk, s] at h1 h2
  rw [← h1, h2]

/-- If `G` preserves wide pushouts of spans with legs in `M` and `m` has a codiagonal presentation
by `f, g ∈ M`, then every `z` with `G f ≫ z = G g ≫ z` factors through `G m`. -/
lemma exists_factor_of_codiagonalCoequalizer {M : MorphismProperty X}
    {G : X ⥤ Y} (hG : PreservesWidePushoutsIn K M G) {a c q : X} {m : c ⟶ a}
    {f g : q ⟶ c} (hfg : IsCodiagonalCoequalizer m f g) (hf : M f) (hg : M g)
    [Epi f] [Epi g] [Epi m] {T : Y} (z : G.obj c ⟶ T)
    (hz : G.map f ≫ z = G.map g ≫ z) :
    ∃ u : G.obj a ⟶ T, G.map m ≫ u = z := by
  obtain ⟨k₁, k₂, hk⟩ := exists_pair_ne K
  classical
  let Dg := WidePushoutShape.wideSpan q (fun _ : K => c)
    (fun k => if k = k₁ then f else g)
  let s : Cocone Dg := WidePushoutShape.mkCocone (X := a) (f ≫ m) (fun _ => m)
    (fun k => by
      by_cases h : k = k₁
      · simp [Dg, h]
      · simp [Dg, h, hfg.condition])
  have hleg : ∀ k, Epi (Dg.map (WidePushoutShape.Hom.init k)) := fun k => by
    by_cases h : k = k₁
    · simpa [Dg, h] using (inferInstance : Epi f)
    · simpa [Dg, h] using (inferInstance : Epi g)
  have hs : IsColimit s := isColimitOfWideCriterion s
    (by simpa [s] using (inferInstance : Epi (f ≫ m))) hleg
    (fun T z' w hw => by
      have h1 : f ≫ w k₁ = z' := by simpa [Dg] using hw k₁
      have h2 : g ≫ w k₂ = z' := by simpa [Dg, Ne.symm hk] using hw k₂
      have e : w k₁ = w k₂ := hfg.codiag _ _ (h1.trans h2.symm)
      obtain ⟨u, hu⟩ := hfg.factor (w k₁) (by rw [h1, e, h2])
      exact ⟨u, by simp [s, ← h1, ← hu]⟩)
  have := hG Dg (fun k => by
    by_cases h : k = k₁
    · simpa [Dg, h] using hf
    · simpa [Dg, h] using hg)
  have hs' : IsColimit (G.mapCocone s) := (PreservesColimit.preserves hs).some
  obtain ⟨l, -, hl⟩ := exists_desc_wide hs' (G.map f ≫ z) (fun _ => z) (fun k => by
    by_cases h : k = k₁
    · simp [Dg, h]
    · simp [Dg, h, hz])
  exact ⟨l, by simpa [s] using hl k₁⟩

/-- Such preservation also preserves every regular epi with a codiagonal presentation. -/
lemma regularEpi_map_of_preservesWide (hC : RegularEpisAreCodiagonalCoequalizers X)
    {G : X ⥤ Y} (hG : PreservesWidePushoutsIn K (regEpi X) G)
    {a c : X} (m : c ⟶ a) (hm : IsRegularEpi m) : IsRegularEpi (G.map m) := by
  obtain ⟨q, f, g, hf, hg, hfg⟩ := hC m hm
  have := hf
  have := hg
  have := hm
  have : Epi (G.map m) := epi_map_of_preservesWide hG m hm
  have hw : G.map f ≫ G.map m = G.map g ≫ G.map m := by
    rw [← G.map_comp, ← G.map_comp, hfg.condition]
  refine ⟨⟨{ W := G.obj q
             left := G.map f
             right := G.map g
             w := hw
             isColimit := Cofork.IsColimit.mk _ (fun s => ?_) (fun s => ?_)
               (fun s l hl => ?_) }⟩⟩
  · exact (exists_factor_of_codiagonalCoequalizer hG hfg hf hg s.π s.condition).choose
  · exact (exists_factor_of_codiagonalCoequalizer hG hfg hf hg s.π s.condition).choose_spec
  · apply (cancel_epi (G.map m)).1
    exact hl.trans
      (exists_factor_of_codiagonalCoequalizer hG hfg hf hg s.π s.condition).choose_spec.symm

end OneVariable

section Engine

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {D : Type u₃} [Category.{v₃} D]

open CategoryTheory.Prod in
/-- Factoring a morphism `v₁ : F.obj (a₀, b₀) ⟶ T` through `F.map (𝟙 a₀ ×ₘ m)` when `m` has a
codiagonal coequalizer presentation in `B` and `F.map (π₁ ×ₘ 𝟙 _)` is epi. -/
private lemma exists_factor_prod_right {F : A × B ⥤ D} {MB : MorphismProperty B}
    (hMB : ∀ ⦃b b' : B⦄ (f : b ⟶ b'), MB f → Epi f)
    (hB : ∀ a : A, PreservesWidePushoutsIn K MB (Prod.sectR a B ⋙ F))
    (hcore : ∀ ⦃b c : B⦄ (m : c ⟶ b), MB m →
      ∃ (q : B) (f g : q ⟶ c), MB f ∧ MB g ∧ IsCodiagonalCoequalizer m f g)
    {a₀ a₁ a₂ : A} {b₀ b₁ : B} {T : D} (π₁ : a₀ ⟶ a₁) (m₀ : a₀ ⟶ a₂) (m₁ : b₀ ⟶ b₁)
    (hm₁ : MB m₁) (hEπA : ∀ b : B, Epi (F.map (π₁ ×ₘ 𝟙 b)))
    (v₁ : F.obj (a₁, b₀) ⟶ T) (z : F.obj (a₀, b₀) ⟶ T) (w : F.obj (a₂, b₁) ⟶ T)
    (hv₁ : F.map (π₁ ×ₘ 𝟙 b₀) ≫ v₁ = z)
    (hw : F.map (m₀ ×ₘ m₁) ≫ w = z) :
    ∃ u : F.obj (a₁, b₁) ⟶ T, F.map (𝟙 a₁ ×ₘ m₁) ≫ u = v₁ := by
  obtain ⟨q, f, g, hf, hg, hfg⟩ := hcore m₁ hm₁
  have := hMB f hf
  have := hMB g hg
  have := hMB _ hm₁
  have key' : F.map (𝟙 a₁ ×ₘ f) ≫ v₁ = F.map (𝟙 a₁ ×ₘ g) ≫ v₁ := by
    have := hEπA q
    apply (cancel_epi (F.map (π₁ ×ₘ 𝟙 q))).1
    have e : ∀ h : q ⟶ b₀, (π₁ ×ₘ 𝟙 q) ≫ (𝟙 a₁ ×ₘ h) = (𝟙 a₀ ×ₘ h) ≫ (π₁ ×ₘ 𝟙 b₀) := by
      intro h; ext <;> simp
    simp only [← Category.assoc, ← F.map_comp]
    rw [e f, e g, F.map_comp, F.map_comp, Category.assoc, Category.assoc, hv₁,
      ← hw, ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp]
    congr 2
    ext
    · simp
    · simp [hfg.condition]
  exact exists_factor_of_codiagonalCoequalizer (hB a₁) hfg hf hg v₁ key'

open CategoryTheory.Prod in
/-- Binary preservation for classes of epis with codiagonal presentations in the second factor. -/
theorem preservesColimit_prod_of_componentwise (F : A × B ⥤ D)
    (MA : MorphismProperty A) (MB : MorphismProperty B)
    (hMA : ∀ ⦃a a' : A⦄ (f : a ⟶ a'), MA f → Epi f)
    (hMB : ∀ ⦃b b' : B⦄ (f : b ⟶ b'), MB f → Epi f)
    (hA : ∀ b : B, PreservesWidePushoutsIn K MA (Prod.sectL A b ⋙ F))
    (hB : ∀ a : A, PreservesWidePushoutsIn K MB (Prod.sectR a B ⋙ F))
    (hcore : ∀ ⦃b c : B⦄ (m : c ⟶ b), MB m →
      ∃ (q : B) (f g : q ⟶ c), MB f ∧ MB g ∧ IsCodiagonalCoequalizer m f g)
    (Dg : WidePushoutShape K ⥤ A × B)
    (hDg : ∀ k, MA (Dg.map (WidePushoutShape.Hom.init k)).1 ∧
      MB (Dg.map (WidePushoutShape.Hom.init k)).2) :
    PreservesColimit Dg F := by
  have L1A : ∀ (b : B) ⦃a a' : A⦄ (f : a ⟶ a'), MA f → Epi (F.map (f ×ₘ 𝟙 b)) := fun b _ _ f hf =>
    by have := hMA f hf; exact epi_map_of_preservesWide (hA b) f hf
  have L1B : ∀ (a : A) ⦃b b' : B⦄ (f : b ⟶ b'), MB f → Epi (F.map (𝟙 a ×ₘ f)) := fun a _ _ f hf =>
    by have := hMB f hf; exact epi_map_of_preservesWide (hB a) f hf
  constructor; intro c hc
  set m := fun k => Dg.map (WidePushoutShape.Hom.init k); set π := c.ι.app none
  have colA : ∀ b : B,
      IsColimit ((Prod.sectL A b ⋙ F).mapCocone ((CategoryTheory.Prod.fst A B).mapCocone c)) :=
    fun b => by
      haveI := hA b (Dg ⋙ CategoryTheory.Prod.fst A B) (fun k => (hDg k).1)
      exact (PreservesColimit.preserves (isColimitFst hc)).some
  have colB : ∀ a : A,
      IsColimit ((Prod.sectR a B ⋙ F).mapCocone ((CategoryTheory.Prod.snd A B).mapCocone c)) :=
    fun a => by
      haveI := hB a (Dg ⋙ CategoryTheory.Prod.snd A B) (fun k => (hDg k).2)
      exact (PreservesColimit.preserves (isColimitSnd hc)).some
  have EπA : ∀ b : B, Epi (F.map (π.1 ×ₘ 𝟙 b)) := fun b =>
    epi_apex (colA b) (fun k => L1A b _ (hDg k).1)
  have hπ_split : π = (π.1 ×ₘ 𝟙 (Dg.obj none).2) ≫ (𝟙 c.pt.1 ×ₘ π.2) := by ext <;> simp
  have hm_split : ∀ k, m k = ((m k).1 ×ₘ 𝟙 _) ≫ (𝟙 (Dg.obj (some k)).1 ×ₘ (m k).2) :=
    fun k => by ext <;> simp
  refine ⟨isColimitOfWideCriterion _ ?_ ?_ ?_⟩
  · change Epi (F.map π); rw [hπ_split, F.map_comp]
    have := EπA (Dg.obj none).2
    have : Epi (F.map (𝟙 c.pt.1 ×ₘ π.2)) := epi_apex (colB c.pt.1) (fun k => L1B c.pt.1 _ (hDg k).2)
    exact epi_comp _ _
  · intro k; change Epi (F.map (m k)); rw [hm_split k, F.map_comp]
    have := L1A (Dg.obj none).2 _ (hDg k).1; have := L1B (Dg.obj (some k)).1 _ (hDg k).2
    infer_instance
  · intro T z w hw
    obtain ⟨v₁, hv₁, -⟩ : ∃ v₁ : F.obj (c.pt.1, (Dg.obj none).2) ⟶ T, _ ∧ _ :=
      exists_desc_wide (colA (Dg.obj none).2) z (fun k => F.map (𝟙 _ ×ₘ (m k).2) ≫ w k)
        (fun k => by
          simp only [Functor.comp_obj, Functor.comp_map, Prod.sectL_map]
          exact (Category.assoc _ _ _).symm.trans ((eq_whisker ((F.map_comp _ _).symm.trans
            (congrArg F.map (hm_split k).symm)) _).trans (hw k)))
    have step2 : ∀ k, ∃ u : F.obj (c.pt.1, (Dg.obj (some k)).2) ⟶ T,
        F.map (𝟙 c.pt.1 ×ₘ (m k).2) ≫ u = v₁ := fun k =>
      exists_factor_prod_right hMB hB hcore π.1 (m k).1 (m k).2 (hDg k).2 EπA v₁ z (w k)
        hv₁ (hw k)
    choose u hu using step2
    obtain ⟨v, hv, -⟩ := exists_desc_wide (colB c.pt.1) v₁ u hu
    refine ⟨v, ?_⟩
    change F.map π ≫ v = z; rw [hπ_split, F.map_comp]
    exact (Category.assoc _ _ _).trans ((whisker_eq _ hv).trans hv₁)

end Engine

end UlmerBialgebras.RegEpiWide
