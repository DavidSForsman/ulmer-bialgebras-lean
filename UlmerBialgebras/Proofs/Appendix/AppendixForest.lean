module

public import UlmerBialgebras.Paper.AppendixDefsForest
public import UlmerBialgebras.Proofs.Appendix.AppendixProbes

/-!
# Lemma A.3: the free enriched category on a labelled forest

Generic construction over a monoidal category `W` with an absorbing initial object, in the
library's composition order `Hom(a,b) ⊗ Hom(b,c) → Hom(a,c)`. The hom-object from `a` to `b`
is the label `lab p` of the unique path `p : a → b` if there is one, and the initial object
otherwise. Along paths, composition is the coherence isomorphism `mu` (`comp_homIso`).

The paper's convention is obtained over `Vᴹᵒᵖ` with the reversed labelling `mopLab ℓ`: `labIso`
identifies its labels with `DirectedGraph.pathLabel`, and `unmop_mu` identifies `mu` with the
canonical isomorphism `DirectedGraph.pathLabelCompIso` (`exists_paperVCat_free_of_isForest`).

## Main results

* `UlmerBialgebras.Paper.Appendix.Forest.forestVCat`: the free enriched category on a labelled
  forest, in the library's convention (Lemma A.3).
* `UlmerBialgebras.Paper.Appendix.Forest.emap_path`: the action of a functor on a path is
  determined by its edge maps.
* `UlmerBialgebras.Paper.Appendix.Forest.reconstruct`: a functor out of the free category is
  `functorOf` of its vertices and edge maps.
* `UlmerBialgebras.Paper.Appendix.Forest.exists_paperVCat_free_of_isForest`: Lemma A.3 in the
  paper's convention over `Vᴹᵒᵖ`: a `V`-category on the vertices of the forest, with hom-objects
  identified with the path labels (initial when there is no path), composition and identities given
  by the canonical isomorphisms, and functors out of it in bijection with vertex assignments and
  edge maps.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma A.3
* [H. Wolff, *V-cat and V-graph*][wolffVcatVgraph1974]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix.Forest

open CategoryTheory MonoidalCategory Limits

variable {W : Type v} [Category.{w} W] [MonoidalCategory W]
variable {G : DirectedGraph.{u}} (ℓ : G.Labelling W)

/-- The label of a path, in the library's order: `lab (p.cons e) = lab p ⊗ ℓ e`. -/
def lab {a : G.Vertex} : ∀ {b : G.Vertex}, G.Path a b → W
  | _, .nil => 𝟙_ W
  | _, .cons p e => lab p ⊗ ℓ e

/-- The label of the empty path is the unit `𝟙_ W`. -/
@[simp] lemma lab_nil (a : G.Vertex) : lab ℓ (Quiver.Path.nil : G.Path a a) = 𝟙_ W := rfl

/-- `lab (p.cons e) = lab p ⊗ ℓ e`. -/
@[simp] lemma lab_cons {a b c : G.Vertex} (p : G.Path a b) (e : b ⟶ c) :
    lab ℓ (p.cons e) = lab ℓ p ⊗ ℓ e := rfl

/-- `lab p ⊗ lab q ≅ lab (p ≫ q)`. -/
def mu {a b : G.Vertex} (p : G.Path a b) : ∀ {c : G.Vertex} (q : G.Path b c),
    lab ℓ p ⊗ lab ℓ q ≅ lab ℓ (p.comp q)
  | _, .nil => ρ_ (lab ℓ p)
  | _, .cons q e => (α_ _ _ _).symm ≪≫ whiskerRightIso (mu p q) (ℓ e)

/-- `mu p nil` is the right unitor `ρ_ (lab p)`. -/
lemma mu_nil {a b : G.Vertex} (p : G.Path a b) :
    mu ℓ p (Quiver.Path.nil) = ρ_ (lab ℓ p) := rfl

/-- `mu p (q.cons e)` is `α⁻¹` followed by `mu p q ▷ ℓ e`. -/
@[simp] lemma mu_cons_hom {a b c d : G.Vertex} (p : G.Path a b) (q : G.Path b c)
    (e : c ⟶ d) :
    (mu ℓ p (q.cons e)).hom = (α_ _ _ _).inv ≫ (mu ℓ p q).hom ▷ ℓ e := rfl

/-- The inverse of `mu p (q.cons e)` is `(mu p q)⁻¹ ▷ ℓ e` followed by `α`. -/
@[simp] lemma mu_cons_inv {a b c d : G.Vertex} (p : G.Path a b) (q : G.Path b c)
    (e : c ⟶ d) :
    (mu ℓ p (q.cons e)).inv = (mu ℓ p q).inv ▷ ℓ e ≫ (α_ _ _ _).hom := rfl

/-- Equal paths have equal labels. -/
lemma lab_congr {a b : G.Vertex} {p p' : G.Path a b} (h : p = p') : lab ℓ p = lab ℓ p' :=
  congrArg _ h

/-- Left unit coherence. -/
lemma mu_nil_left : ∀ {a b : G.Vertex} (q : G.Path a b),
    (mu ℓ Quiver.Path.nil q).hom ≫ eqToHom (lab_congr ℓ (Quiver.Path.nil_comp q)) =
      (λ_ (lab ℓ q)).hom
  | _, _, .nil => by simp [mu_nil, unitors_equal]
  | _, _, .cons q e => by
    let m : 𝟙_ W ⊗ lab ℓ q ⟶ lab ℓ (Quiver.Path.nil.comp q) :=
      (mu ℓ Quiver.Path.nil q).hom
    let t : lab ℓ (Quiver.Path.nil.comp q) ⟶ lab ℓ q :=
      eqToHom (lab_congr ℓ (Quiver.Path.nil_comp q))
    let te : lab ℓ (Quiver.Path.nil.comp q) ⊗ ℓ e ⟶ lab ℓ q ⊗ ℓ e :=
      eqToHom (congrArg (fun X => X ⊗ ℓ e) (lab_congr ℓ (Quiver.Path.nil_comp q)))
    have ht : te = t ▷ ℓ e := by rw [eqToHom_whiskerRight]
    have ih : m ≫ t = (λ_ (lab ℓ q)).hom := mu_nil_left q
    change ((α_ (𝟙_ W) (lab ℓ q) (ℓ e)).inv ≫ m ▷ ℓ e) ≫ te =
      (λ_ (lab ℓ q ⊗ ℓ e)).hom
    rw [ht, Category.assoc, ← comp_whiskerRight, ih]
    monoidal

/-- Associativity coherence. -/
lemma mu_assoc {a b c : G.Vertex} (p : G.Path a b) (q : G.Path b c) : ∀ {d : G.Vertex}
    (r : G.Path c d),
    (mu ℓ p q).hom ▷ lab ℓ r ≫ (mu ℓ (p.comp q) r).hom ≫
        eqToHom (lab_congr ℓ (Quiver.Path.comp_assoc p q r)) =
      (α_ _ _ _).hom ≫ lab ℓ p ◁ (mu ℓ q r).hom ≫ (mu ℓ p (q.comp r)).hom
  | _, .nil => by
    simp [mu_nil]
  | _, .cons r e => by
    let mpq : lab ℓ p ⊗ lab ℓ q ⟶ lab ℓ (p.comp q) := (mu ℓ p q).hom
    let mqr : lab ℓ q ⊗ lab ℓ r ⟶ lab ℓ (q.comp r) := (mu ℓ q r).hom
    let ml : lab ℓ (p.comp q) ⊗ lab ℓ r ⟶ lab ℓ ((p.comp q).comp r) :=
      (mu ℓ (p.comp q) r).hom
    let mr : lab ℓ p ⊗ lab ℓ (q.comp r) ⟶ lab ℓ (p.comp (q.comp r)) :=
      (mu ℓ p (q.comp r)).hom
    let t : lab ℓ ((p.comp q).comp r) ⟶ lab ℓ (p.comp (q.comp r)) :=
      eqToHom (lab_congr ℓ (Quiver.Path.comp_assoc p q r))
    let te : lab ℓ ((p.comp q).comp r) ⊗ ℓ e ⟶ lab ℓ (p.comp (q.comp r)) ⊗ ℓ e :=
      eqToHom (congrArg (fun X => X ⊗ ℓ e) (lab_congr ℓ (Quiver.Path.comp_assoc p q r)))
    have ht : te = t ▷ ℓ e := by rw [eqToHom_whiskerRight]
    have ih : mpq ▷ lab ℓ r ≫ ml ≫ t = (α_ _ _ _).hom ≫ lab ℓ p ◁ mqr ≫ mr :=
      mu_assoc p q r
    change mpq ▷ (lab ℓ r ⊗ ℓ e) ≫
        ((α_ (lab ℓ (p.comp q)) (lab ℓ r) (ℓ e)).inv ≫ ml ▷ ℓ e) ≫ te =
      (α_ (lab ℓ p) (lab ℓ q) (lab ℓ r ⊗ ℓ e)).hom ≫
        lab ℓ p ◁ ((α_ (lab ℓ q) (lab ℓ r) (ℓ e)).inv ≫ mqr ▷ ℓ e) ≫
          (α_ (lab ℓ p) (lab ℓ (q.comp r)) (ℓ e)).inv ≫ mr ▷ ℓ e
    rw [ht, Category.assoc, associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight, Category.assoc, ih]
    monoidal

/-! ## The enriched category -/

section Cat

attribute [local instance] Classical.propDecidable

variable (Z : MonoidalInitial W) (hG : G.IsForest)

include hG in
/-- In a forest there is at most one path between two vertices. -/
lemma path_eq {a b : G.Vertex} (p p' : G.Path a b) : p = p' := (hG a b).elim p p'

/-- The hom-object: the label of the path if there is one, initial otherwise. -/
noncomputable def hom (a b : G.Vertex) : W :=
  if h : Nonempty (G.Path a b) then lab ℓ h.some else Z.zero

include hG in
/-- If `p : a → b` is a path, the hom-object `hom a b` is the label `lab p`. -/
lemma hom_eq {a b : G.Vertex} (p : G.Path a b) : hom ℓ Z a b = lab ℓ p := by
  rw [hom, dite_eq_left ⟨p⟩, path_eq hG (Nonempty.some ⟨p⟩) p]

/-- The identification `hom a b ≅ lab p` for a path `p : a → b` (an `eqToIso` of `hom_eq`). -/
noncomputable def homIso {a b : G.Vertex} (p : G.Path a b) : hom ℓ Z a b ≅ lab ℓ p :=
  eqToIso (hom_eq ℓ Z hG p)

/-- If there is no path `a → b`, the hom-object `hom a b` is initial. -/
noncomputable def homInitial {a b : G.Vertex} (h : IsEmpty (G.Path a b)) :
    IsInitial (hom ℓ Z a b) :=
  Z.isInitial.ofIso (eqToIso (by rw [hom, dite_eq_right (not_nonempty_iff.mpr h)]))

/-- For `h : p = p'`, `(homIso p').inv = eqToHom _ ≫ (homIso p).inv`. -/
lemma homIso_congr {a b : G.Vertex} {p p' : G.Path a b} (h : p = p') :
    (homIso ℓ Z hG p').inv = eqToHom (lab_congr ℓ h).symm ≫ (homIso ℓ Z hG p).inv := by
  subst h; simp

/-- `x ⊗ y` is initial when `x` is initial (the initial object is absorbing). -/
def initL {x : W} (hx : IsInitial x) (y : W) : IsInitial (x ⊗ y) :=
  (Z.zeroTensor y).ofIso (whiskerRightIso (hx.uniqueUpToIso Z.isInitial).symm y)

/-- `x ⊗ y` is initial when `y` is initial (the initial object is absorbing). -/
def initR (x : W) {y : W} (hy : IsInitial y) : IsInitial (x ⊗ y) :=
  (Z.tensorZero x).ofIso (whiskerLeftIso x (hy.uniqueUpToIso Z.isInitial).symm)

/-- Composition along given paths. -/
noncomputable def compAt {a b c : G.Vertex} (p : G.Path a b) (q : G.Path b c) :
    hom ℓ Z a b ⊗ hom ℓ Z b c ⟶ hom ℓ Z a c :=
  ((homIso ℓ Z hG p).hom ⊗ₘ (homIso ℓ Z hG q).hom) ≫ (mu ℓ p q).hom ≫
    (homIso ℓ Z hG (p.comp q)).inv

/-- Composition `hom a b ⊗ hom b c → hom a c`: `compAt` along the paths if both exist, and the
map out of an initial tensor otherwise. -/
noncomputable def comp (a b c : G.Vertex) : hom ℓ Z a b ⊗ hom ℓ Z b c ⟶ hom ℓ Z a c :=
  if h₁ : Nonempty (G.Path a b) then
    if h₂ : Nonempty (G.Path b c) then compAt ℓ Z hG h₁.some h₂.some
    else (initR Z _ (homInitial ℓ Z (not_nonempty_iff.mp h₂))).to _
  else (initL Z (homInitial ℓ Z (not_nonempty_iff.mp h₁)) _).to _

/-- For paths `p : a → b` and `q : b → c`, the composition `comp a b c` is `compAt p q`. -/
lemma comp_eq {a b c : G.Vertex} (p : G.Path a b) (q : G.Path b c) :
    comp ℓ Z hG a b c = compAt ℓ Z hG p q := by
  rw [comp, dite_eq_left ⟨p⟩, dite_eq_left ⟨q⟩, path_eq hG (Nonempty.some ⟨p⟩) p,
    path_eq hG (Nonempty.some ⟨q⟩) q]

/-- The identity `𝟙_ W → hom a a`: the label `𝟙_ W` of the empty path. -/
noncomputable def eid (a : G.Vertex) : 𝟙_ W ⟶ hom ℓ Z a a :=
  (homIso ℓ Z hG (Quiver.Path.nil : G.Path a a)).inv

/-- The left unit law of the free enriched category. -/
lemma id_comp' (a b : G.Vertex) :
    (λ_ _).inv ≫ eid ℓ Z hG a ▷ _ ≫ comp ℓ Z hG a a b = 𝟙 (hom ℓ Z a b) := by
  by_cases h : Nonempty (G.Path a b)
  · obtain ⟨p⟩ := h
    rw [comp_eq ℓ Z hG Quiver.Path.nil p, compAt, eid,
      homIso_congr ℓ Z hG (Quiver.Path.nil_comp p).symm, reassoc_of% (mu_nil_left ℓ p)]
    rw [MonoidalCategory.tensorHom_def]
    let E : hom ℓ Z a a ≅ 𝟙_ W := homIso ℓ Z hG Quiver.Path.nil
    let P : hom ℓ Z a b ≅ lab ℓ p := homIso ℓ Z hG p
    change (λ_ (hom ℓ Z a b)).inv ≫ E.inv ▷ hom ℓ Z a b ≫
      (E.hom ▷ hom ℓ Z a b ≫ 𝟙_ W ◁ P.hom) ≫ (λ_ (lab ℓ p)).hom ≫ P.inv = _
    simp only [Category.assoc, inv_hom_whiskerRight_assoc, leftUnitor_naturality_assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (homInitial ℓ Z (not_nonempty_iff.mp h)).hom_ext _ _

/-- The right unit law of the free enriched category. -/
lemma comp_id' (a b : G.Vertex) :
    (ρ_ _).inv ≫ _ ◁ eid ℓ Z hG b ≫ comp ℓ Z hG a b b = 𝟙 (hom ℓ Z a b) := by
  by_cases h : Nonempty (G.Path a b)
  · obtain ⟨p⟩ := h
    rw [comp_eq ℓ Z hG p Quiver.Path.nil, compAt, eid, mu_nil, MonoidalCategory.tensorHom_def']
    let E : hom ℓ Z b b ≅ 𝟙_ W := homIso ℓ Z hG Quiver.Path.nil
    let P : hom ℓ Z a b ≅ lab ℓ p := homIso ℓ Z hG p
    change (ρ_ (hom ℓ Z a b)).inv ≫ hom ℓ Z a b ◁ E.inv ≫
      (hom ℓ Z a b ◁ E.hom ≫ P.hom ▷ 𝟙_ W) ≫ (ρ_ (lab ℓ p)).hom ≫ P.inv = _
    simp only [Category.assoc, whiskerLeft_inv_hom_assoc, rightUnitor_naturality_assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · exact (homInitial ℓ Z (not_nonempty_iff.mp h)).hom_ext _ _

/-- The associativity law along three composable paths, with the hom-objects abstracted
through equalities to the path labels (from `mu_assoc`). -/
lemma assoc_core {a b c d : G.Vertex} (p : G.Path a b) (q : G.Path b c) (r : G.Path c d)
    {X₁₂ X₂₃ X₃₄ X₁₃ X₂₄ X₁₄ : W} (e₁₂ : X₁₂ = lab ℓ p) (e₂₃ : X₂₃ = lab ℓ q)
    (e₃₄ : X₃₄ = lab ℓ r) (e₁₃ : X₁₃ = lab ℓ (p.comp q)) (e₂₄ : X₂₄ = lab ℓ (q.comp r))
    (e₁₄ : X₁₄ = lab ℓ (p.comp (q.comp r))) (e₁₄' : X₁₄ = lab ℓ ((p.comp q).comp r)) :
    (α_ X₁₂ X₂₃ X₃₄).inv ≫
        ((eqToHom e₁₂ ⊗ₘ eqToHom e₂₃) ≫ (mu ℓ p q).hom ≫ eqToHom e₁₃.symm) ▷ X₃₄ ≫
          (eqToHom e₁₃ ⊗ₘ eqToHom e₃₄) ≫ (mu ℓ (p.comp q) r).hom ≫ eqToHom e₁₄'.symm =
      X₁₂ ◁ ((eqToHom e₂₃ ⊗ₘ eqToHom e₃₄) ≫ (mu ℓ q r).hom ≫ eqToHom e₂₄.symm) ≫
        (eqToHom e₁₂ ⊗ₘ eqToHom e₂₄) ≫ (mu ℓ p (q.comp r)).hom ≫ eqToHom e₁₄.symm := by
  subst e₁₂ e₂₃ e₃₄ e₁₃ e₂₄ e₁₄
  have hm := mu_assoc ℓ p q r
  rw [← cancel_epi (α_ _ _ _).hom]
  simp only [eqToHom_refl, MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [hm]

/-- The associativity law of the free enriched category. -/
lemma assoc' (a b c d : G.Vertex) :
    (α_ _ _ _).inv ≫ comp ℓ Z hG a b c ▷ _ ≫ comp ℓ Z hG a c d =
      _ ◁ comp ℓ Z hG b c d ≫ comp ℓ Z hG a b d := by
  by_cases h₁ : Nonempty (G.Path a b)
  · by_cases h₂ : Nonempty (G.Path b c)
    · by_cases h₃ : Nonempty (G.Path c d)
      · obtain ⟨p⟩ := h₁; obtain ⟨q⟩ := h₂; obtain ⟨r⟩ := h₃
        rw [comp_eq ℓ Z hG p q, comp_eq ℓ Z hG (p.comp q) r, comp_eq ℓ Z hG q r,
          comp_eq ℓ Z hG p (q.comp r), compAt, compAt, compAt, compAt]
        simp only [homIso, eqToIso.hom, eqToIso.inv]
        exact assoc_core ℓ p q r _ _ _ _ _ (hom_eq ℓ Z hG _) (hom_eq ℓ Z hG _)
      · exact (initR Z _ (initR Z _ (homInitial ℓ Z (not_nonempty_iff.mp h₃)))).hom_ext _ _
    · exact (initR Z _ (initL Z (homInitial ℓ Z (not_nonempty_iff.mp h₂)) _)).hom_ext _ _
  · exact (initL Z (homInitial ℓ Z (not_nonempty_iff.mp h₁)) _).hom_ext _ _

/-- The objects of the free enriched category: the vertices. -/
def Obj (_ℓ : G.Labelling W) (_Z : MonoidalInitial W) (_hG : G.IsForest) : Type u := G.Vertex

/-- The `W`-category structure on the vertices of a labelled forest: hom-objects `hom`,
identities `eid` and composition `comp`. -/
noncomputable instance enriched : EnrichedCategory W (Obj ℓ Z hG) where
  Hom := hom ℓ Z
  id := eid ℓ Z hG
  comp := comp ℓ Z hG
  id_comp := id_comp' ℓ Z hG
  comp_id := comp_id' ℓ Z hG
  assoc := assoc' ℓ Z hG

/-- The identity of the free enriched category is `eid`. -/
@[simp] lemma eId_obj (a : Obj ℓ Z hG) : eId W a = eid ℓ Z hG a := rfl

/-- The composition of the free enriched category is `comp`. -/
@[simp] lemma eComp_obj (a b c : Obj ℓ Z hG) : eComp W a b c = comp ℓ Z hG a b c := rfl

/-- **Lemma A.3** ([forsman2026syntactic]; library convention): the free enriched category on a
labelled forest. -/
noncomputable def forestVCat : VCat.{w, v, u} W :=
  VCat.of (ForgetEnrichment W (Obj ℓ Z hG))

/-- The inclusion of an edge label. -/
noncomputable def incl {a b : G.Vertex} (e : a ⟶ b) : ℓ e ⟶ hom ℓ Z a b :=
  (λ_ (ℓ e)).inv ≫ (homIso ℓ Z hG ((Quiver.Path.nil : G.Path a a).cons e)).inv

/-- Lemma A.3 before transport: along paths `p : a → b` and `q : b → c`, the composition is the
coherence isomorphism `mu`, read through the identifications `homIso` with the path labels. -/
lemma comp_homIso {a b c : G.Vertex} (p : G.Path a b) (q : G.Path b c) :
    comp ℓ Z hG a b c ≫ (homIso ℓ Z hG (p.comp q)).hom =
      ((homIso ℓ Z hG p).hom ⊗ₘ (homIso ℓ Z hG q).hom) ≫ (mu ℓ p q).hom := by
  rw [comp_eq ℓ Z hG p q, compAt]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The identity of the free category is the identity of `𝟙_ W`, the label of the empty path. -/
lemma eid_homIso (a : G.Vertex) :
    eid ℓ Z hG a ≫ (homIso ℓ Z hG (Quiver.Path.nil : G.Path a a)).hom = 𝟙 _ :=
  Iso.inv_hom_id _

/-- The inclusion of an edge label is `ℓ e ≅ 𝟙_ W ⊗ ℓ e`, the label of the one-edge path. -/
lemma incl_homIso {a b : G.Vertex} (e : a ⟶ b) :
    incl ℓ Z hG e ≫ (homIso ℓ Z hG ((Quiver.Path.nil : G.Path a a).cons e)).hom =
      (λ_ (ℓ e)).inv :=
  (Category.assoc _ _ _).trans
    ((((λ_ (ℓ e)).inv ≫= Iso.inv_hom_id _)).trans (Category.comp_id _))

section Functor

variable {D : Type u} [Category.{w} D] [EnrichedOrdinaryCategory W D] (f : G.Vertex → D)
  (φ : ∀ ⦃a b : G.Vertex⦄ (e : a ⟶ b), ℓ e ⟶ (f a ⟶[W] f b))

/-- The action of a functor out of the free category on path labels. -/
def Phi {a : G.Vertex} : ∀ {b : G.Vertex} (p : G.Path a b), lab ℓ p ⟶ (f a ⟶[W] f b)
  | _, .nil => eId W (f a)
  | _, .cons p e => (Phi p ⊗ₘ φ e) ≫ eComp W _ _ _

/-- `Phi` of the empty path is the identity `eId`. -/
@[simp] lemma phi_nil (a : G.Vertex) : Phi ℓ f φ (Quiver.Path.nil : G.Path a a) = eId W (f a) :=
  rfl

/-- `Phi (p.cons e)` is `Phi p ⊗ φ e` followed by composition. -/
@[simp] lemma phi_cons {a b c : G.Vertex} (p : G.Path a b) (e : b ⟶ c) :
    Phi ℓ f φ (p.cons e) = (Phi ℓ f φ p ⊗ₘ φ e) ≫ eComp W _ _ _ := rfl


/-- `Phi` is compatible with composition: `mu p q ≫ Phi (p.comp q) = (Phi p ⊗ Phi q) ≫ comp`. -/
lemma phi_comp {a b : G.Vertex} (p : G.Path a b) : ∀ {c : G.Vertex} (q : G.Path b c),
    (mu ℓ p q).hom ≫ Phi ℓ f φ (p.comp q) = (Phi ℓ f φ p ⊗ₘ Phi ℓ f φ q) ≫ eComp W _ _ _
  | _, .nil => rightUnitor_comp_eId _
  | _, .cons q e => by
    have ih := phi_comp p q
    change ((α_ _ _ _).inv ≫ (mu ℓ p q).hom ▷ ℓ e) ≫
        (Phi ℓ f φ (p.comp q) ⊗ₘ φ e) ≫ eComp W _ _ _ =
      (Phi ℓ f φ p ⊗ₘ ((Phi ℓ f φ q ⊗ₘ φ e) ≫ eComp W _ _ _)) ≫ eComp W _ _ _
    rw [Category.assoc, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, ih,
      ← Category.comp_id (φ e), ← MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      Category.assoc, ← MonoidalCategory.associator_inv_naturality_assoc,
      MonoidalCategory.tensorHom_id, e_assoc, ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id]

/-- The action on hom-objects of the functor determined by `f` and `φ`. -/
noncomputable def emapOf (a b : G.Vertex) : hom ℓ Z a b ⟶ (f a ⟶[W] f b) :=
  if h : Nonempty (G.Path a b) then (homIso ℓ Z hG h.some).hom ≫ Phi ℓ f φ h.some
  else (homInitial ℓ Z (not_nonempty_iff.mp h)).to _

/-- For a path `p : a → b`, `emapOf a b` is `homIso p` followed by `Phi p`. -/
lemma emapOf_eq {a b : G.Vertex} (p : G.Path a b) :
    emapOf ℓ Z hG f φ a b = (homIso ℓ Z hG p).hom ≫ Phi ℓ f φ p := by
  rw [emapOf, dite_eq_left ⟨p⟩, path_eq hG (Nonempty.some ⟨p⟩) p]

/-- The `V`-functor out of the free category determined by vertices and edge maps. -/
noncomputable def functorOf : VFunctor W (ForgetEnrichment W (Obj ℓ Z hG)) D :=
  VFunctor.ofEnriched (A := Obj ℓ Z hG) f (emapOf ℓ Z hG f φ)
    (fun (a : G.Vertex) => by
      change eid ℓ Z hG a ≫ emapOf ℓ Z hG f φ a a = eId W (f a)
      rw [emapOf_eq ℓ Z hG f φ Quiver.Path.nil, eid]
      dsimp only [lab, Phi]
      exact Iso.inv_hom_id_assoc _ _)
    (fun (a b c : G.Vertex) => by
      change comp ℓ Z hG a b c ≫ emapOf ℓ Z hG f φ a c =
        (emapOf ℓ Z hG f φ a b ⊗ₘ emapOf ℓ Z hG f φ b c) ≫ eComp W _ _ _
      by_cases h₁ : Nonempty (G.Path a b)
      · by_cases h₂ : Nonempty (G.Path b c)
        · obtain ⟨p⟩ := h₁; obtain ⟨q⟩ := h₂
          rw [comp_eq ℓ Z hG p q, compAt, emapOf_eq ℓ Z hG f φ (p.comp q),
            emapOf_eq ℓ Z hG f φ p, emapOf_eq ℓ Z hG f φ q]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          rw [phi_comp, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
        · exact (initR Z _ (homInitial ℓ Z (not_nonempty_iff.mp h₂))).hom_ext _ _
      · exact (initL Z (homInitial ℓ Z (not_nonempty_iff.mp h₁)) _).hom_ext _ _)

/-- On vertices, `functorOf f φ` is `f`. -/
@[simp] lemma functorOf_obj (a : G.Vertex) :
    (functorOf ℓ Z hG f φ).obj (a : ForgetEnrichment W (Obj ℓ Z hG)) = f a := rfl

/-- On hom-objects, `functorOf f φ` is `emapOf f φ`. -/
@[simp] lemma functorOf_emap (a b : G.Vertex) :
    (functorOf ℓ Z hG f φ).emap (a : ForgetEnrichment W (Obj ℓ Z hG))
      (b : ForgetEnrichment W (Obj ℓ Z hG)) = emapOf ℓ Z hG f φ a b := rfl

/-- The functor `functorOf f φ` sends the inclusion of the edge label `ℓ e` to `φ e`. -/
lemma incl_functorOf {a b : G.Vertex} (e : a ⟶ b) :
    incl ℓ Z hG e ≫ emapOf ℓ Z hG f φ a b = φ e := by
  rw [emapOf_eq ℓ Z hG f φ ((Quiver.Path.nil : G.Path a a).cons e),
    reassoc_of% (incl_homIso ℓ Z hG e), phi_cons, phi_nil]
  exact ((λ_ (ℓ e)).inv ≫= (leftUnitor_comp_eId (φ e)).symm).trans (Iso.inv_hom_id_assoc _ _)

end Functor

/-- For a one-edge path `e`, the inverse of `mu p e` is `lab p ◁ λ⁻¹`. -/
lemma mu_edge_inv {a b c : G.Vertex} (p : G.Path a b) (e : b ⟶ c) :
    (mu ℓ p ((Quiver.Path.nil : G.Path b b).cons e)).inv = lab ℓ p ◁ (λ_ (ℓ e)).inv := by
  rw [mu_cons_inv, mu_nil]
  monoidal

/-- On a path, a functor is the composite of its edge maps after identifying the source
hom-object with the path label. -/
lemma emap_path {D : Type u} [Category.{w} D] [EnrichedOrdinaryCategory W D]
    (F : VFunctor W (ForgetEnrichment W (Obj ℓ Z hG)) D)
    {a b : G.Vertex} (p : G.Path a b) :
    (homIso ℓ Z hG p).inv ≫ F.emap (a : ForgetEnrichment W (Obj ℓ Z hG))
        (b : ForgetEnrichment W (Obj ℓ Z hG)) =
      Phi ℓ (fun a => F.obj (a : ForgetEnrichment W (Obj ℓ Z hG)))
        (fun a b e => incl ℓ Z hG e ≫ F.emap (a : ForgetEnrichment W (Obj ℓ Z hG))
          (b : ForgetEnrichment W (Obj ℓ Z hG))) p := by
  let f : G.Vertex → D := fun a => F.obj (a : ForgetEnrichment W (Obj ℓ Z hG))
  let k : ∀ a b : G.Vertex, hom ℓ Z a b ⟶ (f a ⟶[W] f b) :=
    fun a b => F.emap (a : ForgetEnrichment W (Obj ℓ Z hG))
      (b : ForgetEnrichment W (Obj ℓ Z hG))
  let φ : ∀ ⦃a b : G.Vertex⦄ (e : a ⟶ b), ℓ e ⟶ (f a ⟶[W] f b) :=
    fun a b e => incl ℓ Z hG e ≫ k a b
  -- induction on the path: `emap` sends composites of paths to composites of their images
  induction p with
  | nil => exact F.emap_id (a : ForgetEnrichment W (Obj ℓ Z hG))
  | @cons b' c' p e ih =>
    -- `F` sends the composition of `hom` to the composition of `D`
    have h : comp ℓ Z hG a b' c' ≫ k a c' =
        (k a b' ⊗ₘ k b' c') ≫ eComp W (f a) (f b') (f c') :=
      F.emap_comp (a : ForgetEnrichment W (Obj ℓ Z hG))
        (b' : ForgetEnrichment W (Obj ℓ Z hG)) (c' : ForgetEnrichment W (Obj ℓ Z hG))
    rw [comp_eq ℓ Z hG p ((Quiver.Path.nil : G.Path _ _).cons e), compAt] at h
    have h' := ((mu ℓ p ((Quiver.Path.nil : G.Path b' b').cons e)).inv ≫
      ((homIso ℓ Z hG p).inv ⊗ₘ
        (homIso ℓ Z hG ((Quiver.Path.nil : G.Path b' b').cons e)).inv)) ≫= h
    simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Iso.inv_hom_id, MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id_assoc] at h'
    -- the induction hypothesis for `p`, then the last edge by `incl`
    rw [show (homIso ℓ Z hG (p.cons e)).inv ≫ k a c' = _ from h', ih]
    rw [mu_edge_inv, phi_cons, MonoidalCategory.tensorHom_def',
      MonoidalCategory.tensorHom_def', incl]
    simp only [f, k, Category.assoc]
    exact (MonoidalCategory.whiskerLeft_comp_assoc _ _ _ _).symm.trans
      (Category.assoc (λ_ (ℓ e)).inv _ (F.emap _ _) ▸ rfl)


/-- A functor out of the free category is determined by its vertices and edge maps. -/
lemma reconstruct {D : Type u} [Category.{w} D] [EnrichedOrdinaryCategory W D]
    (F : VFunctor W (ForgetEnrichment W (Obj ℓ Z hG)) D) :
    F = functorOf ℓ Z hG (fun a => F.obj (a : ForgetEnrichment W (Obj ℓ Z hG)))
      (fun a b e => incl ℓ Z hG e ≫ F.emap (a : ForgetEnrichment W (Obj ℓ Z hG))
          (b : ForgetEnrichment W (Obj ℓ Z hG))) := by
  let f : G.Vertex → D := fun a => F.obj (a : ForgetEnrichment W (Obj ℓ Z hG))
  let k : ∀ a b : G.Vertex, hom ℓ Z a b ⟶ (f a ⟶[W] f b) :=
    fun a b => F.emap (a : ForgetEnrichment W (Obj ℓ Z hG))
      (b : ForgetEnrichment W (Obj ℓ Z hG))
  let φ : ∀ ⦃a b : G.Vertex⦄ (e : a ⟶ b), ℓ e ⟶ (f a ⟶[W] f b) :=
    fun a b e => incl ℓ Z hG e ≫ k a b
  apply vFunctor_ext_obj_heq
  · rfl
  · intro (a : G.Vertex) (b : G.Vertex)
    apply heq_of_eq
    rw [functorOf_emap]
    by_cases h : Nonempty (G.Path a b)
    · obtain ⟨p⟩ := h
      rw [emapOf_eq ℓ Z hG f φ p]
      exact (Iso.inv_comp_eq _).mp (emap_path ℓ Z hG F p)
    · exact (homInitial ℓ Z (not_nonempty_iff.mp h)).hom_ext _ _

end Cat

/-! ## The paper's convention -/

section Paper

open MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V] {G : DirectedGraph.{u}}

/-- The labelling in the monoidal opposite. -/
def mopLab (ℓ : G.Labelling V) : G.Labelling Vᴹᵒᵖ := fun _ _ e => mop (ℓ e)

/-- The identification of the library-order label of the reversed labelling with the paper's
label `DirectedGraph.pathLabel`, one tensor factor at a time. -/
def labIso (ℓ : G.Labelling V) {a : G.Vertex} : ∀ {b : G.Vertex} (p : G.Path a b),
    unmop (lab (mopLab ℓ) p) ≅ DirectedGraph.pathLabel ℓ p
  | _, .nil => Iso.refl _
  | _, .cons p e => whiskerLeftIso (ℓ e) (labIso ℓ p)

/-- `labIso` of the empty path is the identity. -/
@[simp] lemma labIso_nil (ℓ : G.Labelling V) (a : G.Vertex) :
    labIso ℓ (Quiver.Path.nil : G.Path a a) = Iso.refl _ := rfl

/-- `labIso (p.cons e)` is `ℓ e ◁ labIso p`. -/
@[simp] lemma labIso_cons_hom (ℓ : G.Labelling V) {a b c : G.Vertex} (p : G.Path a b)
    (e : b ⟶ c) : (labIso ℓ (p.cons e)).hom = ℓ e ◁ (labIso ℓ p).hom := rfl

/-- The paper's composition isomorphism along the empty path is the left unitor. -/
@[simp] lemma pathLabelCompIso_nil (ℓ : G.Labelling V) {a b : G.Vertex} (p : G.Path a b) :
    DirectedGraph.pathLabelCompIso ℓ p (Quiver.Path.nil : G.Path b b) =
      λ_ (DirectedGraph.pathLabel ℓ p) := rfl

/-- The coherence isomorphism `mu` of the reversed labelling is the paper's canonical
isomorphism `ℓ(q) ⊗ ℓ(p) ≅ ℓ(qp)`, read through `labIso`. -/
lemma unmop_mu (ℓ : G.Labelling V) {a b : G.Vertex} (p : G.Path a b) :
    ∀ {c : G.Vertex} (q : G.Path b c),
      (mu (mopLab ℓ) p q).hom.unmop ≫ (labIso ℓ (p.comp q)).hom =
        ((labIso ℓ q).hom ⊗ₘ (labIso ℓ p).hom) ≫ (DirectedGraph.pathLabelCompIso ℓ p q).hom
  | _, .nil => by
    simp only [mu_nil, labIso_nil, pathLabelCompIso_nil, Iso.refl_hom]
    refine (leftUnitor_naturality (labIso ℓ p).hom).symm.trans ?_
    exact (MonoidalCategory.id_tensorHom _ _).symm =≫ _
  | _, .cons q e => by
    have ih := unmop_mu ℓ p q
    change ((α_ _ _ _).hom ≫ ℓ e ◁ (mu (mopLab ℓ) p q).hom.unmop) ≫
        ℓ e ◁ (labIso ℓ (p.comp q)).hom =
      ((ℓ e ◁ (labIso ℓ q).hom) ⊗ₘ (labIso ℓ p).hom) ≫ (α_ _ _ _).hom ≫
        ℓ e ◁ (DirectedGraph.pathLabelCompIso ℓ p q).hom
    rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ih]
    monoidal

/-- Initiality is unchanged by unwrapping the monoidal opposite. -/
def unmopIsInitial {X : Vᴹᵒᵖ} (h : IsInitial X) : IsInitial (unmop X) :=
  IsInitial.ofUniqueHom (fun y => (h.to (mop y)).unmop)
    (fun y f => by
      have := h.hom_ext (f.mop) (h.to (mop y))
      exact congr(($(this)).unmop))

/-- Injectivity and surjectivity of the restriction map out of `forestVCat` in Lemma A.3. -/
private lemma bijective_paperVCat_functorOf (Z : MonoidalInitial V) (G : DirectedGraph.{u})
    (hG : G.IsForest) (ℓ : G.Labelling V) (D : PaperVCat.{w, v, u} V) :
    Function.Bijective (fun F : forestVCat (mopLab ℓ) (reverseInitial Z) hG ⟶ D =>
      (⟨fun a => F.obj a,
        fun a b e => (incl (mopLab ℓ) (reverseInitial Z) hG e).unmop ≫
          (F.emap a b).unmop⟩ :
        Σ f : G.Vertex → D.carrier,
          ∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b), ℓ e ⟶ unmop (f a ⟶[Vᴹᵒᵖ] f b))) := by
  let Z' := reverseInitial Z
  let ℓ' := mopLab ℓ
  constructor
  · intro F₁ F₂ hF
    simp only [Sigma.mk.injEq] at hF
    obtain ⟨h₁, h₂⟩ := hF
    have key : ∀ (f₁ f₂ : G.Vertex → D.carrier)
        (φ₁ : ∀ ⦃a b : G.Vertex⦄ (e : a ⟶ b), ℓ' e ⟶ (f₁ a ⟶[Vᴹᵒᵖ] f₁ b))
        (φ₂ : ∀ ⦃a b : G.Vertex⦄ (e : a ⟶ b), ℓ' e ⟶ (f₂ a ⟶[Vᴹᵒᵖ] f₂ b)),
        f₁ = f₂ → HEq (fun a b (e : G.Edge a b) => (φ₁ e).unmop)
          (fun a b (e : G.Edge a b) => (φ₂ e).unmop) →
          functorOf ℓ' Z' hG f₁ φ₁ = functorOf ℓ' Z' hG f₂ φ₂ := by
      rintro f₁ f₂ φ₁ φ₂ rfl h
      have h' := eq_of_heq h
      have : φ₁ = φ₂ := by
        funext a b e
        exact MonoidalOpposite.hom_ext congr($h' a b e)
      rw [this]
    rw [reconstruct ℓ' Z' hG F₁, reconstruct ℓ' Z' hG F₂]
    exact key _ _ _ _ h₁ h₂
  · rintro ⟨f, ψ⟩
    refine ⟨functorOf ℓ' Z' hG f (fun a b e => (ψ e).mop), ?_⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext a b e
    have hi := incl_functorOf ℓ' Z' hG f (fun a b e => (ψ e).mop) e
    exact congr(($(hi)).unmop)

/-- **Lemma A.3** ([forsman2026syntactic]) in the paper's convention: the free category of the
reversed labelling over `Vᴹᵒᵖ` with the reversed absorbing initial object. The hom
identifications `θ` are `homIso` followed by `labIso`. -/
theorem exists_paperVCat_free_of_isForest (Z : MonoidalInitial V) (G : DirectedGraph.{u})
    (hG : G.IsForest)
    (ℓ : G.Labelling V) :
    ∃ (C : PaperVCat.{w, v, u} V) (ι : G.Vertex ≃ C.carrier)
      (θ : ∀ (a b : G.Vertex) (p : G.Path a b),
        unmop (ι a ⟶[Vᴹᵒᵖ] ι b) ≅ DirectedGraph.pathLabel ℓ p)
      (incl : ∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b), ℓ e ⟶ unmop (ι a ⟶[Vᴹᵒᵖ] ι b)),
      (∀ a b : G.Vertex, IsEmpty (G.Path a b) →
        Nonempty (Limits.IsInitial (unmop (ι a ⟶[Vᴹᵒᵖ] ι b)))) ∧
      (∀ a b c : G.Vertex, IsEmpty (G.Path a b) ∨ IsEmpty (G.Path b c) →
        Nonempty (Limits.IsInitial (unmop (ι b ⟶[Vᴹᵒᵖ] ι c) ⊗ unmop (ι a ⟶[Vᴹᵒᵖ] ι b)))) ∧
      (∀ (a b c : G.Vertex) (p : G.Path a b) (q : G.Path b c),
        (eComp Vᴹᵒᵖ (ι a) (ι b) (ι c)).unmop ≫ (θ a c (p.comp q)).hom =
          ((θ b c q).hom ⊗ₘ (θ a b p).hom) ≫
            (DirectedGraph.pathLabelCompIso ℓ p q).hom) ∧
      (∀ a : G.Vertex, (eId Vᴹᵒᵖ (ι a)).unmop ≫ (θ a a Quiver.Path.nil).hom = 𝟙 (𝟙_ V)) ∧
      (∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b),
        incl e ≫ (θ a b ((Quiver.Path.nil : G.Path a a).cons e)).hom = (ρ_ (ℓ e)).inv) ∧
      ∀ D : PaperVCat.{w, v, u} V, Function.Bijective (fun F : C ⟶ D =>
        (⟨fun a => F.obj (ι a), fun a b e => incl e ≫ (F.emap (ι a) (ι b)).unmop⟩ :
          Σ f : G.Vertex → D.carrier,
            ∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b), ℓ e ⟶ unmop (f a ⟶[Vᴹᵒᵖ] f b))) := by
  -- the forest category built over `Vᴹᵒᵖ`, read back in `V` through `unmop`
  let Z' := reverseInitial Z
  let ℓ' := mopLab ℓ
  refine ⟨forestVCat ℓ' Z' hG, Equiv.refl _,
    fun a b p => (unmopFunctor V).mapIso (homIso ℓ' Z' hG p) ≪≫ labIso ℓ p,
    fun a b e => (incl ℓ' Z' hG e).unmop,
    fun a b h => ⟨unmopIsInitial (homInitial ℓ' Z' h)⟩, ?_, ?_, ?_, ?_,
    bijective_paperVCat_functorOf Z G hG ℓ⟩
  -- the tensor of an initial hom-object is initial
  · rintro a b c (h | h)
    · exact ⟨unmopIsInitial (initL Z' (homInitial ℓ' Z' h) _)⟩
    · exact ⟨unmopIsInitial (initR Z' _ (homInitial ℓ' Z' h))⟩
  -- composition, identities and the inclusion of edges, through `unmop`
  · intro a b c p q
    have h := congr(($(comp_homIso ℓ' Z' hG p q)).unmop)
    simp only [unmop_comp, unmop_tensorHom] at h
    change (comp ℓ' Z' hG a b c).unmop ≫ (homIso ℓ' Z' hG (p.comp q)).hom.unmop ≫
        (labIso ℓ (p.comp q)).hom =
      (((homIso ℓ' Z' hG q).hom.unmop ≫ (labIso ℓ q).hom) ⊗ₘ
        ((homIso ℓ' Z' hG p).hom.unmop ≫ (labIso ℓ p).hom)) ≫
          (DirectedGraph.pathLabelCompIso ℓ p q).hom
    rw [reassoc_of% h, unmop_mu, ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  · intro a
    change (eid ℓ' Z' hG a).unmop ≫
      (homIso ℓ' Z' hG (Quiver.Path.nil : G.Path a a)).hom.unmop ≫ 𝟙 _ = _
    rw [Category.comp_id, ← unmop_comp, eid_homIso]
    rfl
  · intro a b e
    have h := congr(($(incl_homIso ℓ' Z' hG e)).unmop)
    rw [unmop_comp] at h
    refine Eq.trans ?_ h
    change (incl ℓ' Z' hG e).unmop ≫
      (homIso ℓ' Z' hG ((Quiver.Path.nil : G.Path a a).cons e)).hom.unmop ≫
        ℓ e ◁ 𝟙 _ = _
    rw [MonoidalCategory.whiskerLeft_id]
    exact ((incl ℓ' Z' hG e).unmop ≫= Category.comp_id _)

end Paper

end UlmerBialgebras.Paper.Appendix.Forest
