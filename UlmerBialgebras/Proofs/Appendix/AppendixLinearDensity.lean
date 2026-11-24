module

public import UlmerBialgebras.Proofs.Appendix.AppendixReverse
public import UlmerBialgebras.Appendix.VCatHomDenseNatIso
public import UlmerBialgebras.Appendix.VCatConj

/-!
# Reconstruction from the linear probes

Infrastructure for the essential-surjectivity part of Theorem A.5.
The value of a pseudonatural family at the unit probe determines its
underlying ordinary functor. Point comparisons are natural in each
functor out of a probe.

## Main results

* `UlmerBialgebras.Paper.Appendix.Linear.toVFunctor`: the `V`-functor reconstructed from a
  pseudonatural family on the unit, arrow and three-object linear probes.
* `UlmerBialgebras.Paper.Appendix.Linear.isBiDense_linear`: the class of the point, arrow and
  three-object linear probes is bi-dense, in the library tensor convention.
* `UlmerBialgebras.Paper.Appendix.Linear.isBiDense_paperLinear`: the same class is bi-dense in the
  paper's tensor convention (Theorem A.5).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras.Paper.Appendix.Linear

open CategoryTheory MonoidalCategory
open AHomFamily

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- Regard an object and an ordinary morphism as a functor and transformation
out of the unit enriched category. -/
@[simps]
def unitLift (D : VCat.{w, v, max u w} V) :
    D.carrier ⥤ (unitVCat.{w, v, max u w} V ⟶ D) where
  obj d := unitPt d
  map f := unitCell f
  map_id d := by apply VNatTrans.ext; funext a; rfl
  map_comp f g := by apply VNatTrans.ext; funext a; rfl

/-- Evaluation of a functor or transformation at a vertex. -/
@[simps]
def vertexEval {A : VCat.{w, v, max u w} V} (a : A.carrier)
    (D : VCat.{w, v, max u w} V) : (A ⟶ D) ⥤ D.carrier where
  obj k := k.obj a
  map β := β.app a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation followed by the unit lift agrees with precomposition by a point. -/
def pointPrecompIso {A : VCat.{w, v, max u w} V} (a : A.carrier)
    (D : VCat.{w, v, max u w} V) :
    vertexEval a D ⋙ unitLift D ≅ precomp (unitPt a) D :=
  NatIso.ofComponents (fun k => eqToIso (unitPt_comp₁ a k).symm) (by
    intro k k' β
    apply VNatTrans.ext
    funext t
    change β.app a ≫ (eqToHom (unitPt_comp₁ a k').symm).app t =
      (eqToHom (unitPt_comp₁ a k).symm).app t ≫ β.app a
    simp only [VNatTrans.eqToHom_app]
    change β.app a ≫ (𝟙 _) = (𝟙 _) ≫ β.app a
    simp only [Category.comp_id, Category.id_comp])

/-- The component of `pointPrecompIso a D` at `k` is the `eqToHom` of `unitPt_comp₁ a k`. -/
lemma pointPrecompIso_hom_app {A : VCat.{w, v, max u w} V} (a : A.carrier)
    (D : VCat.{w, v, max u w} V) (k : A ⟶ D) :
    (pointPrecompIso a D).hom.app k = eqToHom (unitPt_comp₁ a k).symm := rfl

/-- The naturality square of `pointPrecompIso` in the vertex: for `f : a ⟶ b`,
`unitCell (k.map f) ≫ (pointPrecompIso b D).hom.app k =
(pointPrecompIso a D).hom.app k ≫ (unitCell f ▷ k)`. -/
theorem pointPrecompIso_vertex_naturality {A : VCat.{w, v, max u w} V}
    {a b : A.carrier} (f : a ⟶ b) (D : VCat.{w, v, max u w} V) (k : A ⟶ D) :
    unitCell (k.map f) ≫ (pointPrecompIso b D).hom.app k =
      (pointPrecompIso a D).hom.app k ≫ (unitCell f ▷ k) := by
  apply VNatTrans.ext
  funext t
  change k.map f ≫ (eqToHom (unitPt_comp₁ b k).symm).app t =
    (eqToHom (unitPt_comp₁ a k).symm).app t ≫ k.map f
  simp only [VNatTrans.eqToHom_app]
  change k.map f ≫ (𝟙 _) = (𝟙 _) ≫ k.map f
  simp only [Category.comp_id, Category.id_comp]

/-- Composing point restriction with unit evaluation is vertex evaluation. -/
theorem pointPrecompEval {A : VCat.{w, v, max u w} V} (a : A.carrier)
    (D : VCat.{w, v, max u w} V) :
    precomp (unitPt a) D ⋙ unitVCatEval D = vertexEval a D := rfl

/-- Enriched functor maps related by an isomorphism differ by conjugation. -/
theorem emap_eq_conjugate {A B : VCat.{w, v, max u w} V}
    {F G : A ⟶ B} (α : F ≅ G) (a b : A.carrier) :
    F.emap a b = G.emap a b ≫ eHomConj₂ (vNatIsoApp α a) (vNatIsoApp α b) := by
  have hb : α.hom.app b ≫ α.inv.app b = 𝟙 (F.obj b) :=
    (vNatIsoApp α b).hom_inv_id
  have h := (α.hom.vnaturality a b =≫ eHomWhiskerLeft V (F.obj a) (α.inv.app b))
  simpa only [Category.assoc, ← eHomWhiskerLeft_comp, hb, eHomWhiskerLeft_id,
    Category.comp_id, eHomConj₂, vNatIsoApp_hom, vNatIsoApp_inv] using h

/-- Postcomposition of an arrow functor reads as postcomposition of its generic map. -/
theorem arrowVFunctor_comp {A D : VCat.{w, v, max u w} V}
    (Z : MonoidalInitial V) (x : V) (a b : A.carrier)
    (f : x ⟶ (a ⟶[V] b)) (k : A ⟶ D) :
    (arrowVFunctor Z x a b f :
      VFunctor V (ForgetEnrichment V (ArrowObj.{w, v, max u w} Z x)) A.carrier).comp k =
      (arrowVFunctor Z x (k.obj a) (k.obj b) (f ≫ k.emap a b) :
        VFunctor V (ForgetEnrichment V (ArrowObj.{w, v, max u w} Z x)) D.carrier) := by
  exact arrowVFunctor_reconstruct Z x D
    ((arrowVFunctor Z x a b f : arrowVCat.{w, v, max u w} Z x ⟶ A) ≫ k)

section Family

variable {P : VCat.{w, v, max u w} V → Prop}
    {D C : VCat.{w, v, max u w} V}
    (Φ : AHomFamily P D C) (h1 : P (unitVCat.{w, v, max u w} V))

/-- The ordinary functor determined by the component at the unit probe. -/
def underlyingFunctor : D.carrier ⥤ C.carrier :=
  unitLift D ⋙ Φ.fn h1 ⋙ unitVCatEval C

/-- Pseudonaturality at each point compares vertex evaluation with the
ordinary functor reconstructed from the unit component. The target is vertex evaluation
after `Φ.fn hA`, written as restriction to the point followed by unit evaluation
(`pointPrecompEval`). -/
def pointComparison {A : VCat.{w, v, max u w} V} (hA : P A) (a : A.carrier) :
    vertexEval a D ⋙ underlyingFunctor Φ h1 ≅
      Φ.fn hA ⋙ precomp (unitPt a) C ⋙ unitVCatEval C :=
  (Functor.associator (vertexEval a D) (unitLift D)
    (Φ.fn h1 ⋙ unitVCatEval C)).symm ≪≫
  Functor.isoWhiskerRight (pointPrecompIso a D) (Φ.fn h1 ⋙ unitVCatEval C) ≪≫
  (Functor.associator (precomp (unitPt a) D) (Φ.fn h1) (unitVCatEval C)).symm ≪≫
  Functor.isoWhiskerRight (Φ.nat h1 hA (unitPt a)) (unitVCatEval C) ≪≫
  Functor.associator (Φ.fn hA) (precomp (unitPt a) C) (unitVCatEval C)

/-- The comparison at one vertex of one probe. -/
def pointIso {A : VCat.{w, v, max u w} V} (hA : P A) (k : A ⟶ D) (a : A.carrier) :
    (underlyingFunctor Φ h1).obj (k.obj a) ≅ ((Φ.fn hA).obj k).obj a :=
  (pointComparison Φ h1 hA a).app k

/-- Component formula with only the point transport and pseudonaturality. -/
theorem pointIso_hom {A : VCat.{w, v, max u w} V} (hA : P A)
    (k : A ⟶ D) (a : A.carrier) :
    (pointIso Φ h1 hA k a).hom =
      ((Φ.fn h1).map ((pointPrecompIso a D).hom.app k)).app (UnitVCat.star V) ≫
        ((Φ.nat h1 hA (unitPt a)).hom.app k).app (UnitVCat.star V) := by
  simp only [pointIso, pointComparison, underlyingFunctor, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map, unitVCatEval_map,
    Category.id_comp]
  -- the last associator leaves an identity on `(unitVCatEval C).obj _`, a `rfl`-unfolding
  -- of the codomain that `simp` cannot rewrite in place
  exact whisker_eq _ (Category.comp_id _)

/-- The comparison is natural in transformations between functors out of a probe. -/
theorem pointIso_naturality {A : VCat.{w, v, max u w} V} (hA : P A)
    {k k' : A ⟶ D} (β : k ⟶ k') (a : A.carrier) :
    (underlyingFunctor Φ h1).map (β.app a) ≫ (pointIso Φ h1 hA k' a).hom =
      (pointIso Φ h1 hA k a).hom ≫ ((Φ.fn hA).map β).app a :=
  (pointComparison Φ h1 hA a).hom.naturality β

/-- A family's functor sends equality transport to equality transport, componentwise. -/
theorem family_map_eqToHom {A : VCat.{w, v, max u w} V} (hA : P A)
    {k k' : A ⟶ D} (e : k = k') (a : A.carrier) :
    ((Φ.fn hA).map (eqToHom e)).app a =
      eqToHom (congrArg (fun m => ((Φ.fn hA).obj m).obj a) e) := by
  subst e
  exact congr(($((Φ.fn hA).map_id k)).app a)

/-- The point comparisons intertwine the family's precomposition isomorphisms. -/
theorem pointIso_precomp {A B : VCat.{w, v, max u w} V} (hA : P A) (hB : P B)
    (u : A ⟶ B) (k : B ⟶ D) (a : A.carrier) :
    (pointIso Φ h1 hA (u ≫ k) a).hom ≫ ((Φ.nat hA hB u).hom.app k).app a =
      (pointIso Φ h1 hB k (u.obj a)).hom := by
  have hc := AHomFamily.nat_comp_app Φ h1 hA hB (unitPt a) u k (UnitVCat.star V)
  have he := AHomFamily.nat_congr_app Φ h1 hB (unitPt_comp₁ a u) k (UnitVCat.star V)
  -- `(unitPt a).obj star` is `a`, and the last transport of `he` is an identity
  have h := hc.symm.trans (he.trans (whisker_eq _ (Category.comp_id _)))
  have e : unitPt (k.obj (u.obj a)) = (unitPt a ≫ u) ≫ k := by
    rw [unitPt_comp₁, unitPt_comp₁]
  have E := eqToHom (congrArg (fun m : unitVCat.{w, v, max u w} V ⟶ D =>
    ((Φ.fn h1).obj m).obj (UnitVCat.star V)) e) ≫= h
  simp only [eqToHom_trans_assoc] at E
  rw [pointIso_hom, pointIso_hom]
  change (((Φ.fn h1).map (eqToHom (unitPt_comp₁ a (u ≫ k)).symm)).app (UnitVCat.star V) ≫ _) ≫
      _ = ((Φ.fn h1).map (eqToHom (unitPt_comp₁ (u.obj a) k).symm)).app (UnitVCat.star V) ≫ _
  rw [family_map_eqToHom, family_map_eqToHom]
  exact (Category.assoc _ _ _).trans (E.trans (eqToHom_trans_assoc _ _ _))

/-- The family's hom map transported to the objects of the reconstructed functor. -/
def transportedEmap {A : VCat.{w, v, max u w} V} (hA : P A)
    (k : A ⟶ D) (a b : A.carrier) :
    (a ⟶[V] b) ⟶ ((underlyingFunctor Φ h1).obj (k.obj a) ⟶[V]
      (underlyingFunctor Φ h1).obj (k.obj b)) :=
  ((Φ.fn hA).obj k).emap a b ≫ eHomConj₂ (pointIso Φ h1 hA k a) (pointIso Φ h1 hA k b)

/-- Transported hom maps respect equality of the test functor, including their codomains. -/
theorem transportedEmap_heq {A : VCat.{w, v, max u w} V} (hA : P A)
    {k k' : A ⟶ D} (e : k = k') (a b : A.carrier) :
    HEq (transportedEmap Φ h1 hA k a b) (transportedEmap Φ h1 hA k' a b) := by
  subst e
  rfl

/-- Transport of the hom maps preserves enriched composition. -/
theorem transportedEmap_comp {A : VCat.{w, v, max u w} V} (hA : P A)
    (k : A ⟶ D) (a b c : A.carrier) :
    eComp V a b c ≫ transportedEmap Φ h1 hA k a c =
      (transportedEmap Φ h1 hA k a b ⊗ₘ transportedEmap Φ h1 hA k b c) ≫
        eComp V ((underlyingFunctor Φ h1).obj (k.obj a))
          ((underlyingFunctor Φ h1).obj (k.obj b))
          ((underlyingFunctor Φ h1).obj (k.obj c)) := by
  dsimp only [transportedEmap]
  rw [← Category.assoc, VFunctor.emap_comp, Category.assoc, eComp_eHomConj₂,
    ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]

/-- Transported hom maps respect precomposition between probes. -/
theorem transportedEmap_precomp {A B : VCat.{w, v, max u w} V}
    (hA : P A) (hB : P B) (u : A ⟶ B) (k : B ⟶ D) (a b : A.carrier) :
    transportedEmap Φ h1 hA (u ≫ k) a b =
      u.emap a b ≫ transportedEmap Φ h1 hB k (u.obj a) (u.obj b) := by
  have hp (t : A.carrier) : pointIso Φ h1 hA (u ≫ k) t ≪≫
      vNatIsoApp ((Φ.nat hA hB u).app k) t = pointIso Φ h1 hB k (u.obj t) := by
    apply Iso.ext
    exact pointIso_precomp Φ h1 hA hB u k t
  dsimp only [transportedEmap]
  have hm := emap_eq_conjugate ((Φ.nat hA hB u).app k) a b
  change ((Φ.fn hA).obj (u ≫ k)).emap a b =
    (u.emap a b ≫ ((Φ.fn hB).obj k).emap (u.obj a) (u.obj b)) ≫
      eHomConj₂ (vNatIsoApp ((Φ.nat hA hB u).app k) a)
        (vNatIsoApp ((Φ.nat hA hB u).app k) b) at hm
  rw [hm]
  simp only [Category.assoc]
  exact whisker_eq _ (whisker_eq _ ((eHomConj₂_trans _ _ _ _).trans
    (congrArg₂ (fun p q => eHomConj₂ (V := V) p q) (hp a) (hp b))))

/-- The proposed global hom map is read from the generic arrow of the source. -/
def reconstructedEmap (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x)) (d d' : D.carrier) :
    (d ⟶[V] d') ⟶ ((underlyingFunctor Φ h1).obj d ⟶[V]
      (underlyingFunctor Φ h1).obj d') :=
  transportedEmap Φ h1 (harr (d ⟶[V] d'))
    (arrowVFunctor Z (d ⟶[V] d') d d' (𝟙 _)) .src .tgt

/-- Changing an arrow label computes the proposed hom map on any generalized element. -/
theorem reconstructedEmap_arrow (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    (x : V) (d d' : D.carrier) (f : x ⟶ (d ⟶[V] d')) :
    f ≫ reconstructedEmap Φ h1 Z harr d d' =
      transportedEmap Φ h1 (harr x) (arrowVFunctor Z x d d' f) .src .tgt := by
  let y := (d ⟶[V] d')
  let u : arrowVCat.{w, v, max u w} Z x ⟶ arrowVCat.{w, v, max u w} Z y :=
    arrowVFunctor Z x (arrowSrc Z y) (arrowTgt Z y) f
  let k : arrowVCat.{w, v, max u w} Z y ⟶ D :=
    arrowVFunctor Z y d d' (𝟙 _)
  have hu : u ≫ k = arrowVFunctor Z x d d' f := by
    have h := arrowVFunctor_comp Z x (arrowSrc Z y) (arrowTgt Z y) f k
    exact h.trans (congrArg (fun z : x ⟶ (d ⟶[V] d') => arrowVFunctor Z x d d' z)
      (Category.comp_id f))
  have h := transportedEmap_precomp Φ h1 (harr x) (harr y) u k
    (arrowSrc Z x) (arrowTgt Z x)
  exact h.symm.trans (eq_of_heq (transportedEmap_heq Φ h1 (harr x) hu .src .tgt))

/-- Every hom map supplied by the family is read from the same global hom map. -/
theorem reconstructedEmap_read (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    {A : VCat.{w, v, max u w} V} (hA : P A) (k : A ⟶ D) (a b : A.carrier) :
    k.emap a b ≫ reconstructedEmap Φ h1 Z harr (k.obj a) (k.obj b) =
      transportedEmap Φ h1 hA k a b := by
  let x := (a ⟶[V] b)
  let u : arrowVCat.{w, v, max u w} Z x ⟶ A :=
    arrowVFunctor Z x a b (𝟙 _)
  have hu : u ≫ k = arrowVFunctor Z x (k.obj a) (k.obj b) (k.emap a b) := by
    have hc := arrowVFunctor_comp Z x a b (𝟙 _) k
    simp only [Category.id_comp] at hc
    exact hc
  have h := transportedEmap_precomp Φ h1 (harr x) hA u k
    (arrowSrc Z x) (arrowTgt Z x)
  have h' : transportedEmap Φ h1 (harr x)
      (arrowVFunctor Z x (k.obj a) (k.obj b) (k.emap a b)) .src .tgt =
        transportedEmap Φ h1 hA k a b := by
    have ht := eq_of_heq (transportedEmap_heq Φ h1 (harr x) hu .src .tgt)
    exact ht.symm.trans (h.trans (Category.id_comp _))
  exact (reconstructedEmap_arrow Φ h1 Z harr x (k.obj a) (k.obj b) (k.emap a b)).trans h' 

/-- The three-object linear probe forces the reconstructed hom maps to preserve composition. -/
theorem reconstructedEmap_comp (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    (hthree : ∀ x y : V, P (threeVCat.{w, v, max u w} Z x y))
    (d₀ d₁ d₂ : D.carrier) :
    eComp V d₀ d₁ d₂ ≫ reconstructedEmap Φ h1 Z harr d₀ d₂ =
      (reconstructedEmap Φ h1 Z harr d₀ d₁ ⊗ₘ reconstructedEmap Φ h1 Z harr d₁ d₂) ≫
        eComp V ((underlyingFunctor Φ h1).obj d₀)
          ((underlyingFunctor Φ h1).obj d₁) ((underlyingFunctor Φ h1).obj d₂) := by
  let x := (d₀ ⟶[V] d₁)
  let y := (d₁ ⟶[V] d₂)
  let k : threeVCat.{w, v, max u w} Z x y ⟶ D :=
    threeVFunctor Z x y d₀ d₁ d₂ (𝟙 _) (𝟙 _)
  have h01 := reconstructedEmap_read Φ h1 Z harr (hthree x y) k
    (.zero) (.one)
  have h12 := reconstructedEmap_read Φ h1 Z harr (hthree x y) k
    (.one) (.two)
  have h02 := reconstructedEmap_read Φ h1 Z harr (hthree x y) k
    (.zero) (.two)
  change (𝟙 x) ≫ reconstructedEmap Φ h1 Z harr d₀ d₁ =
    transportedEmap Φ h1 (hthree x y) k .zero .one at h01
  change (𝟙 y) ≫ reconstructedEmap Φ h1 Z harr d₁ d₂ =
    transportedEmap Φ h1 (hthree x y) k .one .two at h12
  change ((𝟙 x ⊗ₘ 𝟙 y) ≫ eComp V d₀ d₁ d₂) ≫
      reconstructedEmap Φ h1 Z harr d₀ d₂ =
    transportedEmap Φ h1 (hthree x y) k .zero .two at h02
  simp only [Category.id_comp] at h01 h12
  simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp] at h02
  have h := transportedEmap_comp Φ h1 (hthree x y) k .zero .one .two
  rw [← h02, ← h01, ← h12] at h
  exact (Category.id_comp _).symm.trans h

end Family

/-- The point comparisons are natural in ordinary morphisms of a probe.
This is the step that uses compatibility of the family with 2-cells. -/
theorem pointIso_vertex_naturality
    {P : VCat.{w, v, max u w} V → Prop}
    {D C : VCat.{w, v, max u w} V} (Ψ : PsFamily P D C)
    (h1 : P (unitVCat.{w, v, max u w} V))
    {A : VCat.{w, v, max u w} V} (hA : P A) (k : A ⟶ D)
    {a b : A.carrier} (f : a ⟶ b) :
    (underlyingFunctor Ψ.toAHomFamily h1).map (k.map f) ≫
        (pointIso Ψ.toAHomFamily h1 hA k b).hom =
      (pointIso Ψ.toAHomFamily h1 hA k a).hom ≫
        ((Ψ.fn hA).obj k).map f := by
  -- `Ψ.fn h1` applied to the naturality square of `pointPrecompIso` in the vertex
  have hρ : ((Ψ.fn h1).map (unitCell (k.map f))).app (UnitVCat.star V) ≫
      ((Ψ.fn h1).map ((pointPrecompIso b D).hom.app k)).app (UnitVCat.star V) =
    ((Ψ.fn h1).map ((pointPrecompIso a D).hom.app k)).app (UnitVCat.star V) ≫
      ((Ψ.fn h1).map (unitCell f ▷ k)).app (UnitVCat.star V) := by
    have h := congrArg (fun δ => ((Ψ.fn h1).map δ).app (UnitVCat.star V))
      (pointPrecompIso_vertex_naturality f D k)
    -- components of a composite are composites of components (`vCat_vcomp_app`, by `rfl`)
    exact (congr(($((Ψ.fn h1).map_comp
        (unitCell (k.map f)) ((pointPrecompIso b D).hom.app k))).app (UnitVCat.star V))).symm.trans
      (h.trans (congr(($((Ψ.fn h1).map_comp
        ((pointPrecompIso a D).hom.app k) (unitCell f ▷ k))).app (UnitVCat.star V))))
  have hσ := congr(($(Ψ.nat₂ h1 hA (unitCell f) k)).app (UnitVCat.star V))
  simp only [vCat_vcomp_app, vCat_whiskerRight_app, unitCell_app] at hσ
  rw [pointIso_hom, pointIso_hom]
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker hρ _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ hσ).trans (Category.assoc _ _ _).symm)))

/-- The transported enrichment computes the ordinary functor on every named morphism. -/
theorem transportedEmap_hom
    {P : VCat.{w, v, max u w} V → Prop}
    {D C : VCat.{w, v, max u w} V} (Ψ : PsFamily P D C)
    (h1 : P (unitVCat.{w, v, max u w} V))
    {A : VCat.{w, v, max u w} V} (hA : P A) (k : A ⟶ D)
    {a b : A.carrier} (f : a ⟶ b) :
    eHomEquiv V f ≫ transportedEmap Ψ.toAHomFamily h1 hA k a b =
      eHomEquiv V ((underlyingFunctor Ψ.toAHomFamily h1).map (k.map f)) := by
  dsimp only [transportedEmap]
  rw [← Category.assoc, VFunctor.emap_hom, eHomEquiv_comp_eHomConj₂]
  have h := pointIso_vertex_naturality Ψ h1 hA k f
  have he := (h =≫ (pointIso Ψ.toAHomFamily h1 hA k b).inv)
  rw [Category.assoc, (pointIso Ψ.toAHomFamily h1 hA k b).hom_inv_id,
    Category.comp_id] at he
  simpa only [Category.assoc] using congr(eHomEquiv V $(he.symm))

/-- The generic arrow gives compatibility of the global hom map with ordinary morphisms. -/
theorem reconstructedEmap_hom
    {P : VCat.{w, v, max u w} V → Prop}
    {D C : VCat.{w, v, max u w} V} (Ψ : PsFamily P D C)
    (h1 : P (unitVCat.{w, v, max u w} V)) (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    {d d' : D.carrier} (f : d ⟶ d') :
    eHomEquiv V f ≫ reconstructedEmap Ψ.toAHomFamily h1 Z harr d d' =
      eHomEquiv V ((underlyingFunctor Ψ.toAHomFamily h1).map f) := by
  let x := (d ⟶[V] d')
  let k : arrowVCat.{w, v, max u w} Z x ⟶ D :=
    arrowVFunctor Z x d d' (𝟙 _)
  let t : (arrowSrc Z x) ⟶ (arrowTgt Z x) :=
    (eHomEquiv V (C := (arrowVCat.{w, v, max u w} Z x).carrier)
      (X := arrowSrc Z x) (Y := arrowTgt Z x)).symm (eHomEquiv V (C := D.carrier) f)
  have ht : eHomEquiv V t = eHomEquiv V (C := D.carrier) f :=
    Equiv.apply_symm_apply _ _
  have hk : k.map t = f := by
    apply (eHomEquiv V).injective
    have he := k.emap_hom t
    rw [ht] at he
    exact he.symm.trans (Category.comp_id _)
  have h := transportedEmap_hom Ψ h1 (harr x) k t
  rw [ht, hk] at h
  exact h

/-- The functor reconstructed using only the unit, arrow and three-object linear probes. -/
@[simps]
def toVFunctor
    {P : VCat.{w, v, max u w} V → Prop}
    {D C : VCat.{w, v, max u w} V} (Ψ : PsFamily P D C)
    (h1 : P (unitVCat.{w, v, max u w} V)) (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    (hthree : ∀ x y : V, P (threeVCat.{w, v, max u w} Z x y)) : D ⟶ C where
  toFunctor := underlyingFunctor Ψ.toAHomFamily h1
  emap := reconstructedEmap Ψ.toAHomFamily h1 Z harr
  emap_comp := reconstructedEmap_comp Ψ.toAHomFamily h1 Z harr hthree
  emap_hom := reconstructedEmap_hom Ψ h1 Z harr

section Reconstruction

variable {P : VCat.{w, v, max u w} V → Prop}
    {D C : VCat.{w, v, max u w} V} (Ψ : PsFamily P D C)
    (h1 : P (unitVCat.{w, v, max u w} V)) (Z : MonoidalInitial V)
    (harr : ∀ x : V, P (arrowVCat.{w, v, max u w} Z x))
    (hthree : ∀ x y : V, P (threeVCat.{w, v, max u w} Z x y))

/-- Point comparisons assemble into an enriched natural transformation. -/
@[simps]
def comparisonCell {A : VCat.{w, v, max u w} V} (hA : P A) (k : A ⟶ D) :
    k ≫ toVFunctor Ψ h1 Z harr hthree ⟶ (Ψ.fn hA).obj k where
  app a := (pointIso Ψ.toAHomFamily h1 hA k a).hom
  vnaturality a b := by
    change (k.emap a b ≫ reconstructedEmap Ψ.toAHomFamily h1 Z harr (k.obj a) (k.obj b)) ≫
        eHomWhiskerLeft V ((underlyingFunctor Ψ.toAHomFamily h1).obj (k.obj a))
          (pointIso Ψ.toAHomFamily h1 hA k b).hom =
      ((Ψ.fn hA).obj k).emap a b ≫
        eHomWhiskerRight V (pointIso Ψ.toAHomFamily h1 hA k a).hom (((Ψ.fn hA).obj k).obj b)
    rw [reconstructedEmap_read Ψ.toAHomFamily h1 Z harr hA k a b]
    dsimp only [transportedEmap, eHomConj₂]
    simp only [Category.assoc, ← eHomWhiskerLeft_comp, Iso.inv_hom_id,
      eHomWhiskerLeft_id, Category.comp_id]

/-- The comparison is invertible because every point comparison is invertible. -/
noncomputable def comparisonIso {A : VCat.{w, v, max u w} V} (hA : P A) (k : A ⟶ D) :
    k ≫ toVFunctor Ψ h1 Z harr hthree ≅ (Ψ.fn hA).obj k := by
  haveI := VNatTrans.isIso_of_app (comparisonCell Ψ h1 Z harr hthree hA k)
    (fun a => (pointIso Ψ.toAHomFamily h1 hA k a).isIso_hom)
  exact asIso (comparisonCell Ψ h1 Z harr hthree hA k)

/-- Every pseudonatural family on the unit, arrow and three-object probes is represented. -/
noncomputable def representation : Ψ.toAHomFamily.Representation where
  g := toVFunctor Ψ h1 Z harr hthree
  iso A hA := NatIso.ofComponents (fun k => comparisonIso Ψ h1 Z harr hthree hA k) (by
    intro k k' β
    apply VNatTrans.ext
    funext a
    exact pointIso_naturality Ψ.toAHomFamily h1 hA β a)
  iso_nat A B hA hB u k := by
    apply VNatTrans.ext
    funext a
    change (pointIso Ψ.toAHomFamily h1 hA (u ≫ k) a).hom ≫
        ((Ψ.nat hA hB u).hom.app k).app a =
      (eqToHom (Category.assoc u k (toVFunctor Ψ h1 Z harr hthree))).app a ≫
        (pointIso Ψ.toAHomFamily h1 hB k (u.obj a)).hom
    rw [VNatTrans.eqToHom_app]
    exact (pointIso_precomp Ψ.toAHomFamily h1 hA hB u k a).trans (Category.id_comp _).symm

end Reconstruction

/-- Full bi-density for the exact linear class, in the library tensor convention. -/
theorem isBiDense_linear (Z : MonoidalInitial V) :
    IsBiDense (Obj := VCat.{w, v, max u w} V) (IsLinearProbe.{w, v, max u w} Z) := by
  refine ⟨isACellDense_of_probes Z _ (Or.inl rfl)
    (fun x => Or.inr (Or.inl ⟨x, rfl⟩)), ?_⟩
  intro D C Ψ
  exact ⟨representation Ψ (Or.inl rfl) Z
    (fun x => Or.inr (Or.inl ⟨x, rfl⟩))
    (fun x y => Or.inr (Or.inr ⟨x, y, rfl⟩))⟩

/-- The exact linear class is bi-dense with the paper's tensor convention. -/
theorem isBiDense_paperLinear (Z : MonoidalInitial V) :
    IsBiDense (Obj := PaperVCat.{w, v, max u w} V) (IsPaperLinearProbe.{w, v, max u w} Z) :=
  isBiDense_linear (reverseInitial Z)

end UlmerBialgebras.Paper.Appendix.Linear

