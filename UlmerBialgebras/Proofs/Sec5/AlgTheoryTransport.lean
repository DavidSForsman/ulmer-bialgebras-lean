module

public import UlmerBialgebras.Paper.Sec6DefsAlgTheory

/-!
# Transporting models along a functor that preserves finite products

For a functor `E : C ⥤ D` preserving finite products, an `L`-structure `M` in `C` gives the
`L`-structure `E ∘ M` in `D`, with `funMap f` the composite of the inverse product comparison with
`E (funMap f)`. Terms realize compatibly (`map_realize`), so models go to models and
homomorphisms to homomorphisms: a functor `transport E : Mod_C(T) ⥤ Mod_D(T)` over `E^S`.
Transport is functorial in `E` and the identity for `E = 𝟭`, so a strict isomorphism of
categories `C ≅ D` gives a strict isomorphism `Mod_C(T) ≅ Mod_D(T)` over it
(`modelCat_transport`), for instance along `AsSmall.up`.

## Main results

* `UlmerBialgebras.Paper.MSLanguage.map_realize`: `E (t^M) = φ ≫ t^{E ∘ M}`.
* `UlmerBialgebras.Paper.MSLanguage.transport`: the functor `Mod_C(T) ⥤ Mod_D(T)`.
* `UlmerBialgebras.Paper.MSLanguage.modelCat_transport`: the isomorphism of model categories.

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
-/

@[expose] public section

universe v u v' u' v'' u'' u₄ u₅

namespace UlmerBialgebras.Paper.MSLanguage

open CategoryTheory Limits

variable {L : MSLanguage.{u₄, u₅}}
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
variable {B : Type u''} [Category.{v''} B] [HasFiniteProducts B]

section Map

variable (E : C ⥤ D) [PreservesFiniteProducts E]

/-- The `L`-structure `E ∘ M` induced by a finite-product-preserving functor. -/
@[instance_reducible]
noncomputable def mapStructure (M : L.Sorts → C) [L.Structure M] :
    L.Structure (fun s => E.obj (M s)) :=
  ⟨fun f => inv (piComparison E fun i => M (L.argSorts f i)) ≫ E.map (funMap f)⟩

/-- The function symbols of `mapStructure E M` are `E` of those of `M`, after the inverse of the
comparison `E (∏ X) ⟶ ∏ E X`. -/
lemma mapStructure_funMap (M : L.Sorts → C) [L.Structure M] (f : L.Functions) :
    @funMap L D _ _ _ (mapStructure E M) f =
      inv (piComparison E fun i => M (L.argSorts f i)) ≫ E.map (funMap f) :=
  rfl

/-- **Terms realize compatibly**: `E (t^M) = φ ≫ t^{E ∘ M}`, with `φ` the product
comparison. -/
lemma map_realize (M : L.Sorts → C) [L.Structure M] {n : ℕ} {Γ : Fin n → L.Sorts} :
    ∀ {s : L.Sorts} (t : L.Term Γ s),
      E.map (t.realize M) = piComparison E (fun i => M (Γ i)) ≫
        @Term.realize L D _ _ (fun s => E.obj (M s)) (mapStructure E M) n Γ s t
  | _, .var i => by simp [Term.realize]
  | _, .func f ts => by
    simp only [Term.realize, Functor.map_comp]
    have h : E.map (Pi.lift fun i => (ts i).realize M) =
        (Pi.lift fun i => E.map ((ts i).realize M)) ≫
          inv (piComparison E fun i => M (L.argSorts f i)) := by
      rw [← map_lift_piComparison, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hl : (Pi.lift fun i => (piComparison E fun i => M (Γ i)) ≫
        @Term.realize L D _ _ (fun s => E.obj (M s)) (mapStructure E M) n Γ _ (ts i)) =
        piComparison E (fun i => M (Γ i)) ≫ Pi.lift fun i =>
          @Term.realize L D _ _ (fun s => E.obj (M s)) (mapStructure E M) n Γ _ (ts i) := by
      ext i; simp
    rw [h]
    simp only [fun i => map_realize M (ts i)]
    rw [hl]
    simp only [Category.assoc]
    rfl

/-- `E ∘ M` is a model of `T` when `M` is. -/
lemma map_model (M : L.Sorts → C) [L.Structure M] {T : L.Theory} [M ⊨ T] :
    @Theory.Model L D _ _ (fun s => E.obj (M s)) (mapStructure E M) T := by
  let := mapStructure E M
  refine ⟨fun φ hφ => ?_⟩
  have h := congrArg E.map (Theory.Model.realize_of_mem (M := M) φ hφ)
  rw [map_realize, map_realize] at h
  exact (cancel_epi _).1 h

/-- `E` maps homomorphisms to homomorphisms of the induced structures. -/
lemma map_hom {M N : L.Sorts → C} [L.Structure M] [L.Structure N] (h : L.Hom M N)
    (f : L.Functions) :
    @funMap L D _ _ _ (mapStructure E M) f ≫ E.map (h.toFun (L.resSort f)) =
      Limits.Pi.map (fun i => E.map (h.toFun (L.argSorts f i))) ≫
        @funMap L D _ _ _ (mapStructure E N) f := by
  rw [mapStructure_funMap, mapStructure_funMap, Category.assoc,
    ← E.map_comp, h.map_fun', E.map_comp, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq]
  ext i
  simp only [Category.assoc, Limits.Pi.map_π, piComparison_comp_π_assoc,
    piComparison_comp_π, ← Functor.map_comp]

variable {T : L.Theory}

/-- **Transport of models** along `E`: `M ↦ E ∘ M`, `h ↦ E h`. -/
noncomputable def transport : T.ModelCat C ⥤ T.ModelCat D where
  obj A :=
    letI := mapStructure E A.Carrier
    haveI := map_model E A.Carrier (T := T)
    ⟨fun s => E.obj (A.Carrier s)⟩
  map {A B} h := @Hom.mk L D _ _ _ (mapStructure E A.Carrier) _ (mapStructure E B.Carrier)
    (fun s => E.map (h.toFun s)) (map_hom E h)
  map_id _ := Hom.ext (funext fun _ => E.map_id _)
  map_comp _ _ := Hom.ext (funext fun _ => E.map_comp _ _)

/-- Transport commutes with the forgetful functors. -/
lemma transport_forget :
    transport (T := T) E ⋙ Theory.ModelCat.forget D T =
      Theory.ModelCat.forget C T ⋙ Functor.pi fun _ : L.Sorts => E :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by
    funext s
    simp only [Functor.comp_map, CategoryTheory.Pi.comp_apply, CategoryTheory.Functor.eqToHom_proj]
    exact ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

end Map

section Ext

variable {T : L.Theory}

/-- Two models with the same carrier and the same operations are equal. -/
lemma modelCat_eq {M : L.Sorts → C} (s s' : L.Structure M) {hs : @Theory.Model L C _ _ M s T}
    {hs' : @Theory.Model L C _ _ M s' T} (h : ∀ f, s.funMap f = s'.funMap f) :
    (@Theory.ModelCat.mk L C _ _ T M s hs) = @Theory.ModelCat.mk L C _ _ T M s' hs' := by
  obtain ⟨g⟩ := s
  obtain ⟨g'⟩ := s'
  obtain rfl : g = g' := funext h
  rfl

/-- Composition of model homomorphisms is componentwise. -/
lemma comp_toFun {A A' A'' : T.ModelCat C} (g : A ⟶ A') (h : A' ⟶ A'') (s : L.Sorts) :
    Hom.toFun (g ≫ h) s = Hom.toFun g s ≫ Hom.toFun h s :=
  rfl

/-- The components of `eqToHom` between models. -/
lemma eqToHom_toFun {A A' : T.ModelCat C} (h : A = A') (s : L.Sorts) :
    Hom.toFun (eqToHom h) s = eqToHom (by rw [h]) := by
  subst h
  rfl

end Ext

section Functoriality

variable {T : L.Theory}

/-- Transport along the identity is the identity. -/
lemma transport_id (G : C ⥤ C) [PreservesFiniteProducts G] (hG : G = 𝟭 C) :
    transport (T := T) G = 𝟭 _ := by
  subst hG
  refine CategoryTheory.Functor.ext (fun A => modelCat_eq _ _ fun f => ?_) (fun A A' h => ?_)
  · rw [mapStructure_funMap]
    have : piComparison (𝟭 C) (fun i => A.Carrier (L.argSorts f i)) = 𝟙 _ := by
      ext i
      rw [Category.id_comp]
      exact piComparison_comp_π (𝟭 C) _ i
    rw [IsIso.inv_comp_eq, this, Category.id_comp, Functor.id_map]
  · refine Hom.ext (funext fun s => ?_)
    rw [comp_toFun, comp_toFun]
    refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (eqToHom_toFun _ s).symm
      ((_ ≫= eqToHom_toFun _ s).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Transport is functorial: along `E ⋙ E'` it is transport along `E` then `E'`. -/
lemma transport_comp (E : C ⥤ D) (E' : D ⥤ B) [PreservesFiniteProducts E]
    [PreservesFiniteProducts E'] [PreservesFiniteProducts (E ⋙ E')] :
    transport (T := T) (E ⋙ E') = transport E ⋙ transport E' := by
  refine CategoryTheory.Functor.ext (fun A => modelCat_eq _ _ fun f => ?_) (fun A A' h => ?_)
  · change inv (piComparison (E ⋙ E') _) ≫ E'.map (E.map (funMap f)) =
      inv (piComparison E' _) ≫ E'.map (inv (piComparison E _) ≫ E.map (funMap f))
    have hc : piComparison (E ⋙ E') (fun i => A.Carrier (L.argSorts f i)) =
        E'.map (piComparison E _) ≫
          piComparison E' (fun i => E.obj (A.Carrier (L.argSorts f i))) := by
      ext i
      rw [piComparison_comp_π, Category.assoc]
      change _ = E'.map _ ≫ piComparison E' (fun i => E.obj (A.Carrier (L.argSorts f i))) ≫
        Pi.π (fun b => E'.obj (E.obj (A.Carrier (L.argSorts f b)))) i
      rw [piComparison_comp_π, ← E'.map_comp, piComparison_comp_π]
      rfl
    rw [IsIso.inv_comp_eq, hc, Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  · refine Hom.ext (funext fun s => ?_)
    rw [comp_toFun, comp_toFun]
    refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (eqToHom_toFun _ s).symm
      ((_ ≫= eqToHom_toFun _ s).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end Functoriality

/-- **Models along an isomorphism of categories**: a strict isomorphism `E : C ≅ D` of categories
with finite products gives a strict isomorphism `Mod_C(T) ≅ Mod_D(T)` over `E^S`. -/
theorem modelCat_transport (E : C ⥤ D) (E' : D ⥤ C) (h₁ : E ⋙ E' = 𝟭 C)
    (h₂ : E' ⋙ E = 𝟭 D)
    (T : L.Theory) :
    ∃ (F : T.ModelCat C ⥤ T.ModelCat D) (G : T.ModelCat D ⥤ T.ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Theory.ModelCat.forget D T =
          Theory.ModelCat.forget C T ⋙ Functor.pi fun _ : L.Sorts => E := by
  let e : C ≌ D := .mk E E' (eqToIso h₁.symm) (eqToIso h₂)
  have : E.IsEquivalence := e.isEquivalence_functor
  have : E'.IsEquivalence := e.isEquivalence_inverse
  refine ⟨transport E, transport E', ?_, ?_, transport_forget E⟩
  · rw [← transport_comp, transport_id _ h₁]
  · rw [← transport_comp, transport_id _ h₂]

/-- The instance along `AsSmall.up`. -/
example (T : L.Theory) :
    ∃ (F : T.ModelCat C ⥤ T.ModelCat (AsSmall.{u₄} C))
      (G : T.ModelCat (AsSmall.{u₄} C) ⥤ T.ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Theory.ModelCat.forget _ T =
          Theory.ModelCat.forget C T ⋙ Functor.pi fun _ : L.Sorts => AsSmall.up :=
  modelCat_transport AsSmall.up AsSmall.down rfl rfl T

end UlmerBialgebras.Paper.MSLanguage
