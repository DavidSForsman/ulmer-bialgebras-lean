module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Kan.KanInserter
public import UlmerBialgebras.Kan.KanEquifier
public import UlmerBialgebras.Kan.LimKan

/-!
# Slices, commas and Eilenberg–Moore categories as PIE limits in `CAT`

`Over c` is the inserter of `𝟭 C` and the constant functor at `c` (`overIns`); with this
structure the development's strict creation results for inserters
(`Inserter.strictlyCreates_leftKan` and its dual in `UlmerBialgebras/Proofs/Sec4/Sec4.lean`) give
Corollary 4.15.
Also: constant functors preserve connected limits, and the projections of a product category
preserve colimits (first) and limits (second), for the comma case of Corollary 4.14.

## Main results

* `UlmerBialgebras.Paper.overIns`: `Over c` as the inserter of `𝟭 C` and the constant functor at
  `c`.
* `UlmerBialgebras.Paper.commaIns`: `Comma F G` as the inserter of `fst ⋙ F` and `snd ⋙ G` on
  `C × D`.
* `UlmerBialgebras.Paper.preservesLimitsOfShape_const_of_isConnected`: a constant functor preserves
  limits of connected shapes.
* `UlmerBialgebras.Paper.preservesColimitsOfShape_prod_fst`: the first projection of a product
  category preserves colimits.
* `UlmerBialgebras.Paper.preservesLimitsOfShape_prod_snd`: the second projection of a product
  category preserves limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 4.7 and Corollaries 4.14 and 4.15
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- `Over c` is the inserter of `𝟭 C` and the constant functor at `c`. -/
def overIns {C : Cat.{v, max u v}} (c : (C : Type (max u v))) :
    Inserter (Obj := Cat.{v, max u v}) (a := C) (b := C) (𝟙 C)
      ((Functor.const (C : Type (max u v))).obj c).toCatHom where
  pt := Cat.of (Over c)
  u := (Over.forget c).toCatHom
  φ := NatTrans.toCatHom₂ {
         app := fun X => X.hom
         naturality := fun X Y f => by simp }
  lift h α :=
    Functor.toCatHom {
      obj := fun x => Over.mk (α.toNatTrans.app x)
      map := fun {x y} f => Over.homMk (h.toFunctor.map f) (by simp)
      map_id := fun x => Over.OverMorphism.ext (by simp)
      map_comp := fun f g => Over.OverMorphism.ext (by simp) }
  lift_u _ _ := rfl
  lift_φ h α := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    simp
  lift_uniq {X} k h α hu hφ := by
    subst hu
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y f => ?_)
    · have hh : (k.toFunctor.obj x).hom = α.toNatTrans.app x := by
        simpa using congr_app (Cat.Hom₂.ext_iff.mp hφ) x
      change k.toFunctor.obj x = Over.mk (α.toNatTrans.app x)
      rw [← hh]
      rfl
    · apply Over.OverMorphism.ext
      simp
  lift₂ {X} {k₁ k₂} α h :=
    NatTrans.toCatHom₂ {
      app := fun x => Over.homMk (α.toNatTrans.app x) (by
          have := congr_app (Cat.Hom₂.ext_iff.mp h) x
          simpa using this.symm)
      naturality := fun x y f => Over.OverMorphism.ext (α.toNatTrans.naturality f) }
  lift₂_u _ _ := rfl
  lift₂_uniq β γ hβγ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    exact Over.OverMorphism.ext (congr_app (Cat.Hom₂.ext_iff.mp hβγ) x)

/-- A constant functor preserves limits of connected shapes. -/
instance preservesLimitsOfShape_const_of_isConnected {C D : Type*} [Category C] [Category D]
    (J : Type*) [Category J] [IsConnected J] (x : D) :
    PreservesLimitsOfShape J ((Functor.const C).obj x) where
  preservesLimit {K} := ⟨fun {s} _ => by
    let e : K ⋙ (Functor.const C).obj x ≅ (Functor.const J).obj x :=
      NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp)
    refine ⟨(IsLimit.postcomposeHomEquiv e _) ?_⟩
    exact IsLimit.ofIsoLimit (isLimitConstCone J x) (Cone.ext (Iso.refl _) (by intro j; simp [e]))⟩

section ProdProj

variable {A B : Type*} [Category A] [Category B] {J : Type*} [Category J]

/-- The first projection of a product category preserves colimits. -/
instance preservesColimitsOfShape_prod_fst : PreservesColimitsOfShape J
    (CategoryTheory.Prod.fst A B) where
  preservesColimit {K} := ⟨fun {c} hc => ⟨
    { desc := fun s => (hc.desc
        { pt := (s.pt, c.pt.2)
          ι := { app := fun j => (s.ι.app j, (c.ι.app j).2)
                 naturality := fun i j f => by
                   ext
                   · simpa using s.w f
                   · dsimp; rw [Category.comp_id]; exact (Prod.ext_iff.mp (c.w f)).2 }}).1
      fac := fun s j => by
        have := (Prod.ext_iff.mp (hc.fac
          { pt := (s.pt, c.pt.2)
            ι := { app := fun j => (s.ι.app j, (c.ι.app j).2)
                   naturality := fun i j f => by
                     ext
                     · simpa using s.w f
                     · dsimp; rw [Category.comp_id]; exact (Prod.ext_iff.mp (c.w f)).2 }} j)).1
        exact this
      uniq := fun s m hm => by
        let s' : Cocone K :=
          { pt := (s.pt, c.pt.2)
            ι := { app := fun j => (s.ι.app j, (c.ι.app j).2)
                   naturality := fun i j f => by
                     ext
                     · simpa using s.w f
                     · dsimp; rw [Category.comp_id]; exact (Prod.ext_iff.mp (c.w f)).2 }}
        have := hc.uniq s' (m, 𝟙 _) (fun j => by
          ext
          · simpa using hm j
          · exact Category.comp_id _)
        exact (Prod.ext_iff.mp this).1 }⟩⟩

/-- The second projection of a product category preserves limits. -/
instance preservesLimitsOfShape_prod_snd : PreservesLimitsOfShape J (CategoryTheory.Prod.snd A B)
    where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => (hc.lift
        { pt := (c.pt.1, s.pt)
          π := { app := fun j => ((c.π.app j).1, s.π.app j)
                 naturality := fun i j f => by
                   ext
                   · dsimp; rw [Category.id_comp]; exact (Prod.ext_iff.mp (c.w f)).1.symm
                   · simpa using (s.w f).symm }}).2
      fac := fun s j => by
        have := (Prod.ext_iff.mp (hc.fac
          { pt := (c.pt.1, s.pt)
            π := { app := fun j => ((c.π.app j).1, s.π.app j)
                   naturality := fun i j f => by
                     ext
                     · dsimp; rw [Category.id_comp]; exact (Prod.ext_iff.mp (c.w f)).1.symm
                     · simpa using (s.w f).symm }} j)).2
        exact this
      uniq := fun s m hm => by
        let s' : Cone K :=
          { pt := (c.pt.1, s.pt)
            π := { app := fun j => ((c.π.app j).1, s.π.app j)
                   naturality := fun i j f => by
                     ext
                     · dsimp; rw [Category.id_comp]; exact (Prod.ext_iff.mp (c.w f)).1.symm
                     · simpa using (s.w f).symm }}
        have := hc.uniq s' (𝟙 _, m) (fun j => by
          ext
          · exact Category.id_comp _
          · simpa using hm j)
        exact (Prod.ext_iff.mp this).2 }⟩⟩

end ProdProj

/-- `Comma F G` is the inserter of `fst ⋙ F` and `snd ⋙ G` on `C × D`. -/
def commaIns {C D E : Cat.{v, max u v}} (F : C ⟶ E) (G : D ⟶ E) :
    Inserter (Obj := Cat.{v, max u v})
      (a := Cat.of (Prod (C : Type (max u v)) (D : Type (max u v)))) (b := E)
      (CategoryTheory.Prod.fst (C : Type (max u v)) (D : Type (max u v)) ⋙
        F.toFunctor).toCatHom
      (CategoryTheory.Prod.snd (C : Type (max u v)) (D : Type (max u v)) ⋙
        G.toFunctor).toCatHom where
  pt := Cat.of (Comma F.toFunctor G.toFunctor)
  u := ((Comma.fst _ _).prod' (Comma.snd _ _)).toCatHom
  φ := NatTrans.toCatHom₂ {
         app := fun X => X.hom
         naturality := fun X Y f => by exact f.w }
  lift h α :=
    Functor.toCatHom {
      obj := fun x => ⟨(h.toFunctor.obj x).1, (h.toFunctor.obj x).2, α.toNatTrans.app x⟩
      map := fun {x y} f => ⟨(h.toFunctor.map f).1, (h.toFunctor.map f).2, by
          simpa using α.toNatTrans.naturality f⟩
      map_id := fun x => by apply Comma.hom_ext <;> simp
      map_comp := fun f g => by apply Comma.hom_ext <;> simp }
  lift_u _ _ := rfl
  lift_φ h α := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    simp
  lift_uniq {X} k h α hu hφ := by
    subst hu
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y f => ?_)
    · have hh : (k.toFunctor.obj x).hom = α.toNatTrans.app x := by
        simpa using congr_app (Cat.Hom₂.ext_iff.mp hφ) x
      change k.toFunctor.obj x = Comma.mk (k.toFunctor.obj x).left (k.toFunctor.obj x).right
          (α.toNatTrans.app x)
      rw [← hh]
      rfl
    · apply Comma.hom_ext <;> simp
  lift₂ {X} {k₁ k₂} α h :=
    NatTrans.toCatHom₂ {
      app := fun x => ⟨(α.toNatTrans.app x).1, (α.toNatTrans.app x).2, by
          have := congr_app (Cat.Hom₂.ext_iff.mp h) x
          simpa using this.symm⟩
      naturality := fun x y f => by
        apply Comma.hom_ext
        · exact (Prod.ext_iff.mp (α.toNatTrans.naturality f)).1
        · exact (Prod.ext_iff.mp (α.toNatTrans.naturality f)).2 }
  lift₂_u _ _ := rfl
  lift₂_uniq β γ hβγ := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    apply Comma.hom_ext
    · exact (Prod.ext_iff.mp (congr_app (Cat.Hom₂.ext_iff.mp hβγ) x)).1
    · exact (Prod.ext_iff.mp (congr_app (Cat.Hom₂.ext_iff.mp hβγ) x)).2

end UlmerBialgebras.Paper
