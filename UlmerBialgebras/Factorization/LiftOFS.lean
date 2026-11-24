module

public import Foundations.CategoryTheory.Factorization.OFS
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Theorem 6.3: lifting orthogonal factorization systems along PIE limits

We prove the three parts of Theorem 6.3 of *A Syntactic Approach to Ulmer's Bialgebras*:
an orthogonal factorization system lifts along a product, along an inserter of a pair of
functors preserving the left resp. right class, and along an equifier.

* `UlmerBialgebras.prodOFS` / `UlmerBialgebras.prodOFS_unique` — Theorem 6.3 (1);
* `UlmerBialgebras.insOFS` — Theorem 6.3 (2);
* `UlmerBialgebras.equifOFS` — Theorem 6.3 (3).

In each case the lifted classes are the preimages of the given ones along the projections
resp. the forgetful functor.  Uniqueness (among orthogonal factorization systems whose two
classes are sent into the given ones) is formalized only for products.

## Main results

* `UlmerBialgebras.prodOFS`: the product orthogonal factorization system (Theorem 6.3 (1)).
* `UlmerBialgebras.prodOFS_unique`: an orthogonal factorization system on the product whose classes
  the projections send into the given classes is `UlmerBialgebras.prodOFS` (Theorem 6.3 (1)).
* `UlmerBialgebras.insOFS`: the orthogonal factorization system on an inserter (Theorem 6.3 (2)).
* `UlmerBialgebras.equifOFS`: the orthogonal factorization system on an equifier (Theorem 6.3 (3)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 6.3
* [F. E. J. Linton, *Coequalizers in categories of algebras*][Linton1969]
* [T. Wißmann, *Minimality notions via factorization systems and
  examples*][Wissmann2022Minimality], Proposition 3.7
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory

/-! ## Products -/

section Prod

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]

/-- The product orthogonal factorization system: Theorem 6.3 (1). -/
def prodOFS (S : ∀ i, OFS (C i)) : OFS (∀ i, C i) :=
  OFS.mk' (fun _ _ f => ∀ i, (S i).E (f i)) (fun _ _ f => ∀ i, (S i).M (f i))
    (by
      intro x y f
      choose z e m he hm hfac using fun i => (S i).fact (f i)
      exact ⟨z, e, m, he, hm, funext fun i => hfac i⟩)
    (by
      intro x y z w e m he hm f g hsq
      have key : ∀ i, ∃! h : y i ⟶ z i, e i ≫ h = f i ∧ h ≫ m i = g i := by
        intro i
        exact (S i).orth (he i) (hm i) (f i) (g i) (funext_iff.mp hsq i)
      choose h hh huniq using key
      refine ⟨h, ⟨funext fun i => (hh i).1, funext fun i => (hh i).2⟩, ?_⟩
      rintro k ⟨k1, k2⟩
      exact funext fun i => huniq i (k i) ⟨funext_iff.mp k1 i, funext_iff.mp k2 i⟩)
    (by
      constructor
      intro x y z w f g hr hg i
      exact ((S i).e_isStableUnderRetracts).of_retract (hr.map (Pi.eval C i)) (hg i))
    (by
      constructor
      intro x y z w f g hr hg i
      exact ((S i).m_isStableUnderRetracts).of_retract (hr.map (Pi.eval C i)) (hg i))
/-- A morphism lies in the left class of `prodOFS S` iff each component `f i` lies in
that of `S i`. -/
@[simp] lemma prodOFS_E (S : ∀ i, OFS (C i)) {x y : ∀ i, C i} (f : x ⟶ y) :
    (prodOFS S).E f ↔ ∀ i, (S i).E (f i) := Iff.rfl

/-- A morphism lies in the right class of `prodOFS S` iff each component `f i` lies in
that of `S i`. -/
@[simp] lemma prodOFS_M (S : ∀ i, OFS (C i)) {x y : ∀ i, C i} (f : x ⟶ y) :
    (prodOFS S).M f ↔ ∀ i, (S i).M (f i) := Iff.rfl


/-- Theorem 6.3 (1), uniqueness: the product factorization system is the unique one
preserved by the projections. -/
theorem prodOFS_unique (S : ∀ i, OFS (C i)) (S' : OFS (∀ i, C i))
    (hE : ∀ ⦃x y : ∀ i, C i⦄ (f : x ⟶ y), S'.E f → ∀ i, (S i).E (f i))
    (hM : ∀ ⦃x y : ∀ i, C i⦄ (f : x ⟶ y), S'.M f → ∀ i, (S i).M (f i)) :
    S' = prodOFS S :=
  OFS.ext_of_le (fun _ _ _ h => hE _ h) (fun _ _ _ h => hM _ h)

end Prod

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-! ## Inserters -/

section Ins

variable {F G : C ⥤ D} (S : OFS C) (T : OFS D)

/-- The orthogonal factorization system lifted to an inserter: Theorem 6.3 (2). -/
def insOFS (hF : ∀ ⦃x y : C⦄ (e : x ⟶ y), S.E e → T.E (F.map e))
    (hG : ∀ ⦃x y : C⦄ (m : x ⟶ y), S.M m → T.M (G.map m)) : OFS (Ins F G) :=
  OFS.mk' (S.E.inverseImage (Ins.forget F G)) (S.M.inverseImage (Ins.forget F G))
    (by
      rintro x z f
      obtain ⟨y, e, m, he, hm, hfac⟩ := S.fact f.base
      have hfw : x.cell ≫ G.map f.base = F.map f.base ≫ z.cell := f.w
      obtain ⟨cy, ⟨hcy₁, hcy₂⟩, -⟩ :=
        T.orth (hF e he) (hG m hm) (x.cell ≫ G.map e) (F.map m ≫ z.cell) (by
          rw [Category.assoc, ← G.map_comp, hfac, hfw, ← Category.assoc, ← F.map_comp, hfac])
      refine ⟨⟨y, cy⟩, ⟨e, hcy₁.symm⟩, ⟨m, hcy₂⟩, he, hm, ?_⟩
      exact Ins.hom_ext (by simpa using hfac))
    (by
      rintro x v y w e m he hm f g hsq
      -- the underlying lifting problem in `C`
      have hb : f.base ≫ m.base = e.base ≫ g.base := Ins.Hom.ext_iff.mp hsq
      obtain ⟨θ, ⟨hθ₁, hθ₂⟩, hθuniq⟩ := S.orth he hm f.base g.base hb
      have hθ₁' : e.base ≫ θ = f.base := hθ₁
      have hθ₂' : θ ≫ m.base = g.base := hθ₂
      -- `θ` is a morphism of the inserter, by orthogonality of `F e` and `G m` in `D`
      have hsq' : (x.cell ≫ G.map f.base) ≫ G.map m.base
          = F.map e.base ≫ (v.cell ≫ G.map g.base) :=
        calc (x.cell ≫ G.map f.base) ≫ G.map m.base
            = x.cell ≫ G.map (f.base ≫ m.base) := by rw [G.map_comp, Category.assoc]
          _ = x.cell ≫ G.map (e.base ≫ g.base) := by rw [hb]
          _ = (x.cell ≫ G.map e.base) ≫ G.map g.base := by rw [G.map_comp, Category.assoc]
          _ = F.map e.base ≫ v.cell ≫ G.map g.base := by rw [e.w, Category.assoc]
      obtain ⟨_, _, huniq⟩ :=
        T.orth (hF _ he) (hG _ hm) (x.cell ≫ G.map f.base) (v.cell ≫ G.map g.base) hsq'
      have key : v.cell ≫ G.map θ = F.map θ ≫ y.cell := by
        have hA : F.map e.base ≫ (v.cell ≫ G.map θ) = x.cell ≫ G.map f.base := by
          rw [← Category.assoc, ← e.w, Category.assoc, ← G.map_comp, hθ₁']
        have hA' : (v.cell ≫ G.map θ) ≫ G.map m.base = v.cell ≫ G.map g.base := by
          rw [Category.assoc, ← G.map_comp, hθ₂']
        have hB : F.map e.base ≫ (F.map θ ≫ y.cell) = x.cell ≫ G.map f.base := by
          rw [← Category.assoc, ← F.map_comp, hθ₁', f.w]
        have hB' : (F.map θ ≫ y.cell) ≫ G.map m.base = v.cell ≫ G.map g.base := by
          rw [Category.assoc, m.w, ← Category.assoc, ← F.map_comp, hθ₂', ← g.w]
        rw [huniq _ ⟨hA, hA'⟩, huniq _ ⟨hB, hB'⟩]
      refine ⟨⟨θ, key⟩, ⟨Ins.hom_ext hθ₁', Ins.hom_ext hθ₂'⟩, ?_⟩
      rintro k ⟨k1, k2⟩
      exact Ins.hom_ext (hθuniq k.base ⟨Ins.Hom.ext_iff.mp k1, Ins.Hom.ext_iff.mp k2⟩))
    (by
      have := S.e_isStableUnderRetracts
      infer_instance)
    (by
      have := S.m_isStableUnderRetracts
      infer_instance)

/-- A morphism of the inserter lies in the left class of `insOFS` iff its base lies in `S.E`. -/
@[simp] lemma insOFS_E (hF) (hG) {x y : Ins F G} (f : x ⟶ y) :
    (insOFS S T hF hG).E f ↔ S.E f.base := Iff.rfl

/-- A morphism of the inserter lies in the right class of `insOFS` iff its base lies in `S.M`. -/
@[simp] lemma insOFS_M (hF) (hG) {x y : Ins F G} (f : x ⟶ y) :
    (insOFS S T hF hG).M f ↔ S.M f.base := Iff.rfl

end Ins

/-! ## Equifiers -/

section Equif

variable {F G : C ⥤ D} {η θ : F ⟶ G} (S : OFS C) (T : OFS D)

/-- The orthogonal factorization system lifted to an equifier: Theorem 6.3 (3). -/
def equifOFS (hF : ∀ ⦃x y : C⦄ (e : x ⟶ y), S.E e → T.E (F.map e))
    (hG : ∀ ⦃x y : C⦄ (m : x ⟶ y), S.M m → T.M (G.map m)) : OFS (Equif η θ) :=
  OFS.mk' (S.E.inverseImage (Equif.forget η θ)) (S.M.inverseImage (Equif.forget η θ))
    (by
      rintro x z f
      obtain ⟨y, e, m, he, hm, hfac⟩ := S.fact f.hom
      have hx : η.app x.obj = θ.app x.obj := x.property
      have hz : η.app z.obj = θ.app z.obj := z.property
      have hsq : (η.app x.obj ≫ G.map e) ≫ G.map m = F.map e ≫ (F.map m ≫ η.app z.obj) := by
        rw [Category.assoc, ← G.map_comp, hfac, ← Category.assoc, ← F.map_comp, hfac,
          η.naturality]
      obtain ⟨_, _, huniq⟩ := T.orth (hF e he) (hG m hm) _ _ hsq
      have hy : η.app y = θ.app y := by
        rw [huniq (η.app y) ⟨η.naturality e, (η.naturality m).symm⟩,
          huniq (θ.app y) ⟨by rw [hx]; exact θ.naturality e,
            by rw [hz]; exact (θ.naturality m).symm⟩]
      refine ⟨⟨y, hy⟩, ObjectProperty.homMk e, ObjectProperty.homMk m, he, hm, ?_⟩
      ext
      simpa using hfac)
    (by
      rintro x v y w e m he hm f g hsq
      have hb : f.hom ≫ m.hom = e.hom ≫ g.hom := (Equif.forget η θ).congr_map hsq
      obtain ⟨δ, ⟨hδ₁, hδ₂⟩, hδuniq⟩ := S.orth he hm f.hom g.hom hb
      have hδ₁' : e.hom ≫ δ = f.hom := hδ₁
      have hδ₂' : δ ≫ m.hom = g.hom := hδ₂
      refine ⟨ObjectProperty.homMk δ, ⟨?_, ?_⟩, ?_⟩
      · ext; simpa using hδ₁'
      · ext; simpa using hδ₂'
      rintro k ⟨k1, k2⟩
      have k1' : e.hom ≫ k.hom = f.hom := (Equif.forget η θ).congr_map k1
      have k2' : k.hom ≫ m.hom = g.hom := (Equif.forget η θ).congr_map k2
      ext
      simpa using hδuniq k.hom ⟨k1', k2'⟩)
    (by
      have := S.e_isStableUnderRetracts
      infer_instance)
    (by
      have := S.m_isStableUnderRetracts
      infer_instance)

/-- A morphism of the equifier lies in the left class of `equifOFS` iff `f.hom` lies in `S.E`. -/
@[simp] lemma equifOFS_E (hF) (hG) {x y : Equif η θ} (f : x ⟶ y) :
    (equifOFS S T hF hG).E f ↔ S.E f.hom := Iff.rfl

/-- A morphism of the equifier lies in the right class of `equifOFS` iff `f.hom` lies in `S.M`. -/
@[simp] lemma equifOFS_M (hF) (hG) {x y : Equif η θ} (f : x ⟶ y) :
    (equifOFS S T hF hG).M f ↔ S.M f.hom := Iff.rfl

end Equif

end UlmerBialgebras
