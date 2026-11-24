module

public import Foundations.CategoryTheory.Presentable.Collapsing
public import UlmerBialgebras.Monadicity.UnderPresentation

/-!
# Collapsing refinements in accessible categories with pushouts

The technical heart of the co-well-poweredness theorem.  Let `C` be a `κ`-accessible category
with pushouts, let `K` be `κ`-presentable and let `e : K ⟶ L` be an **epimorphism**.  Then every
factorization `K ⟶ P ⟶ L` of `e` through a `κ`-presentable object can be refined to a
factorization `K ⟶ P ⟶ R ⟶ L` in which `R` is `κ`-presentable and `P ⟶ R` is
*collapsing* (`UlmerBialgebras.Collapsing`): morphisms out of `R` prescribed on `K` are determined
after composition with `P ⟶ R`.

The proof is a colimit interchange.  Write `e` as a `κ`-filtered colimit of maps `a j : K ⟶ D j`
under `K` (`UlmerBialgebras.UnderPresentation`).  The cokernel pairs `D j ⊔_K D j` then form a
diagram whose colimit is the cokernel pair `L ⊔_K L` of `e`
(`UlmerBialgebras.UnderPresentation.sqIsColimit`).  Since `e` is an epimorphism the two
coprojections `L ⇉ L ⊔_K L` agree, so the two coprojections `D j ⇉ D j ⊔_K D j` agree in the
colimit; as `D j` is `κ`-presentable they agree at some later stage `m`, and that is exactly the
statement that the transition map `D j ⟶ D m` is collapsing.

## Main results

* `UlmerBialgebras.UnderPresentation.sqIsColimit`: the cokernel pair of `e` is the colimit of the
  cokernel pairs of the stages of a presentation of `e`.
* `UlmerBialgebras.UnderPresentation.exists_collapsing_map`: if `e` is an epimorphism, every stage
  `j` has a transition map `j ⟶ m` whose image under the diagram is `a j`-collapsing.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.10
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Theorem 1.58
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

noncomputable section

namespace UnderPresentation

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  {K L : C} {e : K ⟶ L} (p : UnderPresentation κ e) [HasPushouts C]

/-- The diagram of cokernel pairs `D j ⊔_K D j` of the structure maps of a presentation. -/
@[simps obj, implicit_reducible]
def sq : p.J ⥤ C where
  obj j := pushout (p.a j) (p.a j)
  map {i j} f := pushout.map _ _ _ _ (p.D.map f) (p.D.map f) (𝟙 K)
    (by simp [p.a_naturality f]) (by simp [p.a_naturality f])
  map_id j := by apply pushout.hom_ext <;> simp
  map_comp f g := by apply pushout.hom_ext <;> simp

/-- The left coprojection commutes with the transition maps: `inl ≫ sq.map f = D.map f ≫ inl`. -/
@[reassoc (attr := simp)]
lemma inl_sq_map {i j : p.J} (f : i ⟶ j) :
    pushout.inl (p.a i) (p.a i) ≫ p.sq.map f = p.D.map f ≫ pushout.inl (p.a j) (p.a j) := by
  simp [sq]

/-- The right coprojection commutes with the transition maps: `inr ≫ sq.map f = D.map f ≫ inr`. -/
@[reassoc (attr := simp)]
lemma inr_sq_map {i j : p.J} (f : i ⟶ j) :
    pushout.inr (p.a i) (p.a i) ≫ p.sq.map f = p.D.map f ≫ pushout.inr (p.a j) (p.a j) := by
  simp [sq]

/-- The comparison cocone from the diagram of cokernel pairs to the cokernel pair of `e`. -/
@[simps, implicit_reducible]
def sqCocone : Cocone p.sq where
  pt := pushout e e
  ι :=
    { app := fun j => pushout.map _ _ _ _ (p.proj j) (p.proj j) (𝟙 K)
        (by simp [p.fac j]) (by simp [p.fac j])
      naturality := fun i j f => by
        apply pushout.hom_ext <;> simp [sq, p.proj_naturality_assoc f] }

/-- The cocone leg at `j` sends the left coprojection of `D j ⊔_K D j` to `proj j ≫ inl`. -/
@[reassoc (attr := simp)]
lemma inl_sqCocone (j : p.J) :
    pushout.inl (p.a j) (p.a j) ≫ p.sqCocone.ι.app j = p.proj j ≫ pushout.inl e e := by
  simp [sqCocone]

/-- The cocone leg at `j` sends the right coprojection of `D j ⊔_K D j` to `proj j ≫ inr`. -/
@[reassoc (attr := simp)]
lemma inr_sqCocone (j : p.J) :
    pushout.inr (p.a j) (p.a j) ≫ p.sqCocone.ι.app j = p.proj j ≫ pushout.inr e e := by
  simp [sqCocone]

/-- The maps `inl ≫ s.ι.app j` out of the stages `D j` are compatible with the transition maps. -/
lemma sqDescLeft_compat (s : Cocone p.sq) : ∀ {i j : p.J} (f : i ⟶ j),
    p.D.map f ≫ (pushout.inl (p.a j) (p.a j) ≫ s.ι.app j)
      = pushout.inl (p.a i) (p.a i) ≫ s.ι.app i := by
  intro i j f
  rw [← Category.assoc, ← p.inl_sq_map f, Category.assoc, s.w f]

/-- The maps `inr ≫ s.ι.app j` out of the stages `D j` are compatible with the transition maps. -/
lemma sqDescRight_compat (s : Cocone p.sq) : ∀ {i j : p.J} (f : i ⟶ j),
    p.D.map f ≫ (pushout.inr (p.a j) (p.a j) ≫ s.ι.app j)
      = pushout.inr (p.a i) (p.a i) ≫ s.ι.app i := by
  intro i j f
  rw [← Category.assoc, ← p.inr_sq_map f, Category.assoc, s.w f]

/-- The left component of the descent morphism out of the cokernel pair of `e`. -/
def sqDescLeft (s : Cocone p.sq) : L ⟶ s.pt :=
  p.desc (fun j => pushout.inl (p.a j) (p.a j) ≫ s.ι.app j) (p.sqDescLeft_compat s)

/-- The right component of the descent morphism out of the cokernel pair of `e`. -/
def sqDescRight (s : Cocone p.sq) : L ⟶ s.pt :=
  p.desc (fun j => pushout.inr (p.a j) (p.a j) ≫ s.ι.app j) (p.sqDescRight_compat s)

/-- `proj j ≫ sqDescLeft s = inl ≫ s.ι.app j`. -/
@[reassoc (attr := simp)]
lemma proj_sqDescLeft (s : Cocone p.sq) (j : p.J) :
    p.proj j ≫ p.sqDescLeft s = pushout.inl (p.a j) (p.a j) ≫ s.ι.app j :=
  p.desc_fac _ (p.sqDescLeft_compat s) j

/-- `proj j ≫ sqDescRight s = inr ≫ s.ι.app j`. -/
@[reassoc (attr := simp)]
lemma proj_sqDescRight (s : Cocone p.sq) (j : p.J) :
    p.proj j ≫ p.sqDescRight s = pushout.inr (p.a j) (p.a j) ≫ s.ι.app j :=
  p.desc_fac _ (p.sqDescRight_compat s) j

/-- The two components agree after `e`: `e ≫ sqDescLeft s = e ≫ sqDescRight s`. -/
lemma sqDesc_condition (s : Cocone p.sq) : e ≫ p.sqDescLeft s = e ≫ p.sqDescRight s := by
  obtain ⟨j⟩ := p.ne
  have h := p.fac j
  calc e ≫ p.sqDescLeft s = (p.a j ≫ p.proj j) ≫ p.sqDescLeft s := by rw [h]
    _ = p.a j ≫ pushout.inl (p.a j) (p.a j) ≫ s.ι.app j := by
        rw [Category.assoc, p.proj_sqDescLeft]
    _ = p.a j ≫ pushout.inr (p.a j) (p.a j) ≫ s.ι.app j := by
        rw [← Category.assoc, ← Category.assoc, pushout.condition]
    _ = (p.a j ≫ p.proj j) ≫ p.sqDescRight s := by
        rw [Category.assoc, p.proj_sqDescRight]
    _ = e ≫ p.sqDescRight s := by rw [h]

/-- **The cokernel pair of `e` is the colimit of the cokernel pairs of the stages.** -/
def sqIsColimit : IsColimit p.sqCocone where
  desc s := pushout.desc (p.sqDescLeft s) (p.sqDescRight s) (p.sqDesc_condition s)
  fac s j := by
    apply pushout.hom_ext <;>
      simp
  uniq s m hm := by
    apply pushout.hom_ext <;> apply p.hom_ext <;> intro j
    · have h₁ : p.proj j ≫ pushout.inl e e ≫ m
          = pushout.inl (p.a j) (p.a j) ≫ p.sqCocone.ι.app j ≫ m := by
        rw [← Category.assoc, ← p.inl_sqCocone j, Category.assoc]
      rw [h₁, hm j, pushout.inl_desc, p.proj_sqDescLeft]
    · have h₁ : p.proj j ≫ pushout.inr e e ≫ m
          = pushout.inr (p.a j) (p.a j) ≫ p.sqCocone.ι.app j ≫ m := by
        rw [← Category.assoc, ← p.inr_sqCocone j, Category.assoc]
      rw [h₁, hm j, pushout.inr_desc, p.proj_sqDescRight]

/-- **Collapsing refinements exist along a presentation of an epimorphism.**  For each stage `j`
of a presentation of an epimorphism `e : K ⟶ L` there is a later stage `m` such that the
transition morphism `D j ⟶ D m` is `a j`-collapsing. -/
theorem exists_collapsing_map [Epi e] (j : p.J) :
    ∃ (m : p.J) (f : j ⟶ m), Collapsing (p.a j) (p.D.map f) := by
  have hepi : pushout.inl e e = pushout.inr e e := (cancel_epi e).1 pushout.condition
  have h : pushout.inl (p.a j) (p.a j) ≫ p.sqCocone.ι.app j
      = pushout.inr (p.a j) (p.a j) ≫ p.sqCocone.ι.app j := by
    rw [p.inl_sqCocone j, p.inr_sqCocone j, hepi]
  obtain ⟨m, f, hf⟩ := IsCardinalPresentable.exists_eq_of_isColimit' (X := p.D.obj j) κ
    p.sqIsColimit (pushout.inl (p.a j) (p.a j)) (pushout.inr (p.a j) (p.a j)) h
  refine ⟨m, f, collapsing_of_eq (p.a_naturality f) ?_⟩
  rw [← p.inl_sq_map f, ← p.inr_sq_map f]
  exact hf

end UnderPresentation

end

end UlmerBialgebras
