module

public import UlmerBialgebras.Proofs.Sec5.LaxNatLeftAdjoint
public import UlmerBialgebras.Proofs.Sec5.ExtrasDoctrinal
public import UlmerBialgebras.Proofs.Sec3.Sec3Ex
public import UlmerBialgebras.Models.CatPIE

/-!
# The compatible family of left adjoints, through `laxNat_adjunction`

The local data of Theorem 7.4 lifts to a lax transformation. This file shows how.

Take `g : d ⟶ c` such that every `K(x, g)`, `x ∈ A`, is a right adjoint, and the mates of the
left adjoints are invertible. Their invertibility is the paper's oplax-comparison hom-set
argument (`leftMateHomEquiv`, `leftMateHomEquiv_apply`): the right Kan extension in `d`, the
local adjunction at the codomain, preservation of the Kan extension, and the local adjunction
at the domain supply four bijections. Here cotensor universality is precisely the right Kan
extension universal property.
Then `laxNat_adjunction` (Houston, Proposition 2.35) lifts the adjunctions `L_x ⊣ K(x, g)` of
the local data to an adjunction `τ ⊣ K(−, g)` of lax transformations between the hom 2-functors
on `𝒜ᵒᵖ`. The coherence of `τ` is the pseudonaturality of the family `(L_x)`, which yields the
`ALeftAdjointFamily` of the proof of Theorem 7.4.

## Main results

* `UlmerBialgebras.Paper.nonempty_aLeftAdjointFamily`: under these hypotheses, the left adjoints
  form a compatible family of left adjoints.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.4
  and Example 3.12
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory Bicategory TwoFun

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
variable {A : ObjectProperty Obj} {c d : Obj} {g : d ⟶ c}

/-- The components of the inverse of an invertible 2-cell of `Cat` are the inverses of its
components. -/
lemma cat_inv_app {X Y : Cat.{w, v}} {F G : X ⟶ Y} (α : F ⟶ G) [IsIso α] (x : X) :
    (inv α).toNatTrans.app x ≫ α.toNatTrans.app x = 𝟙 _ :=
  congr(($(IsIso.inv_hom_id α)).toNatTrans.app x)

/-- The components of an invertible 2-cell of `Cat`, followed by those of its inverse. -/
lemma cat_hom_inv_app {X Y : Cat.{w, v}} {F G : X ⟶ Y} (α : F ⟶ G) [IsIso α] (x : X) :
    α.toNatTrans.app x ≫ (inv α).toNatTrans.app x = 𝟙 _ :=
  congr(($(IsIso.hom_inv_id α)).toNatTrans.app x)

/-- A 2-cell of `Cat` whose components are invertible is invertible. -/
lemma cat_isIso_of_app {X Y : Cat.{w, v}} {F G : X ⟶ Y} (α : F ⟶ G)
    (h : ∀ x, IsIso (α.toNatTrans.app x)) : IsIso α := by
  have : IsIso α.toNatTrans := NatIso.isIso_of_isIso_app _
  exact ⟨⟨⟨inv α.toNatTrans⟩, by ext x; simp, by ext x; simp⟩⟩

/-- A morphism with a left inverse `m` agrees with every right inverse of `m`. -/
lemma eq_of_left_inverse {C : Type*} [Category C] {X Y : C} {l r : X ⟶ Y} {m : Y ⟶ X}
    (h₁ : m ≫ l = 𝟙 Y) (h₂ : r ≫ m = 𝟙 X) : l = r := by
  calc l = (r ≫ m) ≫ l := by rw [h₂, Category.id_comp]
    _ = r := by rw [Category.assoc, h₁, Category.comp_id]

/-- **The composition law of a lax transformation into `Cat`, in components.** -/
lemma laxNat_nat_comp_app {B : Type*} [Bicategory B] [Bicategory.Strict B]
    {F G : StrictTwoFunctor Cat.{w, v} B} (τ : LaxNat F G) {a b c : B} (f : a ⟶ b) (f' : b ⟶ c)
    (k : F.obj a) :
    (τ.nat (f ≫ f')).toNatTrans.app k =
      eqToHom (by rw [G.map_comp]; rfl) ≫ (G.map f').toFunctor.map ((τ.nat f).toNatTrans.app k) ≫
        (τ.nat f').toNatTrans.app ((F.map f).toFunctor.obj k) ≫
          eqToHom (by rw [F.map_comp]; rfl) := by
  rw [τ.nat_comp]
  simp

/-- Composition coherence of `leftMateApp` deduced from the inverse lax natural
transformation `τ` of `postcompLaxNat A g`. -/
private lemma leftMateApp_comp_of_laxNat
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint)
    (nat : ∀ {a b : FullSubOp A} (f : a ⟶ b),
      homLeftAdj hrep a ≫ (homTwoFunctor A d).map f ⟶ (homTwoFunctor A c).map f ≫ homLeftAdj hrep b)
    (hinv : ∀ {x y : FullSubOp A} (f : x ⟶ y) (k : FullSubOp.pt x ⟶ c),
      (nat f).toNatTrans.app k ≫ leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k = 𝟙 _)
    (hinv₂ : ∀ {x y : FullSubOp A} (f : x ⟶ y) (k : FullSubOp.pt x ⟶ c),
      leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k ≫
          (nat f).toNatTrans.app k = 𝟙 _)
    {x y z : FullSubOp A} (f : x ⟶ y) (f' : y ⟶ z) (k : FullSubOp.pt x ⟶ c)
    (h₂ : (nat (f ≫ f')).toNatTrans.app k = eqToHom (Category.assoc _ _ _) ≫
      FullSubOp.hom f' ◁ (nat f).toNatTrans.app k ≫
        (nat f').toNatTrans.app (FullSubOp.hom f ≫ k) ≫
          eqToHom (congrArg (repLeftAdjoint hrep (FullSubOp.prop z)).obj
            (Category.assoc _ _ _).symm)) :
    leftMateApp (repLeftAdjunction hrep (FullSubOp.prop z))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f' ≫ FullSubOp.hom f) k =
      eqToHom (by simp only [Category.assoc]) ≫
        leftMateApp (repLeftAdjunction hrep (FullSubOp.prop z))
          (repLeftAdjunction hrep (FullSubOp.prop y)) (FullSubOp.hom f')
          (FullSubOp.hom f ≫ k) ≫
        (FullSubOp.hom f' ◁ leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
          (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k) ≫
        eqToHom (Category.assoc _ _ _).symm := by
  refine eq_of_left_inverse (hinv (f ≫ f') k) ?_
  rw [h₂]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hw : FullSubOp.hom f' ◁ leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
      (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k ≫
        FullSubOp.hom f' ◁ (nat f).toNatTrans.app k = 𝟙 _ :=
    (Bicategory.whiskerLeft_comp _ _ _).symm.trans
      (congr(FullSubOp.hom f' ◁ $(hinv₂ f k)).trans (Bicategory.whiskerLeft_id _ _))
  rw [reassoc_of% hw]
  exact (eqToHom _ ≫= ((_ ≫= Category.id_comp _).trans
    ((Category.assoc _ _ _).symm.trans
      ((hinv₂ f' (FullSubOp.hom f ≫ k) =≫ eqToHom _).trans
        (Category.id_comp _))))).trans ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- Identity coherence for `leftMateApp` deduced from a lax natural transformation. -/
private lemma leftMateApp_id_of_laxNat
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint)
    (nat : ∀ {a b : FullSubOp A} (f : a ⟶ b),
      homLeftAdj hrep a ≫ (homTwoFunctor A d).map f ⟶ (homTwoFunctor A c).map f ≫ homLeftAdj hrep b)
    (hinv : ∀ {x y : FullSubOp A} (f : x ⟶ y) (k : FullSubOp.pt x ⟶ c),
      (nat f).toNatTrans.app k ≫ leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k = 𝟙 _)
    (x : FullSubOp A) (k : FullSubOp.pt x ⟶ c)
    {p : homLeftAdj hrep x ≫ (homTwoFunctor A d).map (𝟙 x) =
      (homTwoFunctor A c).map (𝟙 x) ≫ homLeftAdj hrep x}
    (nat_id : nat (𝟙 x) = eqToHom p) :
    leftMateApp (repLeftAdjunction hrep (FullSubOp.prop x))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (𝟙 (FullSubOp.pt x)) k =
      eqToHom (by simp only [Category.id_comp]) := by
  have hX := congr(($nat_id).toNatTrans.app k).trans (Cat.eqToHom_app _ _ _ _)
  refine eq_of_left_inverse (hinv (𝟙 x) k) ?_
  exact (eqToHom _ ≫= hX).trans ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- **The local adjunctions lift to a compatible family of left adjoints**, through
`laxNat_adjunction`. -/
theorem nonempty_aLeftAdjointFamily
    (hrep : ∀ ⦃x : Obj⦄, A x → (postcomp x g).IsRightAdjoint) (hd : IsACotensored A d)
    (hg : RespectsACotensors A g) : Nonempty (ALeftAdjointFamily A g) := by
  -- The mates of the naturality cells of `postcompLaxNat` are invertible (`hd`, `hg`), so the
  -- lax adjunction gives a lax transformation `τ` of left adjoints with the inverse cells.
  have : ∀ {x y : FullSubOp A} (f : x ⟶ y), IsIso
      ((Bicategory.mateEquiv (homAdj hrep x) (homAdj hrep y)).symm
        ((postcompLaxNat A g).nat f)) := fun {x y} f =>
    cat_isIso_of_app _ fun k => (mate_postcompLaxNat_app hrep f k).symm ▸
      isIso_leftMateApp _ _ (FullSubOp.prop y) (FullSubOp.prop x) hd hg k
  obtain ⟨e, he, he', -⟩ := ex_3_12_lax (homTwoFunctor A d) (homTwoFunctor A c)
  obtain ⟨e', he₂, he₂', -⟩ := ex_3_12_lax (homTwoFunctor A c) (homTwoFunctor A d)
  obtain ⟨τ, happ, hnat, -⟩ :=
    laxNat_adjunction (postcompLaxNat A g) (homLeftAdj hrep) (homAdj hrep) e he he' e' he₂ he₂'
  revert happ hnat
  obtain ⟨app, nat, nat_cell, nat_comp, nat_id⟩ := τ
  intro happ hnat
  obtain rfl : app = homLeftAdj hrep := funext happ
  replace hnat : ∀ {x y : FullSubOp A} (f : x ⟶ y), nat f =
      inv ((Bicategory.mateEquiv (homAdj hrep x) (homAdj hrep y)).symm
        ((postcompLaxNat A g).nat f)) := fun f => eq_of_heq (hnat f)
  have hinv : ∀ {x y : FullSubOp A} (f : x ⟶ y) (k : FullSubOp.pt x ⟶ c),
      (nat f).toNatTrans.app k ≫ leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k = 𝟙 _ := fun f k => by
    have h := cat_inv_app ((Bicategory.mateEquiv (homAdj hrep _ ) (homAdj hrep _)).symm
      ((postcompLaxNat A g).nat f)) k
    rwa [← hnat, mate_postcompLaxNat_app] at h
  have hinv₂ : ∀ {x y : FullSubOp A} (f : x ⟶ y) (k : FullSubOp.pt x ⟶ c),
      leftMateApp (repLeftAdjunction hrep (FullSubOp.prop y))
        (repLeftAdjunction hrep (FullSubOp.prop x)) (FullSubOp.hom f) k ≫
          (nat f).toNatTrans.app k = 𝟙 _ := fun f k => by
    have h := cat_hom_inv_app ((Bicategory.mateEquiv (homAdj hrep _) (homAdj hrep _)).symm
      ((postcompLaxNat A g).nat f)) k
    rwa [← hnat, mate_postcompLaxNat_app] at h
  -- Read off the family: the left adjoints, their mate isomorphisms, and the coherence of `τ`.
  let pt : ∀ ⦃x : Obj⦄, A x → FullSubOp A := fun x hx => Opposite.op (show FullSub A from ⟨x, hx⟩)
  let op₁ : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y), (x ⟶ y) → (pt hy ⟶ pt hx) :=
    fun _ _ _ _ u => Quiver.Hom.op (InducedBicategory.mkHom u)
  exact ⟨{
    fn := repLeftAdjoint hrep
    nat := fun _ _ hx hy r => leftMateIso hrep hd hg hx hy r
    nat_id := fun x hx k => by
      rw [leftMateIso_hom_app]
      exact leftMateApp_id_of_laxNat hrep nat hinv (pt hx) k (nat_id (pt hx))
    nat_comp := fun x y z hx hy hz u v k => by
      rw [leftMateIso_hom_app, leftMateIso_hom_app, leftMateIso_hom_app]
      exact leftMateApp_comp_of_laxNat hrep nat hinv hinv₂ (op₁ hy hz v) (op₁ hx hy u) k
        (laxNat_nat_comp_app ⟨homLeftAdj hrep, nat, nat_cell, nat_comp, nat_id⟩
          (op₁ hy hz v) (op₁ hx hy u) k)
    adj := fun _ hx => repLeftAdjunction hrep hx
    unit_nat := fun x y hx hy u k => by
      rw [leftMateIso_hom_app]
      exact leftMateApp_unit (repLeftAdjunction hrep hx) (repLeftAdjunction hrep hy) k }⟩

end UlmerBialgebras.Paper
