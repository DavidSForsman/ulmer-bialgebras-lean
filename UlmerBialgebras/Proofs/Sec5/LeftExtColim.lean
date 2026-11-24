module

public import UlmerBialgebras.Monadicity.BigMonadicity
public import UlmerBialgebras.Kan.Kan
public import UlmerBialgebras.Monadicity.HomCatComp
public import UlmerBialgebras.Paper.Sec5DefsKanIns

/-!
# Colimits in categories of left extensions, and the pushout step as a relative left adjoint

In a 2-category, let `k : I ⟶ X` and `e : I ⟶ c`.

* Connected colimits in `LeftExt k e` are created by the forgetful functor to `K(X, c)`
  (`UlmerBialgebras.Paper.AbsKan.hasColimit_of_isConnected`, `isColimitOfForget`); post-composition
  with `f` preserves those that `K(X, f)` preserves (`push_preservesColimit`,
  `push_preservesColimitsOfShape`).
* For `f : c ⟶ c`, `A : I ⟶ c`, a 2-cell `ψ : A f ⟶ A`, and initial extensions `e₀` of `A`
  and `p` of `A f`, the pushout step `x ↦ e₀ ⊔_p x f` (`UlmerBialgebras.LeftExt.pushoutStep`,
  `UlmerBialgebras/Paper/Sec5DefsKanIns.lean`) is a `push f`-relative left adjoint of the pullback
  `ψ^* = LeftExt.pull k ψ` along `ψ` (`stepRel`). This is the step of the transfinite
  construction in Lemma 5.6.

## Main results

* `UlmerBialgebras.Paper.AbsKan.hasColimit_of_isConnected`: a connected diagram in `LeftExt k e` has
  a colimit when its underlying diagram in `K(X, c)` has one.
* `UlmerBialgebras.Paper.AbsKan.isColimitOfForget`: a cocone of left extensions over a nonempty
  shape whose underlying cocone is a colimit is a colimit.
* `UlmerBialgebras.Paper.AbsKan.push_preservesColimitsOfShape`: post-composition with `f` preserves
  colimits of a connected shape `J` when `K(X, c)` has them and `K(X, f)` preserves them.
* `UlmerBialgebras.Paper.AbsKan.stepRel`: the pushout step is a `push f`-relative left adjoint of
  `ψ^*`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 5.6
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w u v

namespace UlmerBialgebras.Paper.AbsKan

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] {I X c : Obj} (k : I ⟶ X)

section Colim

variable {e : I ⟶ c} {J : Type*} [Category J] (W : J ⥤ LeftExt k e)

/-- A cocone of left extensions over a nonempty shape whose underlying cocone is a colimit is
a colimit. -/
def isColimitOfForget [Nonempty J] (cc : Cocone W)
    (hc : IsColimit ((LeftExt.forget k e).mapCocone cc)) : IsColimit cc where
  desc s := LeftExt.homMk (hc.desc ((LeftExt.forget k e).mapCocone s))
      (by
    let j₀ := Classical.arbitrary J
    -- the underlying cocones, typed by the extending 1-cells
    let D : cc.pt.ext ⟶ s.pt.ext := hc.desc ((LeftExt.forget k e).mapCocone s)
    have h1 : (W.obj j₀).unit ≫ k ◁ (LeftExt.homCell (cc.ι.app j₀)) = cc.pt.unit :=
        (LeftExt.w (cc.ι.app j₀))
    have h2 : (W.obj j₀).unit ≫ k ◁ (LeftExt.homCell (s.ι.app j₀)) = s.pt.unit :=
        (LeftExt.w (s.ι.app j₀))
    have h3 : (LeftExt.homCell (cc.ι.app j₀)) ≫ D = (LeftExt.homCell (s.ι.app j₀)) :=
      hc.fac ((LeftExt.forget k e).mapCocone s) j₀
    -- write `cc.pt.unit` through `j₀` by `h1`, then compose the coprojections by `h3`
    exact (eq_whisker h1 (k ◁ D)).symm.trans ((Category.assoc _ _ _).trans
      ((whisker_eq _ (Bicategory.whiskerLeft_comp _ _ _).symm).trans
        ((whisker_eq _ congr(k ◁ $h3)).trans h2))))
  fac s j := LeftExt.hom_ext (hc.fac ((LeftExt.forget k e).mapCocone s) j)
  uniq s m hm := LeftExt.hom_ext (hc.uniq ((LeftExt.forget k e).mapCocone s) (LeftExt.homCell m)
    (fun j => congr(LeftExt.homCell $(hm j))))

/-- For a connected diagram `W` of left extensions `(gⱼ, ηⱼ : e ⟶ k ≫ gⱼ)`, the composite
    `ηⱼ ≫ k ◁ ιⱼ` into `k ≫ colim gⱼ` does not depend on `j`. -/
lemma unit_const [IsConnected J] [HasColimit (W ⋙ LeftExt.forget k e)] (j j' : J) :
    (W.obj j).unit ≫ k ◁ colimit.ι (W ⋙ LeftExt.forget k e) j =
      (W.obj j').unit ≫ k ◁ colimit.ι (W ⋙ LeftExt.forget k e) j' :=
  constant_of_preserves_morphisms
    (fun j => (W.obj j).unit ≫ k ◁ colimit.ι (W ⋙ LeftExt.forget k e) j) (fun j₁ j₂ f => by
      -- the coprojections, typed by the extending 1-cells
      let ι' : ∀ j, (W.obj j).ext ⟶ colimit (W ⋙ LeftExt.forget k e) :=
        colimit.ι (W ⋙ LeftExt.forget k e)
      have hw : (LeftExt.homCell (W.map f)) ≫ ι' j₂ = ι' j₁ := colimit.w (W ⋙ LeftExt.forget k e) f
      have hf : (W.obj j₁).unit ≫ k ◁ (LeftExt.homCell (W.map f)) = (W.obj j₂).unit :=
          (LeftExt.w (W.map f))
      -- rewrite `ι' j₁` as `W.map f ≫ ι' j₂` and absorb `W.map f` into the unit
      exact (whisker_eq _ (congr(k ◁ $hw).symm.trans (Bicategory.whiskerLeft_comp _ _ _))).trans
        ((Category.assoc _ _ _).symm.trans (eq_whisker hf _))) j j'

/-- The colimit cocone of a connected diagram of left extensions. -/
noncomputable def colimCocone [IsConnected J] [HasColimit (W ⋙ LeftExt.forget k e)] :
    Cocone W where
  pt := LeftExt.mk (colimit (W ⋙ LeftExt.forget k e))
      ((W.obj (Classical.arbitrary J)).unit ≫
      k ◁ colimit.ι (W ⋙ LeftExt.forget k e) (Classical.arbitrary J))
  ι :=
    { app := fun j => LeftExt.homMk (colimit.ι (W ⋙ LeftExt.forget k e) j)
        ((unit_const k W j (Classical.arbitrary J) :))
      naturality := fun _ _ f => LeftExt.hom_ext
        ((colimit.w (W ⋙ LeftExt.forget k e) f).trans (Category.comp_id _).symm) }

/-- A connected diagram `W` in `LeftExt k e` has a colimit when the underlying diagram in
    `K(X, c)` has one; its unit is the common value of `ηⱼ ≫ k ◁ ιⱼ`. -/
theorem hasColimit_of_isConnected [IsConnected J] [HasColimit (W ⋙ LeftExt.forget k e)] :
    HasColimit W :=
  ⟨⟨⟨colimCocone k W, isColimitOfForget k W _ (colimit.isColimit (W ⋙ LeftExt.forget k e))⟩⟩⟩

/-- The forgetful functor `LeftExt k e ⥤ K(X, c)` preserves connected colimits that exist
    in `K(X, c)`. -/
theorem forget_preservesColimit [IsConnected J] [HasColimit (W ⋙ LeftExt.forget k e)] :
    PreservesColimit W (LeftExt.forget k e) :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitOfForget k W (colimCocone k W) (colimit.isColimit (W ⋙ LeftExt.forget k e)))
    (colimit.isColimit (W ⋙ LeftExt.forget k e))

/-- If `K(X, c)` has colimits of a connected shape `J`, so does `LeftExt k e`. -/
theorem hasColimitsOfShape_of_isConnected (J : Type*) [Category J] [IsConnected J]
    [HasColimitsOfShape J (X ⟶ c)] : HasColimitsOfShape J (LeftExt k e) :=
  ⟨fun W => hasColimit_of_isConnected k W⟩

/-- Post-composition with `f` preserves a connected colimit of left extensions whose underlying
colimit exists and is preserved by `K(X, f)`. -/
theorem push_preservesColimit {c' : Obj} (f : c ⟶ c') [IsConnected J]
    [HasColimit (W ⋙ LeftExt.forget k e)]
    [PreservesColimit (W ⋙ LeftExt.forget k e) (postcomp X f)] :
    PreservesColimit W (LeftExt.push k e f) := by
  have := forget_preservesColimit k W
  constructor
  intro cc hc
  have h1 : IsColimit ((LeftExt.forget k e).mapCocone cc) := isColimitOfPreserves _ hc
  have h2 : IsColimit ((postcomp X f).mapCocone ((LeftExt.forget k e).mapCocone cc)) :=
    isColimitOfPreserves _ h1
  exact ⟨isColimitOfForget k (W ⋙ LeftExt.push k e f) _ h2⟩

/-- Post-composition `LeftExt k e ⥤ LeftExt k (e ≫ f)` with `f` preserves colimits of a
    connected shape `J` when `K(X, c)` has them and `K(X, f)` preserves them. -/
theorem push_preservesColimitsOfShape {c' : Obj} (f : c ⟶ c') (J : Type*) [Category J]
    [IsConnected J] [HasColimitsOfShape J (X ⟶ c)] [PreservesColimitsOfShape J (postcomp X f)] :
    PreservesColimitsOfShape J (LeftExt.push k e f) :=
  ⟨fun {W} => push_preservesColimit k W f⟩

end Colim

section Step

variable {f : c ⟶ c} {A : I ⟶ c} (ψ : A ≫ f ⟶ A)
  (e₀ : LeftExt k A) (he : IsInitial e₀) {p : LeftExt k (A ≫ f)} (hp : IsInitial p)
  [HasPushouts (X ⟶ c)]

/-- For a morphism `h` out of the pushout step of `x` into `y`, the unit of `e₀` followed by
    `k ◁ (inl ≫ h)` is the unit of `y`. -/
lemma step_unit_comp {x y : LeftExt k A} (h : (LeftExt.pushoutStep k ψ e₀ hp).obj x ⟶ y) :
    e₀.unit ≫ k ◁ (pushout.inl _ _ ≫ (LeftExt.homCell h)) = y.unit :=
  -- the unit of the pushout step is `e₀.unit ≫ k ◁ pushout.inl _ _`
  (whisker_eq _ (Bicategory.whiskerLeft_comp _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans (LeftExt.w h))

/-- The pushout step is a `push f`-relative left adjoint of `ψ^*`. -/
noncomputable def stepRel :
    RelLeftAdjoint (LeftExt.push k A f) (LeftExt.pull k ψ) (LeftExt.pushoutStep k ψ e₀ hp) where
  homEquiv x y :=
    { toFun := fun h => LeftExt.homMk (pushout.inr _ _ ≫ (LeftExt.homCell h))
        (by
        -- the legs of the pushout and `h`, typed by the extending 1-cells
        let a : p.ext ⟶ e₀.ext := (LeftExt.homCell (hp.to ((LeftExt.pull k ψ).obj e₀)))
        let b : p.ext ⟶ x.ext ≫ f := (LeftExt.homCell (hp.to ((LeftExt.push k A f).obj x)))
        let h₁ : pushout a b ⟶ y.ext := (LeftExt.homCell h)
        have hb : p.unit ≫ k ◁ a = ψ ≫ e₀.unit := (LeftExt.w (hp.to ((LeftExt.pull k ψ).obj e₀)))
        have ha : p.unit ≫ k ◁ b = ((LeftExt.push k A f).obj x).unit :=
          (LeftExt.w (hp.to ((LeftExt.push k A f).obj x)))
        have hs : e₀.unit ≫ k ◁ (pushout.inl a b ≫ h₁) = y.unit := step_unit_comp k ψ e₀ hp h
        have key : p.unit ≫ k ◁ (b ≫ pushout.inr a b ≫ h₁) = ψ ≫ y.unit := by
          rw [← pushout.condition_assoc, Bicategory.whiskerLeft_comp, ← Category.assoc, hb,
            Category.assoc, hs]
        refine (eq_whisker ha.symm _).trans ?_
        exact (Category.assoc _ _ _).trans
          ((whisker_eq _ (Bicategory.whiskerLeft_comp _ _ _).symm).trans key))
      invFun :=
          fun g => LeftExt.homMk (pushout.desc (LeftExt.homCell (he.to y)) (LeftExt.homCell g) (by
          have h := congr(LeftExt.homCell $(hp.hom_ext (hp.to ((LeftExt.pull k ψ).obj e₀) ≫
            (LeftExt.pull k ψ).map (he.to y)) (hp.to ((LeftExt.push k A f).obj x) ≫ g)))
          exact h))
          (by
        let a : p.ext ⟶ e₀.ext := (LeftExt.homCell (hp.to ((LeftExt.pull k ψ).obj e₀)))
        let b : p.ext ⟶ x.ext ≫ f := (LeftExt.homCell (hp.to ((LeftExt.push k A f).obj x)))
        let t : e₀.ext ⟶ y.ext := (LeftExt.homCell (he.to y))
        let g₁ : x.ext ≫ f ⟶ y.ext := (LeftExt.homCell g)
        have ht : e₀.unit ≫ k ◁ t = y.unit := (LeftExt.w (he.to y))
        have hw : a ≫ t = b ≫ g₁ := congr(LeftExt.homCell $(hp.hom_ext
          (hp.to ((LeftExt.pull k ψ).obj e₀) ≫ (LeftExt.pull k ψ).map (he.to y))
          (hp.to ((LeftExt.push k A f).obj x) ≫ g)))
        change (e₀.unit ≫ k ◁ pushout.inl a b) ≫ k ◁ pushout.desc t g₁ hw = y.unit
        rw [Category.assoc, ← Bicategory.whiskerLeft_comp, pushout.inl_desc]
        exact ht)
      left_inv := fun h => LeftExt.hom_ext (by
        apply pushout.hom_ext
        · refine (pushout.inl_desc _ _ _).trans ?_
          let i : e₀ ⟶ (LeftExt.pushoutStep k ψ e₀ hp).obj x :=
            LeftExt.homMk (pushout.inl _ _) rfl
          exact congr(LeftExt.homCell $(he.hom_ext (i ≫ h) (he.to y))).symm
        · exact pushout.inr_desc _ _ _)
      right_inv := fun g => LeftExt.hom_ext (pushout.inr_desc _ _ _) }
  homEquiv_naturality_left g h := LeftExt.hom_ext (by
    exact (pushout.inr_desc_assoc _ _ _ _).trans (Category.assoc _ _ _))
  homEquiv_naturality_right g h := LeftExt.hom_ext (Category.assoc _ _ _).symm

end Step

end UlmerBialgebras.Paper.AbsKan
