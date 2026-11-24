module

public import UlmerBialgebras.Kan.Kan
public import UlmerBialgebras.Basic.HomCat

/-!
# Theorem 4.7 (2): lifting Kan extensions along an inserter

This file proves part (2) of Theorem 4.7 of *A Syntactic Approach to Ulmer's Bialgebras*:
the canonical 1-cell `u : Ins(f, g) → a` out of an inserter strictly creates those left Kan
extensions that `f` preserves.

The right Kan case is the left Kan case in `K^co` (`UlmerBialgebras/Kan/CoKan.lean`); it is derived
in
`UlmerBialgebras/Proofs/Sec4/Sec4.lean`.

## Main results

* `UlmerBialgebras.Inserter.strictlyCreates_leftKan`: the canonical 1-cell `u` out of an inserter
  strictly creates those left Kan extensions that `f` preserves (Theorem 4.7 (2)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.6 (2) and Theorem 4.7 (2)
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Inserter

variable {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {J X : Obj}

/-- The structure 2-cell of the inserter evaluated at a 1-cell `q` into the inserter. -/
def strCell (q : X ⟶ Ins.pt) : (q ≫ Ins.u) ≫ f ⟶ (q ≫ Ins.u) ≫ g := homCell Ins X q
/-- Unfolding of `strCell`: `q ◁ φ` conjugated by the associators. -/
lemma strCell_def (q : X ⟶ Ins.pt) : strCell Ins q
    = eqToHom (Category.assoc q Ins.u f) ≫ (q ◁ Ins.φ) ≫
      eqToHom (Category.assoc q Ins.u g).symm := rfl


/-- Naturality of the structure 2-cell (an instance of the interchange law). -/
lemma strCell_nat {q q' : X ⟶ Ins.pt} (α : q ⟶ q') :
    strCell Ins q ≫ ((α ▷ Ins.u) ▷ g) = ((α ▷ Ins.u) ▷ f) ≫ strCell Ins q' :=
  homCell_naturality Ins X α

/-- The structure 2-cell of the inserter at `q`, transported along `hp : q ≫ u = p`. -/
def transCell {q : X ⟶ Ins.pt} {p : X ⟶ a} (hp : q ≫ Ins.u = p) : p ≫ f ⟶ p ≫ g :=
  eqToHom (by rw [hp]) ≫ strCell Ins q ≫ eqToHom (by rw [hp])

/-- `transCell` along `rfl : q ≫ u = q ≫ u` is `strCell Ins q`. -/
@[simp] lemma transCell_rfl (q : X ⟶ Ins.pt) :
    transCell Ins (rfl : q ≫ Ins.u = q ≫ Ins.u) = strCell Ins q := by
  simp [transCell]

/-- `strCell` at `q` is `transCell` along `q ≫ u = p`, up to the induced `eqToHom`s. -/
lemma strCell_eq_transCell {q : X ⟶ Ins.pt} {p : X ⟶ a} (hp : q ≫ Ins.u = p) :
    strCell Ins q = eqToHom (by rw [hp]) ≫ transCell Ins hp ≫ eqToHom (by rw [hp]) := by
  subst hp; simp [transCell]

/-- The 2-cell used to induce a 1-cell into the inserter is recovered by `transCell`. -/
lemma transCell_lift (p : X ⟶ a) (α : p ≫ f ⟶ p ≫ g) :
    transCell Ins (Ins.lift_u p α) = α := by
  simp [transCell, strCell_def, Ins.lift_φ p α]

/-- The whiskering `q ◁ φ` is `transCell` along `hp : q ≫ u = p`, up to the induced
`eqToHom`s. -/
lemma phi_eq_transCell {q : X ⟶ Ins.pt} {p : X ⟶ a} (hp : q ≫ Ins.u = p) :
    q ◁ Ins.φ = eqToHom (by rw [← Category.assoc, hp]) ≫ transCell Ins hp
      ≫ eqToHom (by rw [← Category.assoc, hp]) := by
  subst hp
  simp [transCell, strCell_def]

/-- `strCell` at `k ≫ q` is `k ◁ strCell q`, up to associators. -/
lemma strCell_whiskerLeft (k : J ⟶ X) (q : X ⟶ Ins.pt) :
    strCell Ins (k ≫ q) = eqToHom (by simp only [Category.assoc]) ≫ (k ◁ strCell Ins q)
      ≫ eqToHom (by simp only [Category.assoc]) := by
  simp [strCell_def, Bicategory.Strict.comp_whiskerLeft k q Ins.φ]

section Left

variable (k : J ⟶ X) (d : J ⟶ Ins.pt)

/-- The left extension `g_*(l', ε') = (g l', (g ∗ ε') • (φ ∗ d))` of Lemma 4.6 (2), the
target of the universal 2-cell out of `f_*(l', ε')`; an extension of `(d ≫ u) ≫ f`
along `k`. -/
def kanTarget (L' : LeftExt k (d ≫ Ins.u)) : LeftExt k ((d ≫ Ins.u) ≫ f) :=
  LeftExt.mk (L'.ext ≫ g)
    (strCell Ins d ≫ (L'.unit ▷ g) ≫ eqToHom (Category.assoc k L'.ext g))

/-- The transported structure 2-cell of a lift is a morphism of left extensions
`f∗(l', ε') ⟶ (g l', (g ∗ ε') • (φ ∗ d))`. -/
lemma transCell_isHom (L : LeftExt k d) {L' : LeftExt k (d ≫ Ins.u)}
    (hL : (LeftExt.push k d Ins.u).obj L = L') (he : L.ext ≫ Ins.u = L'.ext) :
    ((LeftExt.push k (d ≫ Ins.u) f).obj L').unit ≫ (k ◁ transCell Ins he)
      = (kanTarget Ins k d L').unit := by
  subst hL
  simp only [kanTarget, transCell, LeftExt.push_obj_unit, LeftExt.push_obj_ext, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  simp only [LeftExt.mk_unit]
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc]
  conv_rhs =>
    rw [← Category.assoc (obj := _ ⟶ _), strCell_nat Ins L.unit, strCell_whiskerLeft]
  simp

/-- Post-composition with the inserter 1-cell `u`, `LeftExt.push k d Ins.u`, is faithful. -/
instance push_faithful : (LeftExt.push k d Ins.u).Faithful where
  map_injective h := LeftExt.hom_ext (Ins.lift₂_uniq _ _ (LeftExt.hom_ext_iff.mp h))

variable {L' : LeftExt k (d ≫ Ins.u)}

/-- The underlying 1-cell of any lift of `L'` along `u` is the one induced by the
universal 2-cell `f_*(l', ε') ⟶ g_*(l', ε')` (Lemma 4.6 (2)). -/
lemma ext_eq_lift (hFi : Limits.IsInitial ((LeftExt.push k (d ≫ Ins.u) f).obj L'))
    (L : LeftExt k d) (hL : (LeftExt.push k d Ins.u).obj L = L') :
    L.ext = Ins.lift L'.ext (LeftExt.homCell (hFi.to (kanTarget Ins k d L'))) := by
  have he : L.ext ≫ Ins.u = L'.ext := congr(LeftExt.ext $hL)
  have hcell0 : (LeftExt.homMk (transCell Ins he) (transCell_isHom Ins k d L hL he) :
      (LeftExt.push k (d ≫ Ins.u) f).obj L' ⟶ kanTarget Ins k d L')
        = hFi.to (kanTarget Ins k d L') := hFi.hom_ext _ _
  have hcell : transCell Ins he = LeftExt.homCell (hFi.to (kanTarget Ins k d L')) :=
    LeftExt.hom_ext_iff.mp hcell0
  refine Ins.lift_uniq L.ext L'.ext _ he ?_
  rw [← hcell]
  exact phi_eq_transCell Ins he

/-- A left extension of `d` along `k` has at most one lift along `u`. -/
lemma push_injective (hFi : Limits.IsInitial ((LeftExt.push k (d ≫ Ins.u) f).obj L'))
    {L₁ L₂ : LeftExt k d} (h₁ : (LeftExt.push k d Ins.u).obj L₁ = L')
    (h₂ : (LeftExt.push k d Ins.u).obj L₂ = L') : L₁ = L₂ := by
  have he : L₁.ext = L₂.ext :=
    (ext_eq_lift Ins k d hFi L₁ h₁).trans (ext_eq_lift Ins k d hFi L₂ h₂).symm
  refine LeftExt.eq_of_ext_eq he ?_
  refine Ins.lift₂_uniq _ _ ?_
  have h2 := LeftExt.unit_congr (h₁.trans h₂.symm)
  simp only [LeftExt.push_obj_unit, Category.assoc, eqToHom_trans] at h2
  rw [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  refine (cancel_mono (eqToHom (Category.assoc k L₂.ext Ins.u))).mp ?_
  simp only [Category.assoc, eqToHom_trans]
  exact h2

/-- Every left extension of `d ≫ u` along `k` whose image under `f` is initial lifts
along `u`. -/
lemma exists_lift (hFi : Limits.IsInitial ((LeftExt.push k (d ≫ Ins.u) f).obj L')) :
    ∃ L : LeftExt k d, (LeftExt.push k d Ins.u).obj L = L' := by
  set η : L'.ext ≫ f ⟶ L'.ext ≫ g := LeftExt.homCell (hFi.to (kanTarget Ins k d L')) with hη
  have hmor : ((L'.unit ▷ f) ≫ eqToHom (Category.assoc k L'.ext f)) ≫ (k ◁ η)
      = strCell Ins d ≫ (L'.unit ▷ g) ≫ eqToHom (Category.assoc k L'.ext g) :=
    LeftExt.w (hFi.to (kanTarget Ins k d L'))
  set l := Ins.lift L'.ext η with hl
  have hu : l ≫ Ins.u = L'.ext := Ins.lift_u L'.ext η
  have hstr : strCell Ins l = eqToHom (by rw [hu]) ≫ η ≫ eqToHom (by rw [hu]) := by
    rw [strCell_eq_transCell Ins hu, transCell_lift]
  have hmor' : (L'.unit ▷ f) ≫ eqToHom (Category.assoc k L'.ext f) ≫ (k ◁ η)
      = strCell Ins d ≫ (L'.unit ▷ g) ≫ eqToHom (Category.assoc k L'.ext g) := by
    rw [← hmor, Category.assoc (obj := _ ⟶ _)]
  have cond : strCell Ins d ≫ ((L'.unit ≫ eqToHom (by rw [Category.assoc, hu])) ▷ g)
      = ((L'.unit ≫ eqToHom (by rw [Category.assoc, hu])) ▷ f) ≫ strCell Ins (k ≫ l) := by
    rw [strCell_whiskerLeft, hstr]
    simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
      Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
      Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    slice_rhs 1 3 => rw [hmor']
    simp
  have cond' := by
    rw [strCell_def, strCell_def] at cond
    exact cond
  refine ⟨LeftExt.mk l (Ins.lift₂ _ cond'), ?_⟩
  refine LeftExt.eq_of_ext_eq hu ?_
  simp only [LeftExt.push_obj_unit]
  rw [LeftExt.mk_unit, Ins.lift₂_u]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The unit of `kanTarget Ins k d L'` is `strCell Ins d` followed by the unit of the push of
`L'` along `g`. -/
lemma kanTarget_unit (L' : LeftExt k (d ≫ Ins.u)) :
    (kanTarget Ins k d L').unit
      = strCell Ins d ≫ ((LeftExt.push k (d ≫ Ins.u) g).obj L').unit := rfl

/-- The structure 2-cell of the inserter at the underlying 1-cell of a left extension is a
morphism of left extensions. -/
lemma strCell_isHom (L : LeftExt k d) :
    ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L)).unit
        ≫ (k ◁ strCell Ins L.ext)
      = (kanTarget Ins k d ((LeftExt.push k d Ins.u).obj L)).unit := by
  have h := transCell_isHom Ins k d L rfl rfl
  rwa [transCell_rfl] at h

/-- At a left extension whose image under `f` is initial, post-composition with `u` is
full. -/
lemma push_full_of_initial (L T : LeftExt k d)
    (hFi : Limits.IsInitial
      ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L)))
    (β : (LeftExt.push k d Ins.u).obj L ⟶ (LeftExt.push k d Ins.u).obj T) :
    ∃ m : L ⟶ T, (LeftExt.push k d Ins.u).map m = β := by
  -- The two cells into `kanTarget` agree since the image of `L` is initial (`cond`); that is the
  -- inserter's condition, so `homCell β` lifts by `Ins.lift₂`, a morphism by `Ins.lift₂_uniq`.
  have hβf : ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L)).unit
      ≫ (k ◁ (LeftExt.homCell β ▷ f))
        = ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj T)).unit :=
    LeftExt.w ((LeftExt.push k (d ≫ Ins.u) f).map β)
  have hβg : ((LeftExt.push k (d ≫ Ins.u) g).obj ((LeftExt.push k d Ins.u).obj L)).unit
      ≫ (k ◁ (LeftExt.homCell β ▷ g))
        = ((LeftExt.push k (d ≫ Ins.u) g).obj ((LeftExt.push k d Ins.u).obj T)).unit :=
    LeftExt.w ((LeftExt.push k (d ≫ Ins.u) g).map β)
  have hA : ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L)).unit
      ≫ (k ◁ (strCell Ins L.ext ≫ (LeftExt.homCell β ▷ g)))
        = (kanTarget Ins k d ((LeftExt.push k d Ins.u).obj T)).unit := by
    simp only [Bicategory.whiskerLeft_comp]
    simpa only [Category.assoc, kanTarget_unit] using
      (strCell_isHom Ins k d L =≫ (k ◁ (LeftExt.homCell β ▷ g))).trans
        (by simpa only [Category.assoc, kanTarget_unit] using
          (strCell Ins d ≫= hβg))
  have hB : ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L)).unit
      ≫ (k ◁ ((LeftExt.homCell β ▷ f) ≫ strCell Ins T.ext))
        = (kanTarget Ins k d ((LeftExt.push k d Ins.u).obj T)).unit := by
    rw [Bicategory.whiskerLeft_comp, ← Category.assoc (obj := _ ⟶ _), hβf]
    exact strCell_isHom Ins k d T
  have hcell0 : (LeftExt.homMk (strCell Ins L.ext ≫ (LeftExt.homCell β ▷ g)) hA :
      (LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L)
        ⟶ kanTarget Ins k d ((LeftExt.push k d Ins.u).obj T))
      = LeftExt.homMk ((LeftExt.homCell β ▷ f) ≫ strCell Ins T.ext) hB := hFi.hom_ext _ _
  have cond : strCell Ins L.ext ≫ (LeftExt.homCell β ▷ g) =
      (LeftExt.homCell β ▷ f) ≫ strCell Ins T.ext :=
    LeftExt.hom_ext_iff.mp hcell0
  have hb : ((L.unit ▷ Ins.u) ≫ eqToHom (Category.assoc k L.ext Ins.u)) ≫ (k ◁ LeftExt.homCell β)
      = (T.unit ▷ Ins.u) ≫ eqToHom (Category.assoc k T.ext Ins.u) := LeftExt.w β
  have cond' := by
    rw [strCell_def, strCell_def] at cond
    exact cond
  refine ⟨LeftExt.homMk (Ins.lift₂ (LeftExt.homCell β) cond') ?_,
    LeftExt.hom_ext (Ins.lift₂_u _ _)⟩
  refine Ins.lift₂_uniq _ _ ?_
  rw [Bicategory.comp_whiskerRight, Bicategory.Strict.whisker_assoc', Ins.lift₂_u,
    ← Category.assoc (obj := _ ⟶ _),
    ← Category.assoc, hb]
  simp

/-- A left extension of `d` along `k` whose image under `u` is initial, and whose further
image under `f` is initial, is itself initial. -/
noncomputable def isInitialOfPush (L : LeftExt k d)
    (hinit : Limits.IsInitial ((LeftExt.push k d Ins.u).obj L))
    (hFi : Limits.IsInitial
      ((LeftExt.push k (d ≫ Ins.u) f).obj ((LeftExt.push k d Ins.u).obj L))) :
    Limits.IsInitial L :=
  Limits.IsInitial.ofUniqueHom
    (fun T => (push_full_of_initial Ins k d L T hFi (hinit.to _)).choose)
    (fun T _ => (LeftExt.push k d Ins.u).map_injective
      ((hinit.hom_ext _ _).trans
        (push_full_of_initial Ins k d L T hFi (hinit.to _)).choose_spec.symm))

/-- **Theorem 4.7 (2)** ([forsman2026syntactic]): the canonical 1-cell out of an inserter
strictly creates those left Kan extensions that `f` preserves. -/
theorem strictlyCreates_leftKan (hf : PreservesLeftKan k (d ≫ Ins.u) f) :
    StrictlyCreatesLeftKan k d Ins.u := by
  intro L₀ hL₀
  obtain ⟨hFi⟩ := hf L₀ hL₀
  obtain ⟨L, hL⟩ := exists_lift Ins k d hFi
  refine ⟨⟨L, hL, fun L₁ h => push_injective Ins k d hFi h hL⟩, ?_⟩
  intro L₁ h
  subst h
  obtain ⟨hi⟩ := hL₀
  exact ⟨isInitialOfPush Ins k d L₁ hi hFi⟩

end Left

end Inserter

end UlmerBialgebras
