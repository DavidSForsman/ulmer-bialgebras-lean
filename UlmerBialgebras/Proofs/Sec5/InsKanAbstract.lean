module

public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import UlmerBialgebras.Proofs.Sec5.LeftExtColim
public import UlmerBialgebras.Proofs.Sec5.ChainCofinality

/-!
# Left Kan extensions into an abstract inserter `Ins(f, id)` (Lemma 5.6)

Let `N` be an inserter of `f : c ⟶ c` and `𝟙 c` in a 2-category, `d : I ⟶ N.pt` and
`k : I ⟶ X`; write `A = d u`. Extensions of `d` along `k` are equivalent, over
`u_* : LE(d, k) → LE(A, k)`, to the concrete inserter of `push f, ψ^* : LE(A, k) ⥤ LE(A f, k)`,
where `ψ = d ◁ φ : A f ⟶ A` (`UlmerBialgebras.Paper.AbsKan.toIns`). The pushout step is a
`push f`-relative left adjoint of `ψ^*` (`UlmerBialgebras/Proofs/Sec5/LeftExtColim.lean`), so the
development's
`Ins.forget_isRightAdjoint_of_rel` gives the left adjoint of `u_*`, and with it the left Kan
extension of `d`.

## Main results

* `UlmerBialgebras.Paper.AbsKan.toIns`: the functor `LE(d, k) ⥤ Ins(push f, ψ^*)`.
* `UlmerBialgebras.Paper.AbsKan.isRightAdjoint_push_and_exists_initial_leftExt`: Lemma 5.6, under
  its hypotheses `u_*` has a left adjoint and `d` has a left Kan extension along `k`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.6 (with Lemma 4.6 (2) and Theorem 5.5 (1))
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w u v

namespace UlmerBialgebras.Paper.AbsKan

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

section Coherence

variable {c : Obj} {f : c ⟶ c} (N : Inserter f (𝟙 c))

/-- The inserter 2-cell at `k ≫ m` is `k` whiskered with the inserter 2-cell at `m`, up to
associators. -/
lemma phiAt_comp {I X : Obj} (k : I ⟶ X) (m : X ⟶ N.pt) :
    N.phiAt (k ≫ m) = eqToHom (by simp only [Category.assoc]) ≫ k ◁ N.phiAt m ≫
      eqToHom (by simp only [Category.assoc]) := by
  simp only [Inserter.phiAt, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
    Category.assoc,
    Bicategory.Strict.comp_whiskerLeft k m N.φ, eqToHom_trans, eqToHom_trans_assoc]

/-- The structure 2-cell `m u f ⟶ m u` of a 1-cell `m` into the inserter, `Inserter.phiAtId`. -/
abbrev σ {X : Obj} (m : X ⟶ N.pt) : (m ≫ N.u) ≫ f ⟶ m ≫ N.u := N.phiAtId m

/-- `σ (k ≫ m)` is `k ◁ σ m`, up to associators. -/
lemma σ_comp {I X : Obj} (k : I ⟶ X) (m : X ⟶ N.pt) :
    σ N (k ≫ m) = eqToHom (by simp only [Category.assoc]) ≫ k ◁ σ N m ≫
      eqToHom (by simp only [Category.assoc]) := by
  simp only [σ, Inserter.phiAtId, phiAt_comp, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans]

/-- `σ` is natural: for `α : m₁ ⟶ m₂`, `σ m₁ ≫ (α ▷ u) = ((α ▷ u) ▷ f) ≫ σ m₂`. -/
lemma σ_square {X : Obj} {m₁ m₂ : X ⟶ N.pt} (α : m₁ ⟶ m₂) :
    σ N m₁ ≫ (α ▷ N.u) = ((α ▷ N.u) ▷ f) ≫ σ N m₂ := by
  have h := N.phiAt_square α
  rw [Bicategory.Strict.whiskerRight_id] at h
  simp only [σ, Inserter.phiAtId, Category.assoc]
  rw [← reassoc_of% h]
  simp

end Coherence

/-- The morphism of left extensions `f_* L ⟶ ψ^* L` given by a 2-cell `σ : l f ⟹ l`, with the
compatibility stated on the unit of `L` itself (the units of `f_* L` and `ψ^* L` are unfolded). -/
abbrev pushPullHomMk {I X c : Obj} (k : I ⟶ X) {e : I ⟶ c} {f : c ⟶ c} (ψ : e ≫ f ⟶ e)
    (L : LeftExt k e) (σ : L.ext ≫ f ⟶ L.ext)
    (w : (L.unit ▷ f ≫ eqToHom (Category.assoc k L.ext f)) ≫ k ◁ σ = ψ ≫ L.unit) :
    (LeftExt.push k e f).obj L ⟶ (LeftExt.pull k ψ).obj L :=
  LeftExt.homMk σ w

section Main

variable {c : Obj} {f : c ⟶ c} (N : Inserter f (𝟙 c)) {I X : Obj} (k : I ⟶ X)
  (d : I ⟶ N.pt)

/-- The 2-cell `ψ = σ d : A f ⟶ A`, `A = d u`. -/
abbrev ψ : (d ≫ N.u) ≫ f ⟶ d ≫ N.u := σ N d

/-- The cell of the extension `u_* L`. -/
def cellOf (L : LeftExt k d) :
    (LeftExt.push k (d ≫ N.u) f).obj ((LeftExt.push k d N.u).obj L) ⟶
      (LeftExt.pull k (ψ N d)).obj ((LeftExt.push k d N.u).obj L) :=
  pushPullHomMk k (ψ N d) _ (σ N L.ext) (by
    rw [LeftExt.push_obj_unit]
    have h := σ_square N L.unit
    rw [σ_comp] at h
    simp only [Bicategory.comp_whiskerRight, Category.assoc] at h ⊢
    rw [reassoc_of% h]
    rw [Bicategory.eqToHom_whiskerRight, eqToHom_trans_assoc]
    simp)

/-- The 2-cell of `cellOf N k d L` is `σ N L.ext`. -/
@[simp] lemma homCell_cellOf (L : LeftExt k d) :
    LeftExt.homCell (cellOf N k d L) = σ N L.ext := rfl

/-- Extensions of `d` as objects of the concrete inserter. -/
@[simps]
def toIns : LeftExt k d ⥤ Ins (LeftExt.push k (d ≫ N.u) f) (LeftExt.pull k (ψ N d)) where
  obj L := ⟨(LeftExt.push k d N.u).obj L, cellOf N k d L⟩
  map α := ⟨(LeftExt.push k d N.u).map α,
    LeftExt.hom_ext (σ_square N (LeftExt.homCell α))⟩
  map_id L := Ins.hom_ext ((LeftExt.push k d N.u).map_id L)
  map_comp α β := Ins.hom_ext ((LeftExt.push k d N.u).map_comp α β)

/-- `toIns` followed by the forgetful functor of the concrete inserter is `u_*`. -/
lemma toIns_forget : toIns N k d ⋙ Ins.forget _ _ = LeftExt.push k d N.u := rfl

/-- `toIns : LE(d, k) ⥤ Ins(f_*, ψ^*)` is faithful. -/
instance : (toIns N k d).Faithful where
  map_injective {L L'} α β h := by
    have h' : LeftExt.homCell α ▷ N.u = LeftExt.homCell β ▷ N.u :=
      congrArg (fun t => LeftExt.homCell t.base) h
    exact LeftExt.hom_ext (N.faithful _ _ h')

/-- A 2-cell `α : m₁ u ⟶ m₂ u` compatible with `σ` satisfies the condition of the 2-dimensional
universal property of the inserter `N`. -/
lemma lift₂_cond {X' : Obj} {m₁ m₂ : X' ⟶ N.pt} (α : m₁ ≫ N.u ⟶ m₂ ≫ N.u)
    (H : σ N m₁ ≫ α = (α ▷ f) ≫ σ N m₂) :
    N.phiAt m₁ ≫ (α ▷ 𝟙 c) = (α ▷ f) ≫ N.phiAt m₂ := by
  rw [Bicategory.Strict.whiskerRight_id]
  simp only [σ, Inserter.phiAtId] at H
  rw [← cancel_mono (eqToHom (Category.comp_id (m₂ ≫ N.u)))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [← H]
  simp

/-- `toIns : LE(d, k) ⥤ Ins(f_*, ψ^*)` is full (by the 2-dimensional property of the inserter). -/
instance : (toIns N k d).Full where
  map_surjective {L L'} h := by
    have hw : σ N L.ext ≫ LeftExt.homCell h.base = (LeftExt.homCell h.base ▷ f) ≫ σ N L'.ext :=
      congr(LeftExt.homCell $(h.w))
    let β := N.lift₂' (LeftExt.homCell h.base) (lift₂_cond N (LeftExt.homCell h.base) hw)
    have hβ : β ▷ N.u = LeftExt.homCell h.base := N.lift₂'_u _ _
    refine ⟨LeftExt.homMk β (N.faithful _ _ ?_), ?_⟩
    · have h2 : (L.unit ▷ N.u ≫ eqToHom (Category.assoc k L.ext N.u)) ≫ k ◁ LeftExt.homCell h.base =
          L'.unit ▷ N.u ≫ eqToHom (Category.assoc k L'.ext N.u) := LeftExt.w h.base
      rw [Bicategory.comp_whiskerRight, Bicategory.Strict.whisker_assoc', hβ]
      rw [← cancel_mono (eqToHom (Category.assoc k L'.ext N.u))]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [← h2]
      simp only [Category.assoc]
      rfl
    · apply Ins.hom_ext
      exact LeftExt.hom_ext hβ

/-- A morphism of extensions is invertible as soon as its underlying 2-cell is. -/
lemma le_isIso {e : I ⟶ c} {L L' : LeftExt k e} (a : L ⟶ L') [IsIso (LeftExt.homCell a)] :
    IsIso a := by
  have w : L'.unit ≫ k ◁ inv (LeftExt.homCell a) = L.unit :=
    calc L'.unit ≫ k ◁ inv (LeftExt.homCell a)
        = (L.unit ≫ k ◁ LeftExt.homCell a) ≫ k ◁ inv (LeftExt.homCell a) := by rw [LeftExt.w a]
      _ = L.unit := by
        rw [Category.assoc, ← Bicategory.whiskerLeft_comp, IsIso.hom_inv_id,
          Bicategory.whiskerLeft_id, Category.comp_id]
  exact ⟨⟨LeftExt.homMk _ w, LeftExt.hom_ext (by simp), LeftExt.hom_ext (by simp)⟩⟩

/-- `toIns : LE(d, k) ⥤ Ins(f_*, ψ^*)` is essentially surjective: an object `((n, θ), γ)` lifts to
the extension `(lift n γ, lift₂ θ)`. -/
instance : (toIns N k d).EssSurj where
  mem_essImage Y := by
    obtain ⟨P, cell⟩ := Y
    obtain ⟨n, θ, rfl⟩ : ∃ n θ, P = LeftExt.mk n θ := ⟨P.ext, P.unit, (LeftExt.mk_eta P).symm⟩
    obtain ⟨γ, hγ, rfl⟩ : ∃ (γ : n ≫ f ⟶ n)
        (hγ : ((θ ▷ f) ≫ eqToHom (Category.assoc k n f)) ≫ k ◁ γ = ψ N d ≫ θ),
        cell = LeftExt.homMk γ hγ :=
      ⟨LeftExt.homCell cell, LeftExt.w cell, LeftExt.hom_ext (by simp)⟩
    let m : X ⟶ N.pt := N.lift n (γ ≫ eqToHom (Category.comp_id n).symm)
    have hm : m ≫ N.u = n := N.lift_u _ _
    have hφ : σ N m = eqToHom (by rw [hm]) ≫ γ ≫ eqToHom (by rw [hm]) := by
      have := N.lift_φ n (γ ≫ eqToHom (Category.comp_id n).symm)
      simp only [σ, Inserter.phiAtId, Inserter.phiAt]
      rw [this]
      simp
    let α : d ≫ N.u ⟶ (k ≫ m) ≫ N.u := θ ≫ eqToHom (by rw [Category.assoc, hm])
    have hα : N.phiAt d ≫ (α ▷ 𝟙 c) = (α ▷ f) ≫ N.phiAt (k ≫ m) := by
      refine lift₂_cond N α ?_
      rw [σ_comp, hφ]
      simp only [α, Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
        Bicategory.whiskerLeft_comp,
        Bicategory.whiskerLeft_eqToHom, Category.assoc]
      rw [← cancel_epi (eqToHom (show (d ≫ N.u) ≫ f = (d ≫ N.u) ≫ f from rfl))]
      have hγ' := hγ
      simp only [Category.assoc] at hγ'
      rw [← reassoc_of% hγ']
      simp
    let η : d ⟶ k ≫ m := N.lift₂ α hα
    have hη : η ▷ N.u = α := N.lift₂_u α hα
    let L₀ : LeftExt k d := LeftExt.mk m η
    let b : (LeftExt.push k d N.u).obj L₀ ⟶ LeftExt.mk n θ := LeftExt.homMk (eqToHom hm) (by
      simp only [LeftExt.push_obj_unit, L₀, LeftExt.mk_unit]
      rw [hη]
      simp [α])
    have : IsIso (LeftExt.homCell b) := (inferInstance : IsIso (eqToHom hm))
    have : IsIso b := le_isIso k b
    let hb : (toIns N k d).obj L₀ ⟶ ⟨LeftExt.mk n θ, LeftExt.homMk γ hγ⟩ := ⟨b, LeftExt.hom_ext (by
      change σ N m ≫ eqToHom hm = (eqToHom hm ▷ f) ≫ γ
      rw [hφ]
      simp)⟩
    have : IsIso ((Ins.forget _ _).map hb) := inferInstanceAs (IsIso b)
    have : IsIso hb := isIso_of_reflects_iso hb (Ins.forget _ _)
    exact ⟨L₀, ⟨asIso hb⟩⟩

/-- Lemma 4.6 (2) of [forsman2026syntactic] for `Ins(f, id)`: the comparison
`toIns : LE(d, k) ⥤ Ins(f_*, ψ^*)` is an equivalence. -/
instance : (toIns N k d).IsEquivalence where

end Main

/-- **Lemma 5.6** ([forsman2026syntactic]). -/
theorem isRightAdjoint_push_and_exists_initial_leftExt {c : Obj} (f : c ⟶ c)
    (N : Inserter f (𝟙 c)) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ N.pt) (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ)
    [HasPushouts (X ⟶ c)] (hch : HasChainColimitsUpTo κ (X ⟶ c))
    (hf : PreservesColimitsOfShape κ.ord.ToType (postcomp X f))
    (h1 : ∃ L : LeftExt k (d ≫ N.u), Nonempty (IsInitial L))
    (h2 : ∃ L : LeftExt k ((d ≫ N.u) ≫ f), Nonempty (IsInitial L)) :
    (LeftExt.push k d N.u).IsRightAdjoint ∧ ∃ L : LeftExt k d, Nonempty (IsInitial L) := by
  -- The step functor is a relative left adjoint; iterate it along the `κ`-chain.
  obtain ⟨e₀, ⟨he⟩⟩ := h1
  obtain ⟨p, ⟨hp⟩⟩ := h2
  let ra := stepRel k (ψ N d) e₀ he hp
  let := Kappa.orderBotOfPos hκ
  have : HasColimitsOfShape κ.ord.ToType (X ⟶ c) := hch κ hκ le_rfl
  have : IsConnected κ.ord.ToType := IsFiltered.isConnected _
  have := hf
  -- Pushing along `f` preserves the chain colimit, so the chain converges.
  have hF : PreservesColimitsOfShape (Kappa.shape κ) (LeftExt.push k (d ≫ N.u) f) :=
    push_preservesColimitsOfShape k f (Kappa.shape κ)
  have hchLE : HasChainColimitsLE κ (LeftExt k (d ≫ N.u)) := by
    intro J _ _ _ hJ
    have : HasColimitsOfShape J (X ⟶ c) := hasChainColimitsLE_of_upTo hch J hJ
    have : IsConnected J := IsFiltered.isConnected J
    exact hasColimitsOfShape_of_isConnected k J
  have : HasInitial (LeftExt k (d ≫ N.u)) := he.hasInitial
  have : HasPushouts (LeftExt k (d ≫ N.u)) := hasColimitsOfShape_of_isConnected k WalkingSpan
  have : HasBinaryCoproducts (LeftExt k (d ≫ N.u)) :=
    hasBinaryCoproducts_of_hasInitial_and_pushouts _
  have : HasFiniteCoproducts (LeftExt k (d ≫ N.u)) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  have : (Ins.forget (LeftExt.push k (d ≫ N.u) f) (LeftExt.pull k (ψ N d))).IsRightAdjoint :=
    Ins.forget_isRightAdjoint_of_rel hκ ra hchLE hF
  have hR : (LeftExt.push k d N.u).IsRightAdjoint := by
    rw [← toIns_forget N k d]
    infer_instance
  refine ⟨hR, ?_⟩
  let R := Ins.forget (LeftExt.push k (d ≫ N.u) f) (LeftExt.pull k (ψ N d))
  have := (Adjunction.ofIsRightAdjoint R).leftAdjoint_preservesColimits
  have h3 : IsInitial (R.leftAdjoint.obj e₀) := IsInitial.isInitialObj R.leftAdjoint e₀ he
  let E := (toIns N k d).asEquivalence
  exact ⟨E.inverse.obj (R.leftAdjoint.obj e₀), ⟨IsInitial.isInitialObj E.inverse _ h3⟩⟩

end UlmerBialgebras.Paper.AbsKan
