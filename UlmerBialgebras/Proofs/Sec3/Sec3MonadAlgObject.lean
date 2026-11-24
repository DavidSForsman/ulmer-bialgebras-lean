module

public import UlmerBialgebras.Paper.Sec3DefsMonadAlgObject

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Remark 3.17: proofs

* `rem_3_17_exists`: the canonical algebra on `M^T` is universal
  (`Model.canonAlg_isUniversal`), so its comparison functors are isomorphisms of categories
  (`Model.algComparison_iso_iff`); they are natural (`Model.algComparison_natural`).
* `rem_3_17_unique`: the strict 2-categorical Yoneda argument, on objects and, by 2-naturality, on
  morphisms.
* `rem_3_17_em`: the `T_Lax`-algebras of the monad over `x` are the pairs `(h', ψ)` satisfying the
  algebra equations (`MndK.eqn_iff_isAlg`), and the paper's (1) and (2) are the universal property
  of `MndK.emAlg` (`Model.Alg.IsUniversalAt`).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- In a strict bicategory, `β ▷ 𝟙` is `β` up to the unitor identifications. -/
lemma conjEq_whiskerRight_id {a b : Obj} {f g : a ⟶ b} (β : f ⟶ g) : ConjEq (β ▷ 𝟙 b) β :=
  ⟨Category.comp_id f, (Category.comp_id g).symm, by
    rw [Bicategory.whiskerRight_id, Bicategory.Strict.rightUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso]
    simp⟩

/-- Functors preserve `ConjEq`. -/
lemma map_conjEq {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y X' Y' : C}
    {u : X ⟶ Y} {v : X' ⟶ Y'} (h : ConjEq u v) : ConjEq (F.map u) (F.map v) := by
  obtain ⟨p, q, rfl⟩ := h
  subst p q
  exact ConjEq.of_eq (by simp)

variable [HasChosenFinProducts.{u, v, w} Obj]

section General

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{w, v}] [HasChosenProductsOfSize.{s₂} Cat.{w, v}]
  [HasChosenInserters Cat.{w, v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{w, v}] [HasChosenEquifiers Cat.{w, v}]

/-- Remark 3.17, uniqueness: two objects `E`, `E'` representing the `T`-algebras in `M` via `Φ` and
`Φ'` are isomorphic, by an isomorphism compatible with `Φ` and `Φ'`. -/
theorem rem_3_17_unique {E E' : Obj} {Φ : ∀ x : Obj, Cat.of (x ⟶ E) ⟶ (M.homModel x).thyObj sg T}
    {Φ' : ∀ x : Obj, Cat.of (x ⟶ E') ⟶ (M.homModel x).thyObj sg T}
    (h : IsThyRep M sg T E Φ) (h' : IsThyRep M sg T E' Φ') :
    ∃ (i : E ⟶ E') (j : E' ⟶ E), i ≫ j = 𝟙 E ∧ j ≫ i = 𝟙 E' ∧
      ∀ x : Obj, (postcomp x i).toCatHom ≫ Φ' x = Φ x := by
  have nat : ∀ {D : Obj} {Ψ : ∀ x : Obj, Cat.of (x ⟶ D) ⟶ (M.homModel x).thyObj sg T},
      IsThyRep M sg T D Ψ → ∀ {x y : Obj} (k : x ⟶ y) (g : y ⟶ D),
        (Ψ x).toFunctor.obj (k ≫ g) =
          (M.homThyMap y sg T k).toFunctor.obj ((Ψ y).toFunctor.obj g) :=
    fun hΨ _ _ k g => congr(($(hΨ.2.1 k)).toFunctor.obj g)
  obtain ⟨i, hi⟩ := (h'.1 E).1.2 ((Φ E).toFunctor.obj (𝟙 E))
  obtain ⟨j, hj⟩ := (h.1 E').1.2 ((Φ' E').toFunctor.obj (𝟙 E'))
  have key : ∀ (x : Obj) (k : x ⟶ E), (Φ' x).toFunctor.obj (k ≫ i) = (Φ x).toFunctor.obj k :=
    fun x k => by rw [nat h' k i, hi, ← nat h k (𝟙 E), Category.comp_id]
  have key' : ∀ (x : Obj) (k : x ⟶ E'), (Φ x).toFunctor.obj (k ≫ j) = (Φ' x).toFunctor.obj k :=
    fun x k => by rw [nat h k j, hj, ← nat h' k (𝟙 E'), Category.comp_id]
  refine ⟨i, j, (h.1 E).1.1 ?_, (h'.1 E').1.1 ?_, fun x => ?_⟩
  · rw [key' E i]
    exact hi
  · rw [key E' j]
    exact hj
  -- On morphisms: both sides send `β : k ⇒ k'` to the component of `K(β, M)^T` at `Φ_E(𝟙_E)`.
  have happ : ∀ {k k' : x ⟶ E} (β : k ⟶ k') {y y' : (M.homModel E).thyObj sg T}, y = y' →
      ConjEq ((M.homThyMap₂ E sg T β).toNatTrans.app y)
        ((M.homThyMap₂ E sg T β).toNatTrans.app y') := by
    rintro _ _ β _ _ rfl
    exact ConjEq.of_eq rfl
  have hmap : ∀ {k k' : x ⟶ E} (β : k ⟶ k'),
      ConjEq ((Φ' x).toFunctor.map (β ▷ i)) ((Φ x).toFunctor.map β) := fun {k k'} β =>
    ((h'.2.2 β i).trans (happ β hi)).trans ((h.2.2 β (𝟙 E)).symm.trans
      (map_conjEq (Φ x).toFunctor (conjEq_whiskerRight_id β)))
  refine Cat.Hom.ext (CategoryTheory.Functor.ext (fun k => key x k) fun k k' β => ?_)
  obtain ⟨p, q, e⟩ := hmap β
  exact e

/-- Remark 3.17, existence: the object `M.thyObjOf sg P₀ Pfn I T Peq Q` built from products, an
inserter and an equifier represents the `T`-algebras in `M`, via the comparison functors of its
canonical algebra. -/
theorem rem_3_17_exists (P₀ : Product (fun s : sg.Srt => M.obj (sg.sty s)))
    (Pfn : Product (fun f : sg.Fn => M.obj (sg.fnty f)))
    (I : Inserter (M.domCellOf sg P₀ Pfn) (M.codCellOf sg P₀ Pfn))
    (Peq : Product (fun r : T.Eqn => M.obj (T.eqty r)))
    (Q : Equifier (M.lhsCellOf sg P₀ Pfn I T Peq) (M.rhsCellOf sg P₀ Pfn I T Peq)) :
    IsThyRep M sg T (M.thyObjOf sg P₀ Pfn I T Peq Q)
      (fun x => M.algComparison x sg T (M.canonAlg sg T P₀ Pfn I Peq Q)) :=
  ⟨fun x => (M.algComparison_iso_iff x sg T _).mpr
      (M.canonAlg_isUniversal sg T P₀ Pfn I Peq Q x),
    fun k => M.algComparison_natural _ sg T _ k,
    fun α a => M.algComparison_natural₂ _ sg T _ α a⟩

end General

section MonadAlgebras

open MndK SigEx

variable {c : Obj} {t : c ⟶ c} {m : t ≫ t ⟶ t} {e : 𝟙 c ⟶ t}

/-- Two `T_Lax`-algebras over `x` are equal if their carriers are equal and their algebra 2-cells
`psiAlg` are `ConjEq`. -/
lemma em_alg_ext {x : Obj} {B B' : (model t m e).Alg σL TL x} (he : B.env () = B'.env ())
    (hψ : ConjEq (psiAlg B.env B.cell) (psiAlg B'.env B'.cell)) : B = B' := by
  have he' : B.env = B'.env := funext fun s => by cases s; exact he
  refine Model.Alg.ext' he' fun f => ?_
  cases f
  exact (psi_conjEq B.env B.cell).trans (hψ.trans (psi_conjEq B'.env B'.cell).symm)

/-- The algebra 2-cell of `emAlg t m e u η hη` is `ConjEq` to `η`. -/
lemma psiAlg_emAlg {d : Obj} (u : d ⟶ c) (η : u ≫ t ⟶ u) (hη : IsAlg t m e u η) :
    ConjEq (psiAlg (emAlg t m e u η hη).env (emAlg t m e u η hη).cell) η :=
  ((ConjEq.of_eq (rfl : η = η)).eqToHom_comp _).eqToHom_comp _

/-- The algebra 2-cell of the precomposition of `A` with `h` is `ConjEq` to the whiskering by `h` of
the algebra 2-cell of `A`. -/
lemma psiAlg_precomp {d x : Obj} (A : (model t m e).Alg σL TL d) (h : x ⟶ d) :
    ConjEq (psiAlg (A.precomp h).env (A.precomp h).cell) (h ◁ psiAlg A.env A.cell) :=
  ((ConjEq.conj _ _ _).eqToHom_comp _).trans (ConjEq.whiskerLeft h (psi_conjEq A.env A.cell))

/-- The carrier and the algebra 2-cell of a `T_Lax`-algebra satisfy the algebra equations `IsAlg`.
-/
lemma isAlg_of_alg {x : Obj} (B : (model t m e).Alg σL TL x) :
    IsAlg t m e (B.env ()) (psiAlg B.env B.cell) :=
  (eqn_iff_isAlg B.env B.cell).mp B.eqn

/-- Every `T_Lax`-algebra is the algebra `emAlg` given by its carrier and its algebra 2-cell. -/
lemma alg_eq_emAlg {x : Obj} (B : (model t m e).Alg σL TL x) :
    B = emAlg t m e (B.env ()) (psiAlg B.env B.cell) (isAlg_of_alg B) :=
  em_alg_ext rfl (psiAlg_emAlg _ _ _).symm

variable {d : Obj} (u : d ⟶ c) (η : u ≫ t ⟶ u) (hη : IsAlg t m e u η)

/-- The structure cell of the precomposition of `emAlg t m e u η hη` with `h` is `ConjEq` to
`h ◁ η`. -/
lemma cell_precomp_emAlg {x : Obj} (h : x ⟶ d) :
    ConjEq (((emAlg t m e u η hη).precomp h).cell MndFun.T) (h ◁ η) :=
  (psi_conjEq _ _).trans ((psiAlg_precomp _ h).trans
    (ConjEq.whiskerLeft h (psiAlg_emAlg u η hη)))

/-- The precomposition of `emAlg t m e u η hη` with `h` is `emAlg t m e h' ψ hψ` if and only if
`h ≫ u = h'` and `ψ` is `h ◁ η` up to the induced `eqToHom`s. -/
lemma precomp_emAlg_eq_iff {x : Obj} (h : x ⟶ d) (h' : x ⟶ c) (ψ : h' ≫ t ⟶ h')
    (hψ : IsAlg t m e h' ψ) :
    (emAlg t m e u η hη).precomp h = emAlg t m e h' ψ hψ ↔
      ∃ hh : h ≫ u = h', ψ = eqToHom (congr($hh ≫ t).symm.trans (Category.assoc h u t)) ≫
        h ◁ η ≫ eqToHom hh := by
  constructor
  · intro hA
    have hh : h ≫ u = h' := congr(($hA).env ())
    have hc : ConjEq ψ (h ◁ η) := (psiAlg_emAlg h' ψ hψ).symm.trans ((psi_conjEq _ _).symm.trans
      ((Model.Alg.cell_conjEq_of_eq σL TL hA MndFun.T).symm.trans
        (cell_precomp_emAlg u η hη h)))
    obtain ⟨p, q, hpq⟩ := hc
    exact ⟨hh, hpq⟩
  · rintro ⟨hh, hψe⟩
    refine em_alg_ext hh ?_
    refine (psi_conjEq _ _).symm.trans ((cell_precomp_emAlg u η hη h).trans ?_)
    exact (ConjEq.intro hψe : ConjEq ψ (h ◁ η)).symm.trans (psiAlg_emAlg h' ψ hψ).symm

/-- Condition (1) of Remark 3.17 at `x` holds if and only if every `T_Lax`-algebra over `x` is the
precomposition of `emAlg t m e u η hη` with a unique `h : x ⟶ d`. -/
lemma em_one_iff (x : Obj) :
    (∀ (h' : x ⟶ c) (ψ : h' ≫ t ⟶ h'), IsAlg t m e h' ψ →
        ∃! h : x ⟶ d, ∃ hh : h ≫ u = h',
          ψ = eqToHom (congr($hh ≫ t).symm.trans (Category.assoc h u t)) ≫
            h ◁ η ≫ eqToHom hh) ↔
      ∀ B : (model t m e).Alg σL TL x, ∃! h : x ⟶ d, (emAlg t m e u η hη).precomp h = B := by
  constructor
  · intro P B
    obtain ⟨h, hp, hu⟩ := P (B.env ()) (psiAlg B.env B.cell) (isAlg_of_alg B)
    refine ⟨h, ?_, fun h₂ e₂ => hu h₂ ?_⟩
    · rw [alg_eq_emAlg B]
      exact (precomp_emAlg_eq_iff u η hη h _ _ _).mpr hp
    · exact (precomp_emAlg_eq_iff u η hη h₂ _ _ (isAlg_of_alg B)).mp
        (e₂.trans (alg_eq_emAlg B))
  · intro R h' ψ hψ
    obtain ⟨h, hh, hu⟩ := R (emAlg t m e h' ψ hψ)
    exact ⟨h, (precomp_emAlg_eq_iff u η hη h h' ψ hψ).mp hh,
      fun h₂ h₂p => hu h₂ ((precomp_emAlg_eq_iff u η hη h₂ h' ψ hψ).mpr h₂p)⟩

/-- A 2-cell `β : h₁ ≫ u ⟶ h₂ ≫ u` commutes with the structure cells of the precompositions of
`emAlg t m e u η hη` with `h₁` and `h₂` if and only if it satisfies the compatibility with `η` of
condition (2). -/
lemma em_comm_iff {x : Obj} (h₁ h₂ : x ⟶ d) (β : h₁ ≫ u ⟶ h₂ ≫ u) :
    (((emAlg t m e u η hη).precomp h₁).cell MndFun.T ≫
        (model t m e).interpCell (fun _ : Unit => β) (σL.fncod MndFun.T) =
      (model t m e).interpCell (fun _ : Unit => β) (σL.fndom MndFun.T) ≫
        ((emAlg t m e u η hη).precomp h₂).cell MndFun.T) ↔
      (β ▷ t ≫ eqToHom (Category.assoc _ _ _) ≫ h₂ ◁ η =
        eqToHom (Category.assoc _ _ _) ≫ h₁ ◁ η ≫ β) := by
  have hu₁ : ConjEq (((emAlg t m e u η hη).precomp h₁).cell MndFun.T ≫
      (model t m e).interpCell (fun _ : Unit => β) (σL.fncod MndFun.T)) (h₁ ◁ η ≫ β) :=
    ConjEq.comp (cell_precomp_emAlg u η hη h₁) (ConjEq.of_eq rfl)
  have hu : ConjEq (((emAlg t m e u η hη).precomp h₁).cell MndFun.T ≫
      (model t m e).interpCell (fun _ : Unit => β) (σL.fncod MndFun.T))
      (eqToHom (Category.assoc h₁ u t) ≫ h₁ ◁ η ≫ β) :=
    hu₁.trans ((ConjEq.of_eq (rfl : h₁ ◁ η ≫ β = h₁ ◁ η ≫ β)).eqToHom_comp
      (Category.assoc h₁ u t)).symm
  have hv : ConjEq ((model t m e).interpCell (fun _ : Unit => β) (σL.fndom MndFun.T) ≫
      ((emAlg t m e u η hη).precomp h₂).cell MndFun.T)
      (β ▷ t ≫ eqToHom (Category.assoc h₂ u t) ≫ h₂ ◁ η) :=
    ConjEq.comp (appCell_T_conjEq t m e _)
      ((cell_precomp_emAlg u η hη h₂).trans ((ConjEq.of_eq rfl).eqToHom_comp _).symm)
  rw [ConjEq.eq_iff hu hv]
  exact eq_comm

/-- The 2-cell of `T_Lax`-algebras given by `β` satisfying the condition of (2). -/
def emHom {x : Obj} {h₁ h₂ : x ⟶ d} (β : h₁ ≫ u ⟶ h₂ ≫ u)
    (hβ : β ▷ t ≫ eqToHom (Category.assoc _ _ _) ≫ h₂ ◁ η =
      eqToHom (Category.assoc _ _ _) ≫ h₁ ◁ η ≫ β) :
    Model.Alg.Hom ((emAlg t m e u η hη).precomp h₁) ((emAlg t m e u η hη).precomp h₂) where
  app _ := β
  comm f := by
    cases f
    exact (em_comm_iff u η hη h₁ h₂ β).mpr hβ

/-- Condition (2) of Remark 3.17 at `x` holds if and only if every morphism of `T_Lax`-algebras
between precompositions of `emAlg t m e u η hη` is induced by a unique 2-cell `θ : h₁ ⟶ h₂`. -/
lemma em_two_iff (x : Obj) :
    (∀ (h₁ h₂ : x ⟶ d) (β : h₁ ≫ u ⟶ h₂ ≫ u),
        β ▷ t ≫ eqToHom (Category.assoc _ _ _) ≫ h₂ ◁ η =
          eqToHom (Category.assoc _ _ _) ≫ h₁ ◁ η ≫ β →
        ∃! θ : h₁ ⟶ h₂, θ ▷ u = β) ↔
      ∀ (h₁ h₂ : x ⟶ d) (γ : Model.Alg.Hom ((emAlg t m e u η hη).precomp h₁)
          ((emAlg t m e u η hη).precomp h₂)),
        ∃! θ : h₁ ⟶ h₂, ∀ s, θ ▷ (emAlg t m e u η hη).env s = γ.app s := by
  constructor
  · intro P h₁ h₂ γ
    have hβ := (em_comm_iff u η hη h₁ h₂ (γ.app ())).mp (γ.comm MndFun.T)
    obtain ⟨θ, hθ, hu⟩ := P h₁ h₂ (γ.app ()) hβ
    exact ⟨θ, fun s => hθ, fun θ' h' => hu θ' (h' ())⟩
  · intro R h₁ h₂ β hβ
    obtain ⟨θ, hθ, hu⟩ := R h₁ h₂ (emHom u η hη β hβ)
    exact ⟨θ, hθ (), fun θ' h' => hu θ' fun _ => h'⟩

-- The binders are restated so that their order is that of the statement in `Challenge`.
end MonadAlgebras

section MonadAlgebrasStatement

variable [HasChosenProductsOfSize.{0} Cat.{w, v}] [HasChosenInserters Cat.{w, v}]
  [HasChosenEquifiers Cat.{w, v}] {c : Obj} (t : c ⟶ c) (m : t ≫ t ⟶ t) (e : 𝟙 c ⟶ t)

/-- Remark 3.17, algebras of a monad: for an algebra `(u, η)` of the monad `(t, m, e)`, conditions
(1) and (2) hold if and only if `d` represents the `T_Lax`-algebras of the monad via the comparison
functors of `MndK.emAlg t m e u η hη`. -/
theorem rem_3_17_em {d : Obj} (u : d ⟶ c) (η : u ≫ t ⟶ u) (hη : MndK.IsAlg t m e u η) :
    ((∀ {x : Obj} (h' : x ⟶ c) (ψ : h' ≫ t ⟶ h'), MndK.IsAlg t m e h' ψ →
        ∃! h : x ⟶ d, ∃ hh : h ≫ u = h',
          ψ = eqToHom (by rw [← hh, Category.assoc]) ≫ h ◁ η ≫ eqToHom hh) ∧
      ∀ {x : Obj} (h₁ h₂ : x ⟶ d) (β : h₁ ≫ u ⟶ h₂ ≫ u),
        β ▷ t ≫ eqToHom (Category.assoc _ _ _) ≫ h₂ ◁ η =
          eqToHom (Category.assoc _ _ _) ≫ h₁ ◁ η ≫ β →
        ∃! θ : h₁ ⟶ h₂, θ ▷ u = β) ↔
      IsThyRep (MndK.model t m e) MndK.σL MndK.TL d
        (fun x => (MndK.model t m e).algComparison x MndK.σL MndK.TL
          (MndK.emAlg t m e u η hη)) := by
  constructor
  · rintro ⟨hone, htwo⟩
    exact ⟨fun x => ((MndK.model t m e).algComparison_iso_iff x MndK.σL MndK.TL _).mpr
        ⟨(em_one_iff u η hη x).mp fun h' ψ hψ => hone h' ψ hψ,
          (em_two_iff u η hη x).mp fun a b β hβ => htwo a b β hβ⟩,
      fun k => (MndK.model t m e).algComparison_natural _ MndK.σL MndK.TL _ k,
      fun α a => (MndK.model t m e).algComparison_natural₂ _ MndK.σL MndK.TL _ α a⟩
  · rintro ⟨hiso, -, -⟩
    refine ⟨fun {x} h' ψ hψ => ?_, fun {x} a b β hβ => ?_⟩
    · exact (em_one_iff u η hη x).mpr
        (((MndK.model t m e).algComparison_iso_iff x MndK.σL MndK.TL _).mp (hiso x)).1 h' ψ hψ
    · exact (em_two_iff u η hη x).mpr
        (((MndK.model t m e).algComparison_iso_iff x MndK.σL MndK.TL _).mp (hiso x)).2 a b β hβ

end MonadAlgebrasStatement

end UlmerBialgebras.Paper
