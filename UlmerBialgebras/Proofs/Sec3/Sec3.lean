module

public import UlmerBialgebras.Kan.KanBialgebra
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Examples.MonEquiv
public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Proofs.Sec3.TransposedDatum
public import UlmerBialgebras.Proofs.Sec3.MonModelCalc
public import UlmerBialgebras.Proofs.Sec3.MonoidalLaxInduced
public import UlmerBialgebras.Models.CoMor
public import UlmerBialgebras.Models.CoBialgebra
public import UlmerBialgebras.Models.CoInduced

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Solution: Sections 2 and 3

Proofs of the numbered results of Sections 2 and 3, restating the theorems of
`UlmerBialgebras/Paper/Sec2.lean`.

## Main results

* `UlmerBialgebras.Paper.ex_2_3_1`: Example 2.3 (1), `CAT` has all PIE limits.
* `UlmerBialgebras.Paper.prop_3_15`: Proposition 3.15, `M^σ` is the object of pre-bialgebras and
  `M^T` the object of bialgebras of `B_{M,T}`.
* `UlmerBialgebras.Paper.thm_3_22`: Theorem 3.22, the induced functor of algebras.
* `UlmerBialgebras.Paper.cor_3_24`: Corollary 3.24, a lax monoidal functor induces a functor between
  the categories of internal monoids, lying over it.
* `UlmerBialgebras.Paper.ex_3_20_3`: Examples 3.20 (3), `M^{T_Field}` is equivalent to the category
  of fields.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Sections 2 and 3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
* [S. Lack, G. Tendas, *Virtual concepts in the theory of accessible categories*][LACK2023107196],
  Theorem 5.5, Theorem 5.9
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras]
-/

universe u v w u' v' u'' v'' u₁ u₂ u₃ s₁ s₂ s₃ uᵥ u𝓌

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Section 3 -/

section Sec3

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Remark 3.2 (1)** ([forsman2026syntactic]): if `g, g'` have left adjoints `l, l'`, let `I'`
be any inserter of `l f, id_c` and `B'` the datum of the remark (`Rem32.transposedDatum`), with
inserter `I'`, function supports `l f, id_c` and equational supports `l' f', id_c`; its equations
`α', β'` are the mates of `α, β`, restricted along the canonical comparison `I' ⟶ Ins(f, g)`
(`Rem32.comparison`). Then the comparison is an isomorphism over `c` (the paper's
`Ins(f, g) ≅ Ins(l f, id_c)`), the equifier `Bialg(B')` exists, and every equifier of `α', β'` is
isomorphic over `c` to `Bialg(B)`. -/
theorem rem_3_2_adj (B : BialgDatum (Obj := Obj)) {l : B.x ⟶ B.c} {l' : B.y ⟶ B.c}
    (A : TwoAdj l B.g) (A' : TwoAdj l' B.g') (I' : Inserter (B.f ≫ l) (𝟙 B.c))
    (E : Equifier B.α B.β) :
    let B' := Rem32.transposedDatum B (Rem32.relOfAdj A B.f) (Rem32.relOfAdj A' B.f') I'
    (∃ ψ : B.ins.pt ⟶ I'.pt,
      Rem32.comparison (Rem32.relOfAdj A B.f) B.ins I' ≫ ψ = 𝟙 I'.pt ∧
      ψ ≫ Rem32.comparison (Rem32.relOfAdj A B.f) B.ins I' = 𝟙 B.ins.pt ∧
      Rem32.comparison (Rem32.relOfAdj A B.f) B.ins I' ≫ B.ins.u = I'.u) ∧
    (∃ E' : Equifier B'.α B'.β, IsoOver (B.uB E) (B'.uB E')) ∧
      ∀ E' : Equifier B'.α B'.β, IsoOver (B.uB E) (B'.uB E') :=
  Rem32.comparison_iso_and_isoOver_transposed B (Rem32.relOfAdj A B.f) (Rem32.relOfAdj A' B.f') I' E

/-- **Remark 3.2 (2)** ([forsman2026syntactic]): the same with `f`- and `f'`-relative left adjoints
`r, r'` of `g, g'`: for any inserter `I'` of `r, id_c`, the comparison `I' ⟶ Ins(f, g)` is an
isomorphism over `c`, and `Bialg(B)` is isomorphic over `c` to `Bialg(B')` for the transposed
datum `B' = Rem32.transposedDatum B R R' I'`, with supports `r, id_c` and `r', id_c`. -/
theorem rem_3_2_rel (B : BialgDatum (Obj := Obj)) {r r' : B.c ⟶ B.c}
    (R : RelLeftAdj2 B.f B.g r) (R' : RelLeftAdj2 B.f' B.g' r') (I' : Inserter r (𝟙 B.c))
    (E : Equifier B.α B.β) :
    let B' := Rem32.transposedDatum B R R' I'
    (∃ ψ : B.ins.pt ⟶ I'.pt, Rem32.comparison R B.ins I' ≫ ψ = 𝟙 I'.pt ∧
      ψ ≫ Rem32.comparison R B.ins I' = 𝟙 B.ins.pt ∧
      Rem32.comparison R B.ins I' ≫ B.ins.u = I'.u) ∧
    (∃ E' : Equifier B'.α B'.β, IsoOver (B.uB E) (B'.uB E')) ∧
      ∀ E' : Equifier B'.α B'.β, IsoOver (B.uB E) (B'.uB E') :=
  Rem32.comparison_iso_and_isoOver_transposed B R R' I' E

variable [HasChosenFinProducts.{u, v, w} Obj] {Sg : TwoSig.{u₁, u₂, u₃}}

/-- **Proposition 3.11** ([forsman2026syntactic]): the composite of lax morphisms (with the
composite structure 2-cells `φ^B = (G_d * η^B) • (θ^B * F_c̄)`) is a lax morphism. -/
theorem prop_3_11_lax {M N P : Model Sg Obj} (F : LaxMor M N) (G : LaxMor N P) :
    ∃ H : LaxMor M P, H.toLaxData = F.toLaxData.comp G.toLaxData := ⟨F.comp G, rfl⟩

/-- **Proposition 3.11** ([forsman2026syntactic]): strong morphisms are closed under composition. -/
theorem prop_3_11_strong {M N P : Model Sg Obj} (F : LaxMor M N) (G : LaxMor N P)
    (hF : ∀ B, IsIso (F.str B)) (hG : ∀ B, IsIso (G.str B)) :
    ∀ B, IsIso ((F.toLaxData.comp G.toLaxData).str B) := fun B => by
  have := hF B
  have := hG B
  exact LaxData.comp_str_isIso _ _ B

/-- **Proposition 3.11** ([forsman2026syntactic]): oplax morphisms are closed under composition. -/
theorem prop_3_11_oplax {M N P : Model Sg Obj} (F : OplaxMor M N) (G : OplaxMor N P) :
    ∃ H : OplaxMor M P, H.toOplaxData = F.toOplaxData.comp G.toOplaxData := ⟨F.comp G, rfl⟩

/-- **Proposition 3.15** ([forsman2026syntactic]): `M^σ` is the object of pre-bialgebras and `M^T`
the object of bialgebras of the bialgebraic datum `B_{M,T}`. -/
theorem prop_3_15 [HasChosenInserters.{u, v, w} Obj]
    [HasChosenEquifiers.{u, v, w} Obj] (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj] :
    (modelDatum M sg T).ins = M.sigIns sg ∧
      ∃ E : Equifier (modelDatum M sg T).α (modelDatum M sg T).β,
        E.pt = M.thyObj sg T ∧ HEq E.e (M.e sg T) :=
  ⟨rfl, Equifier.conj (M.thyEquif sg T) (M.sigCell_eq sg T T.dom) (M.sigCell_eq sg T T.cod).symm,
    rfl, HEq.rfl⟩

/-- **Lemma 3.18** ([forsman2026syntactic]), equation (3.2):
`M(t^x̄(t₁,…,tₙ)) = M_x̄(t) ∘ (M(t₁),…,M(tₙ))`. -/
theorem lem_3_18_1 (M : Model Sg Obj) {V : Type uᵥ} {W : Type u𝓌} {vty : V → Sg.Cat}
    {wty : W → Sg.Cat} {x : Obj} (ρ : ∀ w, x ⟶ M.obj (wty w))
    (sub : ∀ v : V, Trm Sg.toFunSig wty (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interp ρ (t.subst sub) = M.interp (fun v => M.interp ρ (sub v)) t := M.interp_subst ρ sub t

/-- **Lemma 3.18** ([forsman2026syntactic]), equation (3.3): the factorization of
`η_{t^x̄(t₁,…,tₙ)}`. -/
theorem lem_3_18_2 {M N : Model Sg Obj} (F : LaxMor M N) {V : Type uᵥ} {W : Type u𝓌}
    {vty : V → Sg.Cat} {wty : W → Sg.Cat} {x : Obj} (ρ : ∀ w, x ⟶ M.obj (wty w))
    (sub : ∀ v : V, Trm Sg.toFunSig wty (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    F.toLaxData.eta ρ (t.subst sub) =
      eqToHom (by rw [N.interp_subst]) ≫
        N.interpCell (fun v => F.toLaxData.eta ρ (sub v)) t ≫
        F.toLaxData.eta (fun v => M.interp ρ (sub v)) t ≫
        eqToHom (by rw [← M.interp_subst]) := F.toLaxData.eta_subst ρ sub t

/-- **Lemma 3.21 (1)** ([forsman2026syntactic]): if `η_t` is invertible for every function coarity
term, there is a unique `F^σ : M^σ → N^σ` with `u_N F^σ = F₀ u_M` and satisfying equation (3.4). -/
theorem lem_3_21_1 [HasChosenInserters.{u, v, w} Obj]
    {M N : Model Sg Obj} (F : LaxMor M N) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fncod f))) :
    ∃! G : M.sigObj sg ⟶ N.sigObj sg, ∃ hu : G ≫ N.u sg = M.u sg ≫ F.prod0 sg,
      G ◁ (N.sigIns sg).φ =
        eqToHom (by rw [← Category.assoc, hu]) ≫ F.sigStr sg hiso ≫
          eqToHom (by rw [← Category.assoc, hu]) :=
  ⟨F.sigMor sg hiso, ⟨F.sigMor_u sg hiso, (N.sigIns sg).lift_φ _ _⟩,
    fun _ ⟨hu, hφ⟩ => (N.sigIns sg).lift_uniq _ _ _ hu hφ⟩

/-- **Lemma 3.21 (2)** ([forsman2026syntactic]): equation (3.5),
`η_{t₂} u_M • p̄_N F^σ = F_c p̄_M • η_{t₁} u_M`, for every path `p : t₁ → t₂` of the term graph. -/
theorem lem_3_21_2 [HasChosenInserters.{u, v, w} Obj]
    {M N : Model Sg Obj} (F : LaxMor M N) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fncod f))) {c : Sg.Cat} {t t' : sg.CTrm c}
    (p : sg.Path t t') :
    eqToHom (F.sigMor_sigTm sg hiso t).symm ≫ (F.sigMor sg hiso ◁ N.pathCell sg p) ≫
        eqToHom (F.sigMor_sigTm sg hiso t') ≫ F.Psi sg t'
      = F.Psi sg t ≫ (M.pathCell sg p ▷ F.cell c) := by
  have h := F.theta_path sg hiso p
  simp only [LaxMor.Theta, Category.assoc] at h
  rw [h]
  simp

/-- **Theorem 3.22 (Induced Functor of Algebras Theorem).** ([forsman2026syntactic]) -/
theorem thm_3_22 [HasChosenInserters.{u, v, w} Obj]
    [HasChosenEquifiers.{u, v, w} Obj] {M N : Model Sg Obj} (F : LaxMor M N)
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁, u, v, w} Obj]
    [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fncod f))) (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
    (hmono : ∀ r : T.Eqn, Mono ((M.e sg T ≫ M.u sg) ◁ F.etaTm sg (T.cod r))) :
    ∃! G : M.thyObj sg T ⟶ N.thyObj sg T, G ≫ N.e sg T = M.e sg T ≫ F.sigMor sg hiso :=
  F.exists_unique_thyMor sg hiso T hmono

/-- **Corollary 3.23 (1)** ([forsman2026syntactic]): lax morphisms induce 1-cells for algebraic
theories. -/
theorem cor_3_23_1 [HasChosenInserters.{u, v, w} Obj]
    [HasChosenEquifiers.{u, v, w} Obj] {M N : Model Sg Obj} (F : LaxMor M N)
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁, u, v, w} Obj]
    [HasChosenProductsOfSize.{s₂, u, v, w} Obj] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
    (halg : T.IsAlgebraic) : ∃ G : M.thyObj sg T ⟶ N.thyObj sg T,
      G ≫ N.e sg T = M.e sg T ≫ F.sigMor sg (fun f => F.toLaxData.eta_isVar _ (halg.1 f)) :=
  (F.exists_unique_thyMor_of_algebraic sg T halg).exists

/-- **Corollary 3.23 (2)** ([forsman2026syntactic]): oplax morphisms induce 1-cells for coalgebraic
theories: a 1-cell `F^T : M^T → N^T` with `e_N F^T = F^σ e_M`, for the oplax `F^σ : M^σ → N^σ` of
Lemma 3.21 (1) (`UlmerBialgebras.OplaxMor.sigMor`; `η_t` is an identity at the function arity terms,
which are sorts). -/
theorem cor_3_23_2 [HasChosenInserters.{u, v, w} Obj]
    [HasChosenEquifiers.{u, v, w} Obj] {M N : Model Sg Obj} (F : OplaxMor M N)
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁, u, v, w} Obj]
    [HasChosenProductsOfSize.{s₂, u, v, w} Obj] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
    (hcoalg : T.IsCoalgebraic) : ∃ G : M.thyObj sg T ⟶ N.thyObj sg T,
      G ≫ N.e sg T =
        M.e sg T ≫ F.sigMor sg (fun f => F.toOplaxData.eta_isVar _ (hcoalg.1 f)) := by
  -- Part (1) in `K^co`, for the lax morphism `F.toLax` and the algebraic theory `T^co`; its
  -- `F^σ` is the oplax `F^σ` of `F` (`OplaxMor.toLax_sigMor`).
  obtain ⟨G, hG⟩ := cor_3_23_1 (Obj := Co Obj) F.toLax sg.co T.co hcoalg.co
  exact F.exists_thyMor_of_co sg T _ G hG

/-- **Corollary 3.23 (3)** ([forsman2026syntactic]): strong morphisms induce 1-cells for all
theories. -/
theorem cor_3_23_3 [HasChosenInserters.{u, v, w} Obj]
    [HasChosenEquifiers.{u, v, w} Obj] {M N : Model Sg Obj} (F : LaxMor M N)
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁, u, v, w} Obj]
    [HasChosenProductsOfSize.{s₂, u, v, w} Obj] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
    (hstrong : ∀ B : Sg.Fun, IsIso (F.str B)) : ∃ G : M.thyObj sg T ⟶ N.thyObj sg T,
      G ≫ N.e sg T = M.e sg T ≫ F.sigMor sg
        (fun f => F.toLaxData.eta_isIso_of_strong hstrong _ (sg.fncod f)) :=
            (F.exists_unique_thyMor_of_strong sg T hstrong).exists

end Sec3

/-- **Corollary 3.24** ([forsman2026syntactic]): a lax monoidal functor `F : C ⥤ D` induces a
functor `F̄ : Mon(C) ⥤ Mon(D)` between the categories of internal monoids. `F̄` lies over `F`, and
it gives `F X` the monoid structure induced by the lax structure of `F`: multiplication `μ_F ≫ F(m)`
and unit `ε_F ≫ F(e)`. -/
theorem cor_3_24 (C : Type u) [Category.{v} C] [MonoidalCategory C] (D : Type u')
    [Category.{v'} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    ∃ G : Mon C ⥤ Mon D, G ⋙ Mon.forget D = Mon.forget C ⋙ F ∧
      ∀ M : Mon C,
        HEq (MonObj.mul (X := (G.obj M).X))
            (Functor.LaxMonoidal.μ F M.X M.X ≫ F.map (MonObj.mul (X := M.X))) ∧
          HEq (MonObj.one (X := (G.obj M).X))
            (Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one (X := M.X))) :=
  MonEx.exists_monFunctor_of_laxMonoidal C D F

/-- **Examples 3.20 (1)**: for the monoidal model `M` of a monoidal category `C`, the category
`M^{T_Mon}` is the category of internal monoids of `C`. There are mutually inverse functors
`F : M^{T_Mon} ⥤ Mon C` and `G : Mon C ⥤ M^{T_Mon}` (an isomorphism of categories), and `F` lies
over `C`. Here `M^{T_Mon}` lies over `C` through the forgetful 1-cell `u_M e_M : M^{T_Mon} → M₀`
followed by the projection `M₀ = ∏_{s} C → C` at the unique sort `s` of `σ_Mon`, and `Mon C` lies
over `C` through `Mon.forget C`.

References: [forsman2026syntactic]. -/
theorem ex_3_20_1 (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] :
    ∃ (F : MonEx.ThyObj C ⥤ Mon C) (G : Mon C ⥤ MonEx.ThyObj C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Mon.forget C = ((MonEx.monModel C).thyForget MonEx.oneSig MonEx.monTheory).toFunctor ⋙
          (((MonEx.monModel C).P0 MonEx.oneSig).π ()).toFunctor :=
  ⟨MonEx.comparison C, MonEx.inverseFunctor C, MonEx.comparison_comp_inverseFunctor C,
    MonEx.inverseFunctor_comp_comparison C, MonEx.comparison_comp_forget C⟩

section MonModel

open MonModel

/-- **Examples 3.20 (1)** for an arbitrary `Σ_Mon`-model `M` in `CAT`: `M^σ` is the category of
pointed magmas of `M`. Write `x ⊗ y = M(□)(x, y)` and `I = M(I)(*)`
(`UlmerBialgebras/Paper/Sec3DefsMonModel.lean`). The objects `z` of `M^σ` correspond bijectively to
the triples
`(x, m : x ⊗ x → x, e : I → x)` through `z ↦ (ob z, mul z, one z)`. A morphism `f : z ⟶ z'` of
`M^σ` is determined by its underlying morphism `f.base () : x ⟶ x'` of `M_c`, and a morphism
`g : x ⟶ x'` underlies a morphism `z ⟶ z'` if and only if `g ∘ m = m' ∘ (g ⊗ g)` and
`g ∘ e = e'` (written below in diagrammatic order). -/
theorem ex_3_20_1_magma (M : Model MonEx.twoSig Cat.{v, max u v}) :
    Function.Bijective (fun z : M.sigObj MonEx.oneSig =>
        (⟨ob z, mul z, one z⟩ : Σ x : M.obj (), (tensObj x x ⟶ x) × (unitObj M ⟶ x))) ∧
      ∀ z z' : M.sigObj MonEx.oneSig,
        Function.Injective (fun f : z ⟶ z' => Ins.Hom.base f ()) ∧
          ∀ g : ob z ⟶ ob z', (∃ f : z ⟶ z', Ins.Hom.base f () = g) ↔
            mul z ≫ g = tensHom g g ≫ mul z' ∧ one z ≫ g = one z' :=
  ⟨MonModel.sigObj_bijective, fun z z' =>
    ⟨MonModel.hom_base_injective z z', fun g => MonModel.exists_hom_iff g⟩⟩

/-- **Examples 3.20 (1)** for an arbitrary `Σ_Mon`-model `M` in `CAT`, for instance a monoidal
category. Write `x ⊗ y = M(□)(x, y)` and `I = M(I)(*)`
(`UlmerBialgebras/Paper/Sec3DefsMonModel.lean`). An object
`z = (x, m : x ⊗ x → x, e : I → x)` of `M^σ`, a pointed magma of `M`, lies in the full
subcategory `M^T` of `M^σ` (the image of the inclusion `e_M : M^T → M^σ`) if and only if
`m ∘ (m ⊗ x) = m ∘ (x ⊗ m) ∘ M(α)_{x,x,x}`, `m ∘ (x ⊗ e) = M(ρ)_x` and `m ∘ (e ⊗ x) = M(λ)_x`.
The equations are written in diagrammatic order, and `m ⊗ x` is `m ⊗ 𝟙 x`. -/
theorem ex_3_20_1_iff (M : Model MonEx.twoSig Cat.{v, max u v}) (z : M.sigObj MonEx.oneSig) :
    (∃ t : M.thyObj MonEx.oneSig MonEx.monTheory,
        (M.e MonEx.oneSig MonEx.monTheory).toFunctor.obj t = z) ↔
      (tensHom (mul z) (𝟙 (ob z)) ≫ mul z =
          assocApp (ob z) (ob z) (ob z) ≫ tensHom (𝟙 (ob z)) (mul z) ≫ mul z ∧
        tensHom (𝟙 (ob z)) (one z) ≫ mul z = runitApp (ob z) ∧
        tensHom (one z) (𝟙 (ob z)) ≫ mul z = lunitApp (ob z)) :=
  MonModel.mem_thy_iff z

end MonModel

/-- **Examples 3.20 (3)** ([forsman2026syntactic]): for the model `(Set, ×, 1, (-) + 1)`, the
category `M^{T_Field}` is equivalent to the category of fields. -/
theorem ex_3_20_3 : Nonempty (FieldEx.ThyObj.{u} ≌ FieldEx.FieldCat.{u}) :=
    FieldEx.nonempty_thyObj_equiv_fieldCat

end UlmerBialgebras.Paper
