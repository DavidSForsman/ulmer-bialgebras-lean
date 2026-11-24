module

public import UlmerBialgebras.Paper.Sec3DefsPsFun
public import UlmerBialgebras.Proofs.Sec3.PsFunModel

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Solution: Example 3.12 for pseudofunctors out of a bicategory

`A` is a bicategory, `K` a strict 2-category with chosen finite products, and `F G : A → K`
pseudofunctors (Mathlib's `Pseudofunctor`) with their `Σ_A`-models `M_F`, `M_G` (Examples 3.4 and
3.9, `UlmerBialgebras/Paper/Sec3DefsPsFun.lean`). The categories `[F, G]_Lax`, `[F, G]_Oplax`, `[F,
G]_Psd`,
`[F, G]_Strict` of the paper have as objects the lax, oplax, strong and strict morphisms
`M_F → M_G`, and as morphisms their transformations. The statements give bijections with Mathlib's
lax (resp. oplax) transformations `F.toLax ⟶ G.toLax` and their modifications, on objects and on
morphisms, that keep the components; on structure 2-cells they send `σ_f` to `σ_f` whiskered by the
unary product projection. Under these bijections, strong transformations (invertible naturality
2-cells) correspond to strong morphisms and strict (2-natural) transformations (identity naturality
2-cells, `eqToHom`) to strict morphisms. Composition of transformations and of modifications is
componentwise on both sides, so these are isomorphisms of categories.

This generalizes `ex_3_12_lax` and `ex_3_12_oplax` (`UlmerBialgebras/Paper/Sec3Ex.lean`), which are
stated for
strict 2-functors out of a strict 2-category (`UlmerBialgebras/Paper/Sec3DefsTwoFun.lean`) and are
kept.

## Main results

* `UlmerBialgebras.Paper.ex_3_12_lax_bicat`: a bijection between lax transformations `F ⇒ G` and lax
  morphisms `M_F → M_G`, and between their modifications and transformations, under which strong
  and strict transformations correspond to strong and strict morphisms (Example 3.12).
* `UlmerBialgebras.Paper.ex_3_12_oplax_bicat`: the same bijections for oplax transformations and
  oplax morphisms (Example 3.12).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 3.12 (with Examples 3.4, 3.9)
-/

universe u v w ua va wa

namespace UlmerBialgebras.Paper

open CategoryTheory PsFun

variable {A : Type ua} [Bicategory.{wa, va} A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K]

/-- **Example 3.12** ([forsman2026syntactic]) (lax, strong and strict): lax morphisms `M_F → M_G`
of `Σ_A`-models and their transformations are lax transformations `F ⇒ G` and modifications;
strong morphisms are the strong transformations and strict morphisms the strict ones. -/
theorem ex_3_12_lax_bicat (F G : Pseudofunctor A K) :
    ∃ e : Lax.LaxTrans F.toLax G.toLax ≃ LaxMor (model F) (model G),
      (∀ σ a, (e σ).cell a = σ.app a) ∧
      (∀ σ {a b : A} (f : a ⟶ b),
        HEq ((e σ).str ⟨a, b, f⟩)
          ((HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj a)).π 0 ◁ σ.naturality f)) ∧
      (∀ σ τ, ∃ m : Lax.LaxTrans.Modification σ τ ≃
          LaxTwoCell (e σ).toLaxData (e τ).toLaxData,
        ∀ Γ a, HEq ((m Γ).app a) (Γ.app a)) ∧
      (∀ σ, (∀ {a b : A} (f : a ⟶ b), IsIso (σ.naturality f)) ↔ ∀ B, IsIso ((e σ).str B)) ∧
      (∀ σ, (∀ {a b : A} (f : a ⟶ b), ∃ h, σ.naturality f = eqToHom h) ↔
        ∀ B, ∃ h, (e σ).str B = eqToHom h) :=
  ⟨laxEquiv F G, fun _ _ => rfl, fun σ _ _ f => (toLaxData_str σ f).heq,
    fun σ τ => ⟨laxModifEquiv F G σ τ, fun _ _ => HEq.rfl⟩, laxIsIso_iff F G,
    laxIsStrict_iff F G⟩

/-- **Example 3.12** ([forsman2026syntactic]) (oplax, strong and strict): oplax morphisms
`M_F → M_G` of `Σ_A`-models and their transformations are oplax transformations `F ⇒ G` and
modifications; strong morphisms are the strong transformations and strict morphisms the strict
ones. -/
theorem ex_3_12_oplax_bicat (F G : Pseudofunctor A K) :
    ∃ e : Lax.OplaxTrans F.toLax G.toLax ≃ OplaxMor (model F) (model G),
      (∀ σ a, (e σ).cell a = σ.app a) ∧
      (∀ σ {a b : A} (f : a ⟶ b),
        HEq ((e σ).str ⟨a, b, f⟩)
          ((HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj a)).π 0 ◁ σ.naturality f)) ∧
      (∀ σ τ, ∃ m : Lax.OplaxTrans.Modification σ τ ≃
          OplaxTwoCell (e σ).toOplaxData (e τ).toOplaxData,
        ∀ Γ a, HEq ((m Γ).app a) (Γ.app a)) ∧
      (∀ σ, (∀ {a b : A} (f : a ⟶ b), IsIso (σ.naturality f)) ↔ ∀ B, IsIso ((e σ).str B)) ∧
      (∀ σ, (∀ {a b : A} (f : a ⟶ b), ∃ h, σ.naturality f = eqToHom h) ↔
        ∀ B, ∃ h, (e σ).str B = eqToHom h) :=
  ⟨oplaxEquiv F G, fun _ _ => rfl, fun σ _ _ f => (toOplaxData_str σ f).heq,
    fun σ τ => ⟨oplaxModifEquiv F G σ τ, fun _ _ => HEq.rfl⟩, oplaxIsIso_iff F G,
    oplaxIsStrict_iff F G⟩

end UlmerBialgebras.Paper
