module

public import UlmerBialgebras.Paper.Sec3DefsTwoFun

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Challenge: Example 3.12 (natural transformations as morphisms of models)

`A` is a 2-category, `K` a 2-category with chosen finite products, and `F G : A → K` strict
2-functors with their `Σ_A`-models `M_F`, `M_G` (Examples 3.4 and 3.9,
`UlmerBialgebras/Paper/Sec3DefsTwoFun.lean`).
The categories `[F, G]_Lax`, `[F, G]_Oplax`, `[F, G]_Psd`, `[F, G]_Strict` of the paper have
as objects the lax, oplax, strong and strict morphisms `M_F → M_G`, and as morphisms their
transformations. The statements give bijections with lax (resp. oplax) natural
transformations, on objects and on morphisms, that keep the components; on structure
2-cells they send `σ_f` to `σ_f` whiskered by the unary product projection. Under the lax
bijection, pseudo transformations correspond to strong morphisms and strict (2-natural)
transformations to strict morphisms. Composition of transformations and of modifications is
componentwise on both sides, so these are isomorphisms of categories.

## Main results

* `UlmerBialgebras.Paper.ex_3_12_lax`: a bijection between lax natural transformations `F ⇒ G` and
  lax morphisms `M_F → M_G`, and between their modifications and transformations, under which pseudo
  and strict transformations correspond to strong and strict morphisms (Example 3.12).
* `UlmerBialgebras.Paper.ex_3_12_oplax`: the same bijections for oplax transformations and oplax
  morphisms (Example 3.12).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 3.12 (with Examples 3.4, 3.9)
-/

universe u v w ua va wa

namespace UlmerBialgebras.Paper

open CategoryTheory TwoFun

variable {A : Type ua} [Bicategory.{wa, va} A] [Bicategory.Strict A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K]

/-- **Example 3.12** ([forsman2026syntactic]) (lax, pseudo and strict): lax morphisms `M_F → M_G` of
`Σ_A`-models and their transformations are lax natural transformations `F ⇒ G` and modifications;
strong morphisms are the pseudo-natural transformations and strict morphisms the strict ones. -/
theorem ex_3_12_lax (F G : StrictTwoFunctor K A) :
    ∃ e : LaxNat F G ≃ LaxMor F.model G.model,
      (∀ σ a, (e σ).cell a = σ.app a) ∧
      (∀ σ {a b : A} (f : a ⟶ b),
        HEq ((e σ).str ⟨a, b, f⟩)
          ((HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj a)).π 0 ◁ σ.nat f)) ∧
      (∀ σ τ, ∃ m : LaxModif σ τ ≃ LaxTwoCell (e σ).toLaxData (e τ).toLaxData,
        ∀ Γ a, HEq ((m Γ).app a) (Γ.app a)) ∧
      (∀ σ, σ.IsPseudo ↔ ∀ B, IsIso ((e σ).str B)) ∧
      (∀ σ, σ.IsStrict ↔ ∀ B, ∃ h, (e σ).str B = eqToHom h) := sorry

/-- **Example 3.12** ([forsman2026syntactic]) (oplax): oplax morphisms `M_F → M_G` of `Σ_A`-models
and their transformations are oplax natural transformations `F ⇒ G` and modifications. -/
theorem ex_3_12_oplax (F G : StrictTwoFunctor K A) :
    ∃ e : OplaxNat F G ≃ OplaxMor F.model G.model,
      (∀ σ a, (e σ).cell a = σ.app a) ∧
      (∀ σ {a b : A} (f : a ⟶ b),
        HEq ((e σ).str ⟨a, b, f⟩)
          ((HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj a)).π 0 ◁ σ.nat f)) ∧
      (∀ σ τ, ∃ m : OplaxModif σ τ ≃ OplaxTwoCell (e σ).toOplaxData (e τ).toOplaxData,
        ∀ Γ a, HEq ((m Γ).app a) (Γ.app a)) := sorry

end UlmerBialgebras.Paper
