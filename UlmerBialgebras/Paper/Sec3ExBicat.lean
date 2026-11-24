module

public import UlmerBialgebras.Paper.Sec3DefsPsFun

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Challenge: Example 3.12 for pseudofunctors out of a bicategory

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

/-- **Example 3.12, lax, strong and strict (bicategory form)** ([forsman2026syntactic], §3).

```latex
Let $F, G \colon \A \to \K$ be strict $2$-functors. We define the categories
\[
[F, G]_\mathbf{Lax}, \quad [F, G]_\mathbf{Oplax}, \quad [F, G]_\Psd, \quad [F, G]_\mathbf{Strict}
\]
as the categories whose objects are lax, oplax, strong, and strict morphisms $M_F \to M_G$ of
$\Sigma_\A$-models in $\K$ (Example \ref{ex:2FunctorInucingAModel}), respectively, and whose
morphisms are transformations between them. (The implicit size issues are sidestepped with
Grothendieck universes.)

These objects correspond precisely to lax, oplax, pseudo-, and strict natural transformations
$F \Rightarrow G$, and the morphisms between them are modifications.
```

**Reading.**
* $\A$, $\K$ ↦ bicategory `A` (`[Bicategory.{wa, va} A]`) and strict 2-category `K`
  (`[Bicategory.{w, v} K]`, `[Bicategory.Strict K]`) with chosen finite products
  (`[HasChosenFinProducts.{u, v, w} K]`).
* $F, G \colon \A \to \K$ ↦ pseudofunctors `F G : Pseudofunctor A K`, with induced
  $\Sigma_\A$-models `model F` and `model G`.
* objects of $[F, G]_{\mathbf{Lax}}$ correspond to lax transformations $F \Rightarrow G$ ↦
  equivalence `e : Lax.LaxTrans F.toLax G.toLax ≃ LaxMor (model F) (model G)` preserving object
  components `σ.app a` (`LaxData.cell`) and sending the naturality 2-cell `σ.naturality f` at
  `f : a ⟶ b` to `LaxData.str` at `⟨a, b, f⟩` whiskered by the unary-product projection (`HEq`).
* morphisms are modifications ↦ equivalence
  `m : Lax.LaxTrans.Modification σ τ ≃ LaxTwoCell (LaxMor.toLaxData (e σ)) (LaxMor.toLaxData (e τ))`
  preserving components (`HEq`).
* $[F, G]_{\Psd}$ and $[F, G]_{\mathbf{Strict}}$ ↦ `IsIso (σ.naturality f)` for all `f` iff
  `IsIso (LaxData.str (LaxMor.toLaxData (e σ)) B)` for all `B` (strong morphisms), and
  `σ.naturality f = eqToHom h` for all `f` iff
  `LaxData.str (LaxMor.toLaxData (e σ)) B = eqToHom h` for all `B` (strict morphisms).

**Deviations.**
- stronger: stated for pseudofunctors out of an arbitrary bicategory `A` rather than strict
  2-functors out of a strict 2-category (`docs/STATE.yml`, deviations).
-/
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
        ∀ B, ∃ h, (e σ).str B = eqToHom h) := sorry

/-- **Example 3.12, oplax, strong and strict (bicategory form)** ([forsman2026syntactic], §3).

```latex
Let $F, G \colon \A \to \K$ be strict $2$-functors. We define the categories
\[
[F, G]_\mathbf{Lax}, \quad [F, G]_\mathbf{Oplax}, \quad [F, G]_\Psd, \quad [F, G]_\mathbf{Strict}
\]
as the categories whose objects are lax, oplax, strong, and strict morphisms $M_F \to M_G$ of
$\Sigma_\A$-models in $\K$ (Example \ref{ex:2FunctorInucingAModel}), respectively, and whose
morphisms are transformations between them. (The implicit size issues are sidestepped with
Grothendieck universes.)

These objects correspond precisely to lax, oplax, pseudo-, and strict natural transformations
$F \Rightarrow G$, and the morphisms between them are modifications.
```

**Reading.**
* $\A$, $\K$ ↦ bicategory `A` (`[Bicategory.{wa, va} A]`) and strict 2-category `K`
  (`[Bicategory.{w, v} K]`, `[Bicategory.Strict K]`) with chosen finite products
  (`[HasChosenFinProducts.{u, v, w} K]`).
* $F, G \colon \A \to \K$ ↦ pseudofunctors `F G : Pseudofunctor A K`, with induced
  $\Sigma_\A$-models `model F` and `model G`.
* objects of $[F, G]_{\mathbf{Oplax}}$ correspond to oplax transformations $F \Rightarrow G$ ↦
  equivalence `e : Lax.OplaxTrans F.toLax G.toLax ≃ OplaxMor (model F) (model G)` preserving object
  components `σ.app a` (`OplaxData.cell`) and sending the naturality 2-cell `σ.naturality f` at
  `f : a ⟶ b` to `OplaxData.str` at `⟨a, b, f⟩` whiskered by the unary-product projection (`HEq`).
* morphisms are modifications ↦ equivalence `m : Lax.OplaxTrans.Modification σ τ ≃
  OplaxTwoCell (OplaxMor.toOplaxData (e σ)) (OplaxMor.toOplaxData (e τ))` preserving components
  (`HEq`).
* $[F, G]_{\Psd}$ and $[F, G]_{\mathbf{Strict}}$ ↦ `IsIso (σ.naturality f)` for all `f` iff
  `IsIso (OplaxData.str (OplaxMor.toOplaxData (e σ)) B)` for all `B` (strong morphisms), and
  `σ.naturality f = eqToHom h` for all `f` iff
  `OplaxData.str (OplaxMor.toOplaxData (e σ)) B = eqToHom h` for all `B` (strict morphisms).

**Deviations.**
- stronger: stated for pseudofunctors out of an arbitrary bicategory `A` rather than strict
  2-functors out of a strict 2-category, and includes the strong and strict characterizations on
  the oplax side (`docs/STATE.yml`, deviations).
-/
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
        ∀ B, ∃ h, (e σ).str B = eqToHom h) := sorry

end UlmerBialgebras.Paper
