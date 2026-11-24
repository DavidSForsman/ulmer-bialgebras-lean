module

public import UlmerBialgebras.Paper.Sec3DefsMonadAlgObject

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Remark 3.17: the universal property of `M^T`

`M^T` represents `K(-, M)^T`, and this characterizes it up to isomorphism. No assumption is made on
the 2-category `K` beyond chosen finite products (nullary ones included), which a `Σ`-model needs:
the products, inserter and equifier that form `M^T` are given as data.

## Main statements

* `UlmerBialgebras.Paper.rem_3_17_unique`: two representing pairs give isomorphic objects,
  compatibly with the isomorphisms of categories (strict 2-categorical Yoneda).
* `UlmerBialgebras.Paper.rem_3_17_exists`: `M^T`, built from given limits (`Model.thyObjOf`), with
  the canonical comparison functors, represents `K(-, M)^T`.
* `UlmerBialgebras.Paper.rem_3_17_em`: for a monad and a pair `(u, η)` satisfying the algebra
  equations, the paper's (1) and (2) hold iff `(d, u, η)` represents `M^{T_Lax}`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17
* [R. Street, *The formal theory of monads*][STREET1972149]
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]

section General

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{w, v}] [HasChosenProductsOfSize.{s₂} Cat.{w, v}]
  [HasChosenInserters Cat.{w, v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{w, v}] [HasChosenEquifiers Cat.{w, v}]

/-- **Remark 3.17, uniqueness** ([forsman2026syntactic], §3).

```latex
By the $2$-categorical Yoneda lemma, $M^T$ is characterized up to isomorphism by an isomorphism
of categories $\K(x,M^T)\cong\K(x,M)^T$, natural in $x$, where $\K(x,M)$ is the $\Sigma$-model
in $\CAT$ induced by $M$.
```

**Reading.**
* $2$-category $\K$ ↦ `Obj` with `[Bicategory.{w, v} Obj] [Bicategory.Strict Obj]` and
  `[HasChosenFinProducts.{u, v, w} Obj]`.
* $\Sigma$-model $M$ and $\sigma$-theory $T$ ↦ `M : Model Sg Obj`, `sg : OneSig Sg`,
  `T : Theory sg`.
* induced model $\K(x, M)$ in $\CAT$ ↦ `M.homModel x`.
* representing pairs $(E, \Phi)$ and $(E', \Phi')$ for $\K(x, M^T) \cong \K(x, M)^T$ natural in
  $x$ ↦ `h : IsThyRep M sg T E Φ`, `h' : IsThyRep M sg T E' Φ'`.
* "characterized up to isomorphism" ↦ mutually inverse 1-cells `i : E ⟶ E'` and `j : E' ⟶ E`
  with `i ≫ j = 𝟙 E`, `j ≫ i = 𝟙 E'`, and
  `CategoryTheory.Functor.toCatHom (postcomp x i) ≫ Φ' x = Φ x` for every `x : Obj`.

**Deviations.** none recorded.
-/
theorem rem_3_17_unique {E E' : Obj} {Φ : ∀ x : Obj, Cat.of (x ⟶ E) ⟶ (M.homModel x).thyObj sg T}
    {Φ' : ∀ x : Obj, Cat.of (x ⟶ E') ⟶ (M.homModel x).thyObj sg T}
    (h : IsThyRep M sg T E Φ) (h' : IsThyRep M sg T E' Φ') :
    ∃ (i : E ⟶ E') (j : E' ⟶ E), i ≫ j = 𝟙 E ∧ j ≫ i = 𝟙 E' ∧
      ∀ x : Obj, (postcomp x i).toCatHom ≫ Φ' x = Φ x :=
  sorry

/-- **Remark 3.17, existence** ([forsman2026syntactic], §3).

```latex
By the $2$-categorical Yoneda lemma, $M^T$ is characterized up to isomorphism by an isomorphism
of categories $\K(x,M^T)\cong\K(x,M)^T$, natural in $x$, where $\K(x,M)$ is the $\Sigma$-model
in $\CAT$ induced by $M$.
```

**Reading.**
* PIE limits forming $M^T$ given as data in $\K$ ↦ sort product `P₀`, function-symbol product
  `Pfn`, inserter `I`, equation product `Peq`, and equifier `Q`.
* object of bialgebras $M^T$ ↦ `M.thyObjOf sg P₀ Pfn I T Peq Q`.
* category of bialgebras $\K(x, M)^T$ ↦ `Model.thyObj (M.homModel x) sg T`.
* natural isomorphism of categories $\K(x, M^T) \cong \K(x, M)^T$ ↦
  `IsThyRep M sg T (M.thyObjOf sg P₀ Pfn I T Peq Q)` with comparison functors
  `M.algComparison x sg T (M.canonAlg sg T P₀ Pfn I Peq Q)`.

**Deviations.** none recorded.
-/
theorem rem_3_17_exists (P₀ : Product (fun s : sg.Srt => M.obj (sg.sty s)))
    (Pfn : Product (fun f : sg.Fn => M.obj (sg.fnty f)))
    (I : Inserter (M.domCellOf sg P₀ Pfn) (M.codCellOf sg P₀ Pfn))
    (Peq : Product (fun r : T.Eqn => M.obj (T.eqty r)))
    (Q : Equifier (M.lhsCellOf sg P₀ Pfn I T Peq) (M.rhsCellOf sg P₀ Pfn I T Peq)) :
    IsThyRep M sg T (M.thyObjOf sg P₀ Pfn I T Peq Q)
      (fun x => M.algComparison x sg T (M.canonAlg sg T P₀ Pfn I Peq Q)) :=
  sorry

end General

section MonadAlgebras

variable [HasChosenProductsOfSize.{0} Cat.{w, v}] [HasChosenInserters Cat.{w, v}]
  [HasChosenEquifiers Cat.{w, v}] {c : Obj} (t : c ⟶ c) (m : t ≫ t ⟶ t) (e : 𝟙 c ⟶ t)

/-- **Remark 3.17, the Eilenberg–Moore object** ([forsman2026syntactic], §3;
Street [STREET1972149]).

```latex
For example, let $(t\colon c\to c,m\colon tt\Rightarrow t,e\colon \id_c\Rightarrow t)$ be a
monad in $\K$. Its (strict) Eilenberg--Moore object \cite{STREET1972149} is a triple
$(d,u\colon d\to c,\eta\colon tu\Rightarrow u)$ satisfying $\eta\bullet mu=\eta\bullet t\eta$
and $\eta\bullet eu=\id_u$, such that:
\begin{enumerate}
    \item for every triple $(x,h'\colon x\to c,\psi\colon th'\Rightarrow h')$ satisfying the
    same two equations, there is a unique $h\colon x\to d$ with $h' = uh$ and $\psi = \eta h$;
    \item for all $h_1,h_2\colon x\to d$ and every $\beta\colon uh_1\Rightarrow uh_2$ with
    $\eta h_2\bullet t\beta=\beta\bullet\eta h_1$, there is a unique $\theta\colon h_1\Rightarrow
    h_2$ with $u\theta=\beta$.
\end{enumerate}
```

**Reading.**
* monad $(t\colon c\to c, m\colon tt\Rightarrow t, e\colon \id_c\Rightarrow t)$ in $\K$ ↦
  `t : c ⟶ c`, `m : t ≫ t ⟶ t`, `e : 𝟙 c ⟶ t`, with $\Sigma_{\mathrm{Mnd}}$-model
  `MndK.model t m e`.
* triple $(d, u\colon d\to c, \eta\colon tu\Rightarrow u)$ satisfying the algebra equations ↦
  `d : Obj`, `u : d ⟶ c`, `η : u ≫ t ⟶ u`, `hη : MndK.IsAlg t m e u η`.
* item (1) ↦ for every `h' : x ⟶ c` and `ψ : h' ≫ t ⟶ h'` with `MndK.IsAlg t m e h' ψ`, unique
  `h : x ⟶ d` with `hh : h ≫ u = h'` and `ψ = eqToHom _ ≫ h ◁ η ≫ eqToHom hh`.
* item (2) ↦ for all `h₁ h₂ : x ⟶ d` and `β : h₁ ≫ u ⟶ h₂ ≫ u` compatible with `η`, unique
  `θ : h₁ ⟶ h₂` with `θ ▷ u = β`.
* equivalence with the universal property of $M^{T_{\mathrm{Lax}}}$ ↦ items (1) and (2) hold iff
  `IsThyRep (MndK.model t m e) MndK.σL MndK.TL d` holds for the comparison functors of
  `MndK.emAlg t m e u η hη`.

**Deviations.** none recorded.
-/
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
          (MndK.emAlg t m e u η hη)) :=
  sorry

end MonadAlgebras

end UlmerBialgebras.Paper
