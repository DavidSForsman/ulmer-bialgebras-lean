module

public import UlmerBialgebras.Paper.Sec6DefsTheoryMorphism
public import UlmerBialgebras.Paper.Sec6DefsGrp

/-!
# Theories of universal algebra extending the theory of groups, and their paths

Corollary 6.11 of [forsman2026syntactic] speaks of "a multi-sorted theory of universal algebra
extending the theory of groups in each sort". This file sets up that notion for `MSLanguage`:

* `grpExtLanguage S Fn' …`: the language of groups in each sort of `S`, with further function
  symbols `Fn'`;
* `grpInl`: the inclusion of the language of groups;
* a theory `T` over `grpExtLanguage S Fn' …` extends the theory of groups when it contains the
  translated group axioms (`∀ φ ∈ grpEqTheory S, grpInl.translateEquation φ ∈ T`).

It also proves the syntactic fact that the proof of Corollary 6.11 needs: the path of a term of
the language of groups, pushed into the larger term graph, is the path of the translated term
(`ofRestrictFn_toPath`). The generic lemmas say that `OneSig.Path.ofRestrictFn` commutes with
the path combinators of `Σ_Cart`.

## Main results

* `UlmerBialgebras.Paper.UniversalAlgebra.grpExtLanguage`, `grpInl`.
* `UlmerBialgebras.Paper.UniversalAlgebra.ofRestrictFn_toPath`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.11
-/

@[expose] public section

universe u₁

namespace UlmerBialgebras.Paper.UniversalAlgebra

open CategoryTheory Cart MSLanguage

/-! ## `ofRestrictFn` commutes with the path combinators -/

section Generic

variable {sg : OneSig sigCart} {Fn₁ : Type*} (jFn : Fn₁ → sg.Fn)

/-- Pushing a composite path is the composite of the pushed paths. -/
lemma ofRestrictFn_comp {c : Unit} :
    ∀ {t t' t'' : sg.CTrm c} (p : (sg.restrictFn jFn).Path t t')
      (q : (sg.restrictFn jFn).Path t' t''),
      OneSig.Path.ofRestrictFn jFn (p.comp q) =
        (OneSig.Path.ofRestrictFn jFn p).comp (OneSig.Path.ofRestrictFn jFn q)
  | _, _, _, .nil _, _ => by simp [OneSig.Path.comp, OneSig.Path.ofRestrictFn]
  | _, _, _, .cons g p, q => by
    simp [OneSig.Path.comp, OneSig.Path.ofRestrictFn, ofRestrictFn_comp p q]

/-- Pushing a transported arrow is transporting the pushed arrow. -/
lemma ofRestrictFn_transport {c : Unit} {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁')
    (h₂ : t₂ = t₂') (a : (sg.restrictFn jFn).Arr t₁ t₂) :
    OneSig.Arr.ofRestrictFn jFn (OneSig.Arr.transport h₁ h₂ a) =
      OneSig.Arr.transport h₁ h₂ (OneSig.Arr.ofRestrictFn jFn a) := by
  subst h₁ h₂
  rfl

/-- Pushing the diagonal. -/
lemma ofRestrictFn_diagPath (t : sg.CTrm ()) :
    OneSig.Path.ofRestrictFn jFn (diagPath (sg := sg.restrictFn jFn) t) = diagPath t :=
  congrArg (fun a => OneSig.Path.cons a (.nil _)) (ofRestrictFn_transport jFn _ _ _)

/-- Pushing the first projection. -/
lemma ofRestrictFn_fstPath (a b : sg.CTrm ()) :
    OneSig.Path.ofRestrictFn jFn (fstPath (sg := sg.restrictFn jFn) a b) = fstPath a b :=
  congrArg (fun a => OneSig.Path.cons a (.nil _)) (ofRestrictFn_transport jFn _ _ _)

/-- Pushing the second projection. -/
lemma ofRestrictFn_sndPath (a b : sg.CTrm ()) :
    OneSig.Path.ofRestrictFn jFn (sndPath (sg := sg.restrictFn jFn) a b) = sndPath a b :=
  congrArg (fun a => OneSig.Path.cons a (.nil _)) (ofRestrictFn_transport jFn _ _ _)

/-- Pushing the terminal map. -/
lemma ofRestrictFn_toUnitPath (t : sg.CTrm ()) :
    OneSig.Path.ofRestrictFn jFn (toUnitPath (sg := sg.restrictFn jFn) t) = toUnitPath t :=
  congrArg (fun a => OneSig.Path.cons a (.nil _)) (ofRestrictFn_transport jFn _ _ _)

/-- Pushing a path whiskered on the right. -/
lemma ofRestrictFn_whiskerRightPath (b : sg.CTrm ()) :
    ∀ {a t : sg.CTrm ()} (p : (sg.restrictFn jFn).Path a t),
      OneSig.Path.ofRestrictFn jFn (whiskerRightPath (sg := sg.restrictFn jFn) b p) =
        whiskerRightPath b (OneSig.Path.ofRestrictFn jFn p)
  | _, _, .nil _ => by simp [whiskerRightPath, OneSig.Path.ofRestrictFn]
  | _, _, .cons g p => by
    simp only [whiskerRightPath, OneSig.Path.ofRestrictFn, ofRestrictFn_whiskerRightPath b p]
    rfl

/-- Pushing a path whiskered on the left. -/
lemma ofRestrictFn_whiskerLeftPath (a : sg.CTrm ()) :
    ∀ {b t : sg.CTrm ()} (p : (sg.restrictFn jFn).Path b t),
      OneSig.Path.ofRestrictFn jFn (whiskerLeftPath (sg := sg.restrictFn jFn) a p) =
        whiskerLeftPath a (OneSig.Path.ofRestrictFn jFn p)
  | _, _, .nil _ => by simp [whiskerLeftPath, OneSig.Path.ofRestrictFn]
  | _, _, .cons g p => by
    simp only [whiskerLeftPath, OneSig.Path.ofRestrictFn, ofRestrictFn_whiskerLeftPath a p]
    rfl

/-- Pushing a pairing of paths. -/
lemma ofRestrictFn_liftPath {t a b : sg.CTrm ()} (p : (sg.restrictFn jFn).Path t a)
    (q : (sg.restrictFn jFn).Path t b) :
    OneSig.Path.ofRestrictFn jFn (liftPath p q) =
      liftPath (OneSig.Path.ofRestrictFn jFn p) (OneSig.Path.ofRestrictFn jFn q) := by
  simp only [liftPath, tensorPath, ofRestrictFn_comp, ofRestrictFn_diagPath,
    ofRestrictFn_whiskerRightPath, ofRestrictFn_whiskerLeftPath]

end Generic

/-! ## The language of groups with further symbols -/

section Lang

variable {S Fn' : Type u₁} {arity' : Fn' → ℕ} {argSorts' : ∀ f, Fin (arity' f) → S}
  {resSort' : Fn' → S}

/-- Restricting the term graph of `grpExtLanguage` to the group symbols gives the term graph of
the language of groups (definitionally). -/
lemma toCartSig_restrictFn_inl :
    (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig.restrictFn Sum.inl =
      (grpLanguage S).toCartSig := rfl

variable (Fn' arity' argSorts' resSort') in
/-- A path of the term graph of groups, pushed into the term graph of `grpExtLanguage`. -/
def pushGrp {t t' : (grpLanguage S).toCartSig.CTrm ()}
    (p : (grpLanguage S).toCartSig.Path t t') :
    (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig.Path t t' :=
  OneSig.Path.ofRestrictFn (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig)
    (Fn₁ := S × GrpFn) Sum.inl p

/-! The lemmas of `Generic` for `pushGrp`, with the paths typed in the term graph of groups. -/

/-- Pushing a composite path. -/
lemma pushGrp_comp {t t' t'' : (grpLanguage S).toCartSig.CTrm ()}
    (p : (grpLanguage S).toCartSig.Path t t') (q : (grpLanguage S).toCartSig.Path t' t'') :
    pushGrp Fn' arity' argSorts' resSort' (p.comp q) =
      (pushGrp Fn' arity' argSorts' resSort' p).comp (pushGrp Fn' arity' argSorts' resSort' q) :=
  ofRestrictFn_comp
    (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) Sum.inl p q

/-- Pushing the first projection. -/
lemma pushGrp_fstPath (a b : (grpLanguage S).toCartSig.CTrm ()) :
    pushGrp Fn' arity' argSorts' resSort' (fstPath a b) =
      fstPath (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) a b :=
  ofRestrictFn_fstPath
    (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) Sum.inl a b

/-- Pushing the second projection. -/
lemma pushGrp_sndPath (a b : (grpLanguage S).toCartSig.CTrm ()) :
    pushGrp Fn' arity' argSorts' resSort' (sndPath a b) =
      sndPath (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) a b :=
  ofRestrictFn_sndPath
    (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) Sum.inl a b

/-- Pushing the terminal map. -/
lemma pushGrp_toUnitPath (t : (grpLanguage S).toCartSig.CTrm ()) :
    pushGrp Fn' arity' argSorts' resSort' (toUnitPath t) =
      toUnitPath (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) t :=
  ofRestrictFn_toUnitPath
    (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) Sum.inl t

/-- Pushing a pairing of paths. -/
lemma pushGrp_liftPath {t a b : (grpLanguage S).toCartSig.CTrm ()}
    (p : (grpLanguage S).toCartSig.Path t a) (q : (grpLanguage S).toCartSig.Path t b) :
    pushGrp Fn' arity' argSorts' resSort' (liftPath p q) =
      liftPath (pushGrp Fn' arity' argSorts' resSort' p)
        (pushGrp Fn' arity' argSorts' resSort' q) :=
  ofRestrictFn_liftPath
    (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) Sum.inl p q

/-- Pushing a group function symbol. -/
lemma pushGrp_arrPath_fn (f : S × GrpFn) :
    pushGrp Fn' arity' argSorts' resSort'
        (arrPath (OneSig.Arr.fn (sg := (grpLanguage S).toCartSig) f)) =
      arrPath (OneSig.Arr.fn
        (sg := (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig) (.inl f)) :=
  rfl

/-- Pushing a projection of the term graph of groups gives the projection of the larger term
graph. -/
lemma ofRestrictFn_projPath : ∀ {n : ℕ} (a : Fin n → S) (i : Fin n),
    pushGrp Fn' arity' argSorts' resSort' (projPath (L := grpLanguage S) a i) =
      projPath (L := grpExtLanguage S Fn' arity' argSorts' resSort') a i
  | 0, _, i => i.elim0
  | 1, _, ⟨0, _⟩ => rfl
  | _ + 2, a, ⟨0, _⟩ => pushGrp_fstPath _ _
  | _ + 2, a, ⟨k + 1, h⟩ =>
    (pushGrp_comp (sndPath (sg := (grpLanguage S).toCartSig) (.var (a 0)) (prodTrm (Fin.tail a)))
      (projPath (L := grpLanguage S) (Fin.tail a) ⟨k, by omega⟩)).trans
      (congrArg₂ OneSig.Path.comp (pushGrp_sndPath (.var (a 0)) (prodTrm (Fin.tail a)))
        (ofRestrictFn_projPath (Fin.tail a) ⟨k, by omega⟩))

/-- Pushing a tuple of paths of the term graph of groups gives the tuple of the pushed paths. -/
lemma ofRestrictFn_tuplePath {t : (grpLanguage S).toCartSig.CTrm ()} :
    ∀ {m : ℕ} {b : Fin m → S} (p : ∀ j, (grpLanguage S).toCartSig.Path t (.var (b j))),
      pushGrp Fn' arity' argSorts' resSort' (tuplePath (L := grpLanguage S) p) =
        tuplePath (L := grpExtLanguage S Fn' arity' argSorts' resSort')
          (fun j => pushGrp Fn' arity' argSorts' resSort' (p j))
  | 0, _, _ => pushGrp_toUnitPath _
  | 1, _, _ => rfl
  | _ + 2, _, p =>
    (pushGrp_liftPath (p 0) (tuplePath (L := grpLanguage S) (fun j => p j.succ))).trans
      (congrArg (liftPath (pushGrp Fn' arity' argSorts' resSort' (p 0)))
        (ofRestrictFn_tuplePath (fun j => p j.succ)))

/-- **The path of a translated group term**: the path of a term of the language of groups,
pushed into the term graph of `grpExtLanguage`, is the path of the translated term. -/
lemma ofRestrictFn_toPath {n : ℕ} {Γ : Fin n → S} :
    ∀ {s : S} (t : (grpLanguage S).Term Γ s),
      pushGrp Fn' arity' argSorts' resSort' t.toPath =
        ((grpInl S Fn' arity' argSorts' resSort').translate t).toPath
  | _, .var i => ofRestrictFn_projPath Γ i
  | _, .func f ts =>
    (pushGrp_comp (tuplePath (L := grpLanguage S) (fun j => (ts j).toPath))
      (arrPath (OneSig.Arr.fn (sg := (grpLanguage S).toCartSig) f))).trans
      (congrArg₂ OneSig.Path.comp
        ((ofRestrictFn_tuplePath (fun j => (ts j).toPath)).trans
          (congrArg tuplePath (funext fun j => ofRestrictFn_toPath (ts j))))
        (pushGrp_arrPath_fn f))

end Lang

end UlmerBialgebras.Paper.UniversalAlgebra
