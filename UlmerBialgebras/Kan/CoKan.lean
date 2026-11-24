module

public import UlmerBialgebras.Models.Co
public import UlmerBialgebras.Kan.Kan

/-!
# Kan extensions in `K^co`

A left extension of `d` along `k` in `K^co` is a 1-cell `l` with a 2-cell `d ⟹ k l` of `K^co`,
that is, a 2-cell `k l ⟹ d` of `K`: a right extension in `K`. A morphism of left extensions in
`K^co` is a morphism of the corresponding right extensions in `K`, in the opposite direction.
Hence initial left extensions in `K^co` are terminal right extensions in `K`, and a 1-cell
preserves (strictly creates) left Kan extensions in `K^co` exactly when it preserves (strictly
creates) right Kan extensions in `K`.

This turns every statement about right Kan extensions into the corresponding statement about left
Kan extensions applied to `K^co`: the paper's "the cases for right Kan extensions follow dually".

## Main results

* `UlmerBialgebras.Co.preservesLeftKan_iff`: a 1-cell preserves left Kan extensions in `K^co` iff it
  preserves right Kan extensions in `K`.
* `UlmerBialgebras.Co.strictlyCreatesLeftKan_iff`: a 1-cell strictly creates left Kan extensions in
  `K^co` iff it strictly creates right Kan extensions in `K`.
* `UlmerBialgebras.Co.jointlyStrictlyCreatesInitial_iff`,
  `UlmerBialgebras.Co.jointlyStrictlyCreatesQuotientInitial_iff`: the corresponding statements for
  joint strict creation.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 4.2, 4.4 and Theorem 4.7
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

namespace Co

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] {I X c c' : Obj}

/-- A left extension in `K^co` as a right extension in `K`. -/
def toRight {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt (Obj := Co Obj) (hom k) (hom d)) :
    RightExt k d := RightExt.mk L.ext L.unit

/-- A right extension in `K` as a left extension in `K^co`. -/
def ofRight {k : I ⟶ X} {d : I ⟶ c} (R : RightExt k d) :
    LeftExt (Obj := Co Obj) (hom k) (hom d) := LeftExt.mk R.ext R.counit
/-- `toRight` undoes `ofRight`. -/
@[simp] lemma toRight_ofRight {k : I ⟶ X} {d : I ⟶ c} (R : RightExt k d) :
    toRight (ofRight R) = R := rfl

/-- `ofRight` undoes `toRight`. -/
@[simp] lemma ofRight_toRight {k : I ⟶ X} {d : I ⟶ c}
    (L : LeftExt (Obj := Co Obj) (hom k) (hom d)) : ofRight (toRight L) = L := rfl

/-- `toRight` is injective. -/
lemma toRight_inj {k : I ⟶ X} {d : I ⟶ c} {L M : LeftExt (Obj := Co Obj) (hom k) (hom d)} :
    toRight L = toRight M ↔ L = M :=
  ⟨fun h => by rw [← ofRight_toRight L, h, ofRight_toRight], fun h => h ▸ rfl⟩

/-- `ofRight` is injective. -/
lemma ofRight_inj {k : I ⟶ X} {d : I ⟶ c} {R R' : RightExt k d} :
    ofRight R = ofRight R' ↔ R = R' :=
  ⟨fun h => by rw [← toRight_ofRight R, h, toRight_ofRight], fun h => h ▸ rfl⟩


/-- Initial left extensions in `K^co` are terminal right extensions in `K`. -/
lemma isInitial_iff {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt (Obj := Co Obj) (hom k) (hom d)) :
    Nonempty (IsInitial L) ↔ Nonempty (IsTerminal (toRight L)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨IsTerminal.ofUniqueHom
      (fun Y => RightExt.homMk (LeftExt.homCell (h.to (ofRight Y))) (LeftExt.w (h.to (ofRight Y))))
      (fun Y m => RightExt.hom_ext (LeftExt.hom_ext_iff.mp
        (h.hom_ext (LeftExt.homMk (RightExt.homCell m) (RightExt.w m) : L ⟶ ofRight Y)
          (h.to (ofRight Y)))))⟩
  · rintro ⟨h⟩
    exact ⟨IsInitial.ofUniqueHom
      (fun Y => LeftExt.homMk (RightExt.homCell (h.from (toRight Y)))
        (RightExt.w (h.from (toRight Y))))
      (fun Y m => LeftExt.hom_ext (RightExt.hom_ext_iff.mp
        (h.hom_ext (RightExt.homMk (LeftExt.homCell m) (LeftExt.w m) : toRight Y ⟶ toRight L)
          (h.from (toRight Y)))))⟩

/-- Quotient-initial left extensions in `K^co` are subterminal right extensions in `K`. -/
lemma quotientInitial_iff {k : I ⟶ X} {d : I ⟶ c}
    (L : LeftExt (Obj := Co Obj) (hom k) (hom d)) :
    QuotientInitial L ↔ Subterminal (toRight L) := by
  constructor
  · intro h R a b
    exact RightExt.hom_ext (LeftExt.hom_ext_iff.mp
      ((h (ofRight R)).elim (LeftExt.homMk (RightExt.homCell a) (RightExt.w a) : L ⟶ ofRight R)
        (LeftExt.homMk (RightExt.homCell b) (RightExt.w b))))
  · intro h M
    exact ⟨fun a b => LeftExt.hom_ext (RightExt.hom_ext_iff.mp
      (h (RightExt.homMk (LeftExt.homCell a) (LeftExt.w a) : toRight M ⟶ toRight L)
        (RightExt.homMk (LeftExt.homCell b) (LeftExt.w b))))⟩

/-- Post-composition in `K^co` corresponds to post-composition in `K`. -/
lemma toRight_push (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')
    (L : LeftExt (Obj := Co Obj) (hom k) (hom d)) :
    toRight ((LeftExt.push (Obj := Co Obj) (hom k) (hom d) (hom f)).obj L) =
      (RightExt.push k d f).obj (toRight L) := by
  refine RightExt.eq_of_ext_eq rfl ?_
  change _ = (L.unit ▷ hom f) ≫ eqToHom (Category.assoc (hom k) L.ext (hom f))
  rw [comp_eq, eqToHom_eq]
  simp
  rfl

/-- `f` preserves left Kan extensions in `K^co` iff it preserves right Kan extensions in `K`. -/
theorem preservesLeftKan_iff (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') :
    PreservesLeftKan (Obj := Co Obj) (hom k) (hom d) (hom f) ↔ PreservesRightKan k d f := by
  constructor
  · intro h R hR
    have := h (ofRight R) ((isInitial_iff _).2 hR)
    rw [isInitial_iff, toRight_push] at this
    exact this
  · intro h L hL
    rw [isInitial_iff, toRight_push]
    exact h _ ((isInitial_iff L).1 hL)

/-- `f` strictly creates left Kan extensions in `K^co` iff it strictly creates right Kan
extensions in `K`. -/
theorem strictlyCreatesLeftKan_iff (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') :
    StrictlyCreatesLeftKan (Obj := Co Obj) (hom k) (hom d) (hom f) ↔
      StrictlyCreatesRightKan k d f := by
  have key : ∀ (L : LeftExt (Obj := Co Obj) (hom k) (hom d))
      (M : LeftExt (Obj := Co Obj) (hom k) (hom (d ≫ f))),
      (LeftExt.push (Obj := Co Obj) (hom k) (hom d) (hom f)).obj L = M ↔
        (RightExt.push k d f).obj (toRight L) = toRight M := by
    intro L M
    rw [← toRight_push]
    exact toRight_inj.symm
  constructor
  · intro h R hR
    obtain ⟨⟨L, hL, hu⟩, hi⟩ := h (ofRight R) ((isInitial_iff _).2 hR)
    refine ⟨⟨toRight L, (key L (ofRight R)).1 hL, fun R' hR' => ?_⟩, fun R' hR' => ?_⟩
    · exact toRight_inj.mpr (hu (ofRight R') ((key _ _).2 hR'))
    · exact (isInitial_iff (ofRight R')).1 (hi _ ((key _ _).2 hR'))
  · intro h M hM
    obtain ⟨⟨R, hR, hu⟩, hi⟩ := h (toRight M) ((isInitial_iff M).1 hM)
    refine ⟨⟨ofRight R, (key _ _).2 hR, fun L hL => ?_⟩, fun L hL => ?_⟩
    · exact ofRight_inj.mpr (hu (toRight L) ((key _ _).1 hL))
    · exact (isInitial_iff L).2 (hi _ ((key _ _).1 hL))

/-- Joint creation of initial left extensions in `K^co` is joint creation of terminal
right extensions in `K`. -/
theorem jointlyStrictlyCreatesInitial_iff {ι : Type*} {cs : ι → Obj}
    (k : I ⟶ X) (d : I ⟶ c) (f : ∀ i, c ⟶ cs i) :
    JointlyStrictlyCreatesInitial
      (fun i => LeftExt.push (Obj := Co Obj) (hom k) (hom d) (hom (f i))) ↔
    JointlyStrictlyCreatesTerminal (fun i => RightExt.push k d (f i)) := by
  have key : ∀ (L : LeftExt (Obj := Co Obj) (hom k) (hom d))
      (b : ∀ i, LeftExt (Obj := Co Obj) (hom k) (hom (d ≫ f i))),
      (∀ i, (LeftExt.push (Obj := Co Obj) (hom k) (hom d) (hom (f i))).obj L = b i) ↔
      (∀ i, (RightExt.push k d (f i)).obj (toRight L) = toRight (b i)) := by
    intro L b
    apply forall_congr'
    intro i
    rw [← toRight_push]
    exact toRight_inj.symm
  constructor
  · intro h b hb
    have hbi : Nonempty (IsInitial (fun i => ofRight (b i))) :=
      ⟨isInitialPi (fun i =>
        ((isInitial_iff (ofRight (b i))).2 ⟨isTerminalPiApply hb.some i⟩).some)⟩
    obtain ⟨⟨L, hL, hu⟩, hi⟩ := h (fun i => ofRight (b i)) hbi
    refine ⟨⟨toRight L, (key L _).1 hL, fun R hR => ?_⟩, fun R hR => ?_⟩
    · exact toRight_inj.mpr (hu (ofRight R) ((key _ _).2 hR))
    · exact (isInitial_iff (ofRight R)).1 (hi _ ((key _ _).2 hR))
  · intro h b hb
    have hbt : Nonempty (IsTerminal (fun i => toRight (b i))) :=
      ⟨isTerminalPi (fun i => ((isInitial_iff _).1 ⟨isInitialPiApply hb.some i⟩).some)⟩
    obtain ⟨⟨R, hR, hu⟩, hi⟩ := h (fun i => toRight (b i)) hbt
    refine ⟨⟨ofRight R, (key _ _).2 hR, fun L hL => ?_⟩, fun L hL => ?_⟩
    · exact ofRight_inj.mpr (hu (toRight L) ((key _ _).1 hL))
    · exact (isInitial_iff L).2 (hi _ ((key _ _).1 hL))

/-- Joint strict creation of quotient-initial left extensions in `K^co` is joint strict creation of
subterminal right extensions in `K`. -/
theorem jointlyStrictlyCreatesQuotientInitial_iff {ι : Type*} {cs : ι → Obj}
    (k : I ⟶ X) (d : I ⟶ c) (f : ∀ i, c ⟶ cs i) :
    JointlyStrictlyCreatesQuotientInitial
      (fun i => LeftExt.push (Obj := Co Obj) (hom k) (hom d) (hom (f i))) ↔
    JointlyStrictlyCreatesSubterminal (fun i => RightExt.push k d (f i)) := by
  have key : ∀ (L : LeftExt (Obj := Co Obj) (hom k) (hom d))
      (b : ∀ i, LeftExt (Obj := Co Obj) (hom k) (hom (d ≫ f i))),
      (∀ i, (LeftExt.push (Obj := Co Obj) (hom k) (hom d) (hom (f i))).obj L = b i) ↔
      (∀ i, (RightExt.push k d (f i)).obj (toRight L) = toRight (b i)) := by
    intro L b
    apply forall_congr'
    intro i
    rw [← toRight_push]
    exact toRight_inj.symm
  constructor
  · intro h b hb
    obtain ⟨⟨L, hL, hu⟩, hi⟩ :=
      h (fun i => ofRight (b i)) (fun i => (quotientInitial_iff (ofRight (b i))).2 (hb i))
    refine ⟨⟨toRight L, (key L _).1 hL, fun R hR => ?_⟩, fun R hR => ?_⟩
    · exact toRight_inj.mpr (hu (ofRight R) ((key _ _).2 hR))
    · exact (quotientInitial_iff (ofRight R)).1 (hi _ ((key _ _).2 hR))
  · intro h b hb
    obtain ⟨⟨R, hR, hu⟩, hi⟩ :=
      h (fun i => toRight (b i)) (fun i => (quotientInitial_iff (b i)).1 (hb i))
    refine ⟨⟨ofRight R, (key _ _).2 hR, fun L hL => ?_⟩, fun L hL => ?_⟩
    · exact ofRight_inj.mpr (hu (toRight L) ((key _ _).1 hL))
    · exact (quotientInitial_iff L).2 (hi _ ((key _ _).1 hL))

end Co

end UlmerBialgebras
