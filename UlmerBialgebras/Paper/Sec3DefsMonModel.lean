module

public import UlmerBialgebras.Examples.MonModel

/-!
# The operations of an arbitrary `Σ_Mon`-model in `CAT`

Examples 3.20 (1) of *A Syntactic Approach to Ulmer's Bialgebras* fix the 2-signature
`Σ = (c, □ : cc → c, I : () → c, α : (x□y)□z → x□(y□z), ρ : x□I → x, λ : I□x → x)`
(`UlmerBialgebras.MonEx.twoSig`) and the relative 1-signature `σ = (s : c, µ : s□s → s, u : I → s)`
(`UlmerBialgebras.MonEx.oneSig`). For an arbitrary `Σ`-model `M` in `CAT`, not necessarily a
monoidal category, the paper writes `⊗ := M(□)` and `I := M(I)(*)`, and describes the objects of
`M^σ` as the pointed magmas `(x, m : x ⊗ x → x, e : I → x)`. This file provides that notation.

* `tensObj x y = x ⊗ y` and `tensHom f g = f ⊗ g`: the functor `M(□) : ∏_{i < 2} M_c → M_c`
  at a pair of objects and at a pair of morphisms.
* `unitObj M = I`: the functor `M(I) : ∏_{i < 0} M_c → M_c` at the unique object `*`.
* `assocApp x y z = M(α)_{x,y,z}`, `runitApp x = M(ρ)_x` and `lunitApp x = M(λ)_x`: the components
  of the 2-cells interpreting the transformation symbols.
* `ob z = x`, `mul z = m` and `one z = e` for an object `z` of `M^σ`.

The interpretation of a term is defined by recursion on the term. For example, the source of
`M(α)` at `(x, y, z)` is the interpretation of the term `(x□y)□z` at `(x, y, z)`. This object is
equal to `(x ⊗ y) ⊗ z`, but not definitionally: the pair `(x ⊗ y, z)` is presented by two
different functions on `Fin 2`. The components `assocApp`, `runitApp`, `lunitApp`, `mul` and `one`
are therefore composed with the identity morphisms `eqToHom` along these equalities of objects.
These are the identifications that the paper makes implicitly.

The examples in `UlmerBialgebrasTest.NonVacuity.MonModelOps` check that, for the monoidal model
`UlmerBialgebras.MonEx.monModel C` of a monoidal category `C`, this notation gives the tensor
product, the unit object, the associator and the unitors of `C`, and the structure morphisms of an
object of `M^σ`.

## Main results

* `UlmerBialgebras.Paper.MonModel.tensObj`, `UlmerBialgebras.Paper.MonModel.tensHom`,
  `UlmerBialgebras.Paper.MonModel.unitObj`: the notation `x ⊗ y`, `f ⊗ g` and `I` for a `Σ`-model
  `M`.
* `UlmerBialgebras.Paper.MonModel.assocApp`, `UlmerBialgebras.Paper.MonModel.runitApp`,
  `UlmerBialgebras.Paper.MonModel.lunitApp`: the components of `M(α)`, `M(ρ)` and `M(λ)`.
* `UlmerBialgebras.Paper.MonModel.ob`, `UlmerBialgebras.Paper.MonModel.mul`,
  `UlmerBialgebras.Paper.MonModel.one`: the pointed magma `(x, m, e)` underlying an object of `M^σ`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (1)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper.MonModel

open CategoryTheory

variable {M : Model MonEx.twoSig Cat.{v, max u v}}

/-- The pair `(f, g)` of morphisms `f : x ⟶ x'`, `g : y ⟶ y'` of `M_c`, as a morphism
`(x, y) ⟶ (x', y')` of the product category `∏_{i < 2} M_c` (whose objects are functions on
`Fin 2`). -/
def pairHom {x x' y y' : (M.obj () : Type (max u v))} (f : x ⟶ x') (g : y ⟶ y') :
    ((![x, y] : Fin 2 → (M.obj () : Type (max u v))) ⟶ ![x', y']) :=
  Fin.cons f (Fin.cons g finZeroElim)

variable (M) in
/-- The unit object `I = M(I)(*)` of a `Σ_Mon`-model `M` in `CAT`: the functor `M(I)` at the
unique object `*` of the empty product `∏_{i < 0} M_c`. -/
def unitObj : (M.obj () : Type (max u v)) := (M.fn MonEx.FunSym.unit).toFunctor.obj finZeroElim

/-- The tensor product `x ⊗ y = M(□)(x, y)` of two objects of `M_c`. -/
def tensObj (x y : (M.obj () : Type (max u v))) : (M.obj () : Type (max u v)) :=
  (M.fn MonEx.FunSym.tens).toFunctor.obj ![x, y]

/-- The tensor product `f ⊗ g = M(□)(f, g) : x ⊗ y ⟶ x' ⊗ y'` of two morphisms of `M_c`. -/
def tensHom {x x' y y' : (M.obj () : Type (max u v))} (f : x ⟶ x') (g : y ⟶ y') :
    tensObj x y ⟶ tensObj x' y' :=
  (M.fn MonEx.FunSym.tens).toFunctor.map (pairHom f g)

/-- The component `M(α)_{x,y,z} : (x ⊗ y) ⊗ z ⟶ x ⊗ (y ⊗ z)` of the 2-cell `M(α)` interpreting
the associator, at the triple `(x, y, z)`. The component `(M.tr α).toNatTrans.app (x, y, z)` goes
    from the
interpretation of the term `(x□y)□z` at `(x, y, z)` to that of `x□(y□z)`; these objects equal
`(x ⊗ y) ⊗ z` and `x ⊗ (y ⊗ z)`, and it is composed with the identities `eqToHom` along these
equalities. -/
def assocApp (x y z : (M.obj () : Type (max u v))) :
    tensObj (tensObj x y) z ⟶ tensObj x (tensObj y z) :=
  eqToHom (congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj (funext (Fin.forall_fin_two.2
      ⟨congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj
        (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)), rfl⟩)) :
        tensObj (tensObj x y) z = (M.interp (M.Pctx MonEx.TrSym.assoc).π
          (MonEx.twoSig.trsrc MonEx.TrSym.assoc)).toFunctor.obj ![x, y, z]) ≫
    (M.tr MonEx.TrSym.assoc).toNatTrans.app ![x, y, z] ≫
    eqToHom (congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj (funext (Fin.forall_fin_two.2
      ⟨rfl, congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj
        (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))⟩)) :
        tensObj x (tensObj y z) = (M.interp (M.Pctx MonEx.TrSym.assoc).π
          (MonEx.twoSig.trtgt MonEx.TrSym.assoc)).toFunctor.obj ![x, y, z]).symm

/-- The component `M(ρ)_x : x ⊗ I ⟶ x` of the 2-cell `M(ρ)` interpreting the right unitor, at
`x`. The source of `(M.tr ρ).toNatTrans.app (x)`, the interpretation of the term `x□I` at `x`,
    equals
`x ⊗ I`; its target is `x`. -/
def runitApp (x : (M.obj () : Type (max u v))) : tensObj x (unitObj M) ⟶ x :=
  eqToHom (congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj (funext (Fin.forall_fin_two.2
      ⟨rfl, congrArg (M.fn MonEx.FunSym.unit).toFunctor.obj
        (funext fun j => Fin.elim0 j)⟩)) :
        tensObj x (unitObj M) = (M.interp (M.Pctx MonEx.TrSym.runit).π
          (MonEx.twoSig.trsrc MonEx.TrSym.runit)).toFunctor.obj ![x]) ≫
    (M.tr MonEx.TrSym.runit).toNatTrans.app ![x]

/-- The component `M(λ)_x : I ⊗ x ⟶ x` of the 2-cell `M(λ)` interpreting the left unitor, at
`x`. The source of `(M.tr λ).toNatTrans.app (x)`, the interpretation of the term `I□x` at `x`,
    equals
`I ⊗ x`; its target is `x`. -/
def lunitApp (x : (M.obj () : Type (max u v))) : tensObj (unitObj M) x ⟶ x :=
  eqToHom (congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj (funext (Fin.forall_fin_two.2
      ⟨congrArg (M.fn MonEx.FunSym.unit).toFunctor.obj
        (funext fun j => Fin.elim0 j), rfl⟩)) :
        tensObj (unitObj M) x = (M.interp (M.Pctx MonEx.TrSym.lunit).π
          (MonEx.twoSig.trsrc MonEx.TrSym.lunit)).toFunctor.obj ![x]) ≫
    (M.tr MonEx.TrSym.lunit).toNatTrans.app ![x]

/-! ## The objects of `M^σ` -/

/-- The underlying object `x` of an object `z` of `M^σ`, the inserter
`Ins((M(s□s), M(I)), (M(s), M(s)))`: the component of `u_M(z) ∈ M₀ = ∏_{s} M_c` at the unique
sort `s`. -/
def ob (z : (M.sigObj MonEx.oneSig : Type (max u v))) : (M.obj () : Type (max u v)) := Ins.pt z ()

/-- The multiplication `m : x ⊗ x ⟶ x` of an object `z = (x, m, e)` of `M^σ`: the component at
the function symbol `µ` of its structure morphism, whose source `M(s□s)(x)` equals `x ⊗ x`. -/
def mul (z : (M.sigObj MonEx.oneSig : Type (max u v))) : tensObj (ob z) (ob z) ⟶ ob z :=
  eqToHom (congrArg (M.fn MonEx.FunSym.tens).toFunctor.obj
      (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)) :
    tensObj (ob z) (ob z) = (M.domCell MonEx.oneSig).toFunctor.obj z.pt MonEx.FnSym.mul) ≫
    Ins.cell z MonEx.FnSym.mul

/-- The unit `e : I ⟶ x` of an object `z = (x, m, e)` of `M^σ`: the component at the function
symbol `u` of its structure morphism, whose source `M(I)(x)` equals `I`. -/
def one (z : (M.sigObj MonEx.oneSig : Type (max u v))) : unitObj M ⟶ ob z :=
  eqToHom (congrArg (M.fn MonEx.FunSym.unit).toFunctor.obj (funext fun j => j.elim0)) ≫
    Ins.cell z MonEx.FnSym.one

end UlmerBialgebras.Paper.MonModel
