module

public import Hopf.Coradical.PointedDecomposition
public import Mathlib.Algebra.Order.Ring.Star
public import Hopf.Coradical.Exhaustive
public import Hopf.Coradical.Transfer

/-!
# Kostant's decomposition theorem for arbitrary cocommutative coalgebras

`Hopf/Coradical/PointedDecomposition.lean` proves, for a *finite-dimensional* cocommutative
coalgebra `C` over a field, that `C` is the direct sum of the irreducible components of its simple
subcoalgebras. This file removes the finite-dimensionality hypothesis, using the fundamental theorem
of coalgebras (every finite subset lies in a finite-dimensional subcoalgebra) together with a
*restriction* result: the wedge product, hence every wedge power and every irreducible component, is
computed inside a subcoalgebra `E` by intersecting the corresponding submodule of `C` with `E`.

## Main results

* `Coalgebra.Coradical.sup_tens_inf_tens` — the linear algebra behind the restriction result:
  `(X ⊗ N + M ⊗ Y) ⊓ (E ⊗ F) = (X ⊓ E) ⊗ F + E ⊗ (Y ⊓ F)`;
* `Coalgebra.Coradical.wedge_inf_eq` — `(X ∧ Y) ⊓ E = ((X ⊓ E) ∧ (Y ⊓ E)) ⊓ E` for a subcoalgebra
  `E`;
* `Coalgebra.Coradical.map_wedge_eq`, `Coalgebra.Coradical.map_wedgePow_eq`,
  `Coalgebra.Coradical.map_irrComponent_eq` — wedges, wedge powers and irreducible components formed
  in a subcoalgebra `E` are the traces on `E` of the ones formed in `C`;
* `Coalgebra.Coradical.iSup_irrComponent_eq_top'` and
  `Coalgebra.Coradical.irrComponent_inf_iSup_eq_bot'` — **Kostant's decomposition theorem** for an
  arbitrary cocommutative coalgebra over a field.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 2.2.1 and Chapter 8
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

/-! ### Linear algebra -/

section LinearAlgebra

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The kernel of `π_X ⊗ π_Y` for submodules of two different modules. -/
theorem ker_map_mkQ' (X : Submodule k M) (Y : Submodule k N) :
    LinearMap.ker (map X.mkQ Y.mkQ)
      = tens X (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) Y := by
  rw [ker_map _ X.mkQ_surjective _ Y.mkQ_surjective, Submodule.ker_mkQ, Submodule.ker_mkQ]

/-- `tens A E ⊔ tens E B ≤ tens A ⊤ ⊔ tens ⊤ B`. -/
theorem tens_sup_le (A B E : Submodule k M) :
    tens A E ⊔ tens E B ≤ tens A (⊤ : Submodule k M) ⊔ tens (⊤ : Submodule k M) B :=
  sup_le_sup (tens_mono le_rfl le_top) (tens_mono le_top le_rfl)

/-- The trace on `E ⊗ F` of `X ⊗ N + M ⊗ Y` is `(X ⊓ E) ⊗ F + E ⊗ (Y ⊓ F)`. -/
theorem sup_tens_inf_tens (X E : Submodule k M) (Y F : Submodule k N) :
    (tens X (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) Y) ⊓ tens E F
      = tens (X ⊓ E) F ⊔ tens E (Y ⊓ F) := by
  -- With `X' = X ∩ E` and `Y' = Y ∩ F` inside `E` and `F`, the maps `E/X' → M/X` and
  -- `F/Y' → N/Y` are injective, so the kernel of `E ⊗ F → M/X ⊗ N/Y` is that of
  -- `E ⊗ F → E/X' ⊗ F/Y'`; then map it to `M ⊗ N`.
  set X' : Submodule k E := Submodule.comap E.subtype X with hX'
  set Y' : Submodule k F := Submodule.comap F.subtype Y with hY'
  have hkerX : X' ≤ LinearMap.ker (X.mkQ ∘ₗ E.subtype) := by
    intro x hx; simpa [LinearMap.mem_ker, X', Y'] using hx
  have hkerY : Y' ≤ LinearMap.ker (Y.mkQ ∘ₗ F.subtype) := by
    intro x hx; simpa [LinearMap.mem_ker, X', Y'] using hx
  set ub : (E ⧸ X') →ₗ[k] (M ⧸ X) := X'.liftQ (X.mkQ ∘ₗ E.subtype) hkerX with hub
  set vb : (F ⧸ Y') →ₗ[k] (N ⧸ Y) := Y'.liftQ (Y.mkQ ∘ₗ F.subtype) hkerY with hvb
  have hubinj : Function.Injective ub := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ (fun x hx => ?_)
    simpa [LinearMap.mem_ker, X', Y'] using hx
  have hvbinj : Function.Injective vb := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ (fun x hx => ?_)
    simpa [LinearMap.mem_ker, X', Y'] using hx
  have hsq : map X.mkQ Y.mkQ ∘ₗ map E.subtype F.subtype
      = map ub vb ∘ₗ map X'.mkQ Y'.mkQ := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    congr 1
  have hker : Submodule.comap (map E.subtype F.subtype)
      (LinearMap.ker (map X.mkQ Y.mkQ))
      = tens X' (⊤ : Submodule k F) ⊔ tens (⊤ : Submodule k E) Y' := by
    rw [← LinearMap.ker_comp, hsq, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 (TensorProduct.map_injective_of_flat_flat _ _ hubinj hvbinj)),
      ker_map _ X'.mkQ_surjective _ Y'.mkQ_surjective, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have hmain := congr(Submodule.map (map E.subtype F.subtype) $hker)
  rw [Submodule.map_comap_eq, ker_map_mkQ', ← tens_eq_range, Submodule.map_sup, map_tens, map_tens,
    Submodule.map_top, Submodule.map_top, Submodule.range_subtype, Submodule.range_subtype,
    hX', hY', Submodule.map_comap_subtype, Submodule.map_comap_subtype] at hmain
  rw [inf_comm] at hmain
  rw [inf_comm X E, inf_comm Y F]
  exact hmain

end LinearAlgebra

/-! ### Restriction of wedges to a subcoalgebra -/

section Restrict

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C]

/-- The image in `C` of a submodule of `E` is contained in `E`. -/
theorem map_subtype_le_self {E : Submodule k C} (X : Submodule k E) :
    Submodule.map E.subtype X ≤ E := by
  rintro _ ⟨e, _, rfl⟩; exact e.2

/-- For `T ≤ E`, pulling `T` back to `E` and pushing it forward again gives `T`. -/
theorem map_comap_subtype_eq {E T : Submodule k C} (hTE : T ≤ E) :
    Submodule.map E.subtype (Submodule.comap E.subtype T) = T := by
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hTE]

variable [Coalgebra k C]

/-- The wedge product of the traces on a subcoalgebra `E` has the same trace on `E` as the
original wedge product. -/
theorem wedge_inf_eq {E : Submodule k C} (hE : IsSubcoalgebra E) (X Y : Submodule k C) :
    wedge X Y ⊓ E = wedge (X ⊓ E) (Y ⊓ E) ⊓ E := by
  refine le_antisymm (le_inf ?_ inf_le_right)
    (inf_le_inf_right _ (wedge_mono inf_le_left inf_le_left))
  rintro x ⟨hxw, hxE⟩
  simp only [SetLike.mem_coe] at hxw hxE
  rw [mem_wedge_iff] at hxw
  rw [mem_wedge_iff]
  have hmem : comul (R := k) x ∈ (tens X ⊤ ⊔ tens ⊤ Y) ⊓ tens E E :=
    ⟨hxw, comul_mem_tens hE hxE⟩
  rw [sup_tens_inf_tens] at hmem
  exact tens_sup_le _ _ _ hmem

variable {E : Submodule k C} (hE : IsSubcoalgebra E)

/-- The wedge product formed inside a subcoalgebra `E` is the trace on `E` of the wedge product
formed in `C`. -/
theorem map_wedge_eq (X Y : Submodule k E) :
    letI := subCoalgebra hE
    Submodule.map E.subtype (wedge X Y)
      = wedge (Submodule.map E.subtype X) (Submodule.map E.subtype Y) ⊓ E := by
  let := subCoalgebra hE
  have hcomul : ∀ e : E, comul (R := k) (e : C)
      = map E.subtype E.subtype (comul (R := k) e) :=
    fun e => (LinearMap.ext_iff.1 (map_subtype_comp_subComul hE) e).symm
  have himg : Submodule.map (map E.subtype E.subtype)
      (tens X (⊤ : Submodule k E) ⊔ tens (⊤ : Submodule k E) Y)
      = tens (Submodule.map E.subtype X) E ⊔ tens E (Submodule.map E.subtype Y) := by
    rw [Submodule.map_sup, map_tens, map_tens, Submodule.map_top, Submodule.range_subtype]
  have hXle : Submodule.map E.subtype X ≤ E := map_subtype_le_self X
  have hYle : Submodule.map E.subtype Y ≤ E := map_subtype_le_self Y
  refine le_antisymm ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    simp only [SetLike.mem_coe] at he
    refine ⟨?_, e.2⟩
    rw [SetLike.mem_coe, mem_wedge_iff]
    change comul (R := k) ((e : C)) ∈ _
    rw [hcomul e]
    refine tens_sup_le (Submodule.map E.subtype X) (Submodule.map E.subtype Y) E ?_
    rw [← himg]
    exact ⟨_, (mem_wedge_iff (k := k)).1 he, rfl⟩
  · rintro x ⟨hxw, hxE⟩
    simp only [SetLike.mem_coe] at hxw hxE
    refine ⟨⟨x, hxE⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_wedge_iff]
    have hmem : comul (R := k) x ∈ (tens (Submodule.map E.subtype X) ⊤
        ⊔ tens ⊤ (Submodule.map E.subtype Y)) ⊓ tens E E :=
      ⟨(mem_wedge_iff (k := k)).1 hxw, comul_mem_tens hE hxE⟩
    rw [sup_tens_inf_tens, inf_eq_left.2 hXle, inf_eq_left.2 hYle, ← himg] at hmem
    obtain ⟨t, ht, hteq⟩ := hmem
    have hteq2 : t = comul (R := k) (⟨x, hxE⟩ : E) := by
      apply injective_map_subtype E
      rw [hteq, ← hcomul]
    rwa [hteq2] at ht

/-- Wedge powers formed inside a subcoalgebra `E` are the traces on `E` of those formed in `C`. -/
theorem map_wedgePow_eq (X : Submodule k E) (n : ℕ) :
    letI := subCoalgebra hE
    Submodule.map E.subtype (wedgePow X n)
      = wedgePow (Submodule.map E.subtype X) n ⊓ E := by
  let := subCoalgebra hE
  induction n with
  | zero => simpa using (inf_eq_left.2 (map_subtype_le_self X)).symm
  | succ n ih =>
      have h1 : wedgePow (Submodule.map E.subtype X) (n + 1) ⊓ E
          = wedge (wedgePow (Submodule.map E.subtype X) n ⊓ E)
              (Submodule.map E.subtype X) ⊓ E := by
        rw [wedgePow_succ, wedge_inf_eq hE, inf_eq_left.2 (map_subtype_le_self X)]
      rw [wedgePow_succ, map_wedge_eq hE, ih, h1]

/-- Irreducible components formed inside a subcoalgebra `E` are the traces on `E` of those formed
in `C`. -/
theorem map_irrComponent_eq {X : Submodule k E}
    (hX : letI := subCoalgebra hE; IsSubcoalgebra X) :
    letI := subCoalgebra hE
    Submodule.map E.subtype (irrComponent X)
      = irrComponent (Submodule.map E.subtype X) ⊓ E := by
  let := subCoalgebra hE
  have hcomul : map E.subtype E.subtype ∘ₗ (comul : E →ₗ[k] E ⊗[k] E)
      = comul ∘ₗ E.subtype := map_subtype_comp_subComul hE
  have hXmap : IsSubcoalgebra (Submodule.map E.subtype X) := isSubcoalgebra_map hcomul hX
  refine le_antisymm ?_ ?_
  · rw [irrComponent, Submodule.map_iSup]
    refine iSup_le fun n => ?_
    rw [map_wedgePow_eq hE X n]
    exact inf_le_inf_right _ (wedgePow_le_irrComponent _ n)
  · rintro x ⟨hxi, hxE⟩
    simp only [SetLike.mem_coe] at hxi hxE
    rw [irrComponent, Submodule.mem_iSup_of_directed _ (directed_wedgePow hXmap)] at hxi
    obtain ⟨n, hn⟩ := hxi
    have hx : x ∈ Submodule.map E.subtype (wedgePow X n) := by
      rw [map_wedgePow_eq hE X n]; exact ⟨hn, hxE⟩
    exact Submodule.map_mono (wedgePow_le_irrComponent X n) hx

/-- The preimage in a subcoalgebra `E` of a subcoalgebra of `C` is a subcoalgebra of `E`. -/
theorem isSubcoalgebra_comap_subtype {T : Submodule k C} (hT : IsSubcoalgebra T) :
    letI := subCoalgebra hE; IsSubcoalgebra (Submodule.comap E.subtype T) :=
  letI := subCoalgebra hE
  isSubcoalgebra_comap E.subtype_injective (map_subtype_comp_subComul hE) hT

/-- A simple subcoalgebra contained in `E` stays simple when viewed inside `E`. -/
theorem isSimpleSubcoalgebra_comap {T : Submodule k C} (hT : IsSimpleSubcoalgebra T)
    (hTE : T ≤ E) :
    letI := subCoalgebra hE; IsSimpleSubcoalgebra (Submodule.comap E.subtype T) := by
  let := subCoalgebra hE
  refine ⟨isSubcoalgebra_comap_subtype hE hT.1, ?_, ?_⟩
  · intro h
    apply hT.2.1
    rw [← map_comap_subtype_eq hTE, h, Submodule.map_bot]
  · intro V hV hVsub
    have hmapV : Submodule.map E.subtype V ≤ T := by
      rw [← map_comap_subtype_eq hTE]; exact Submodule.map_mono hV
    rcases hT.2.2 _ hmapV (isSubcoalgebra_map (map_subtype_comp_subComul hE) hVsub) with h | h
    · left
      exact Submodule.map_injective_of_injective E.subtype_injective (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective E.subtype_injective
        (by rw [h, map_comap_subtype_eq hTE])

/-- An element of `E` lying in the irreducible component of a subcoalgebra `T ≤ E` lies, inside
`E`, in the irreducible component of the corresponding subcoalgebra of `E`. -/
theorem mem_irrComponent_comap {T : Submodule k C} (hT : IsSubcoalgebra T) (hTE : T ≤ E)
    {y : C} (hy : y ∈ irrComponent T) (hyE : y ∈ E) :
    letI := subCoalgebra hE
    (⟨y, hyE⟩ : E) ∈ irrComponent (Submodule.comap E.subtype T) := by
  let := subCoalgebra hE
  have h := map_irrComponent_eq hE (isSubcoalgebra_comap_subtype hE hT)
  rw [map_comap_subtype_eq hTE] at h
  have hmem : y ∈ Submodule.map E.subtype (irrComponent (Submodule.comap E.subtype T)) := by
    rw [h]; exact ⟨hy, hyE⟩
  obtain ⟨z, hz, hzy⟩ := hmem
  have hzeq : z = (⟨y, hyE⟩ : E) := Subtype.ext hzy
  rwa [hzeq] at hz

end Restrict

/-! ### Kostant's theorem in general -/

section General

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A simple subcoalgebra is finite-dimensional. -/
theorem fg_of_isSimpleSubcoalgebra {S : Submodule k C} (hS : IsSimpleSubcoalgebra S) : S.FG := by
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.2.1
  obtain ⟨E, hxE, hEfg, hE⟩ := Coalgebra.LocallyFinite.exists_fg_subcoalgebra (k := k) x
  have hSE : S ⊓ E = S := by
    rcases hS.2.2 (S ⊓ E) inf_le_left (isSubcoalgebra_inf hS.1 hE) with h | h
    · exact absurd (h ▸ (Submodule.mem_inf.2 ⟨hxS, hxE⟩)) (by simpa using hx0)
    · exact h
  rw [← hSE]
  have : FiniteDimensional k E := (Submodule.fg_iff_finiteDimensional E).1 hEfg
  have : FiniteDimensional k (S ⊓ E : Submodule k C) :=
    Submodule.finiteDimensional_of_le inf_le_right
  exact (Submodule.fg_iff_finiteDimensional _).2 this

/-- Every finitely generated submodule of a coalgebra lies in a finite-dimensional
subcoalgebra. -/
theorem exists_fd_subcoalgebra_of_fg {V : Submodule k C} (hV : V.FG) :
    ∃ E : Submodule k C, V ≤ E ∧ FiniteDimensional k E ∧ IsSubcoalgebra E := by
  classical
  obtain ⟨s, hs⟩ := hV
  choose F hF1 hF2 hF3 using fun x : C => Coalgebra.LocallyFinite.exists_fg_subcoalgebra (k := k) x
  refine ⟨⨆ x ∈ s, F x, ?_, ?_, ?_⟩
  · rw [← hs, Submodule.span_le]
    intro x hx
    exact le_iSup₂ (f := fun (x : C) (_ : x ∈ s) => F x) x hx (hF1 x)
  · exact (Submodule.fg_iff_finiteDimensional _).1 (Submodule.fg_biSup s F fun x _ => hF2 x)
  · rw [show (⨆ x ∈ s, F x) = sSup (F '' ↑s) from (sSup_image ..).symm]
    exact isSubcoalgebra_sSup (by rintro _ ⟨x, _, rfl⟩; exact hF3 x)

/-- A simple subcoalgebra `S`, finitely many simple subcoalgebras `T i` and finitely many vectors
`v i` all lie in one finite-dimensional subcoalgebra. -/
theorem exists_fd_subcoalgebra_of_finset {S : Submodule k C} (hS : IsSimpleSubcoalgebra S)
    {ι : Type*} (s : Finset ι) (T : ι → Submodule k C) (hT : ∀ i, IsSimpleSubcoalgebra (T i))
    (v : ι → C) :
    ∃ E : Submodule k C, S ≤ E ∧ (∀ i ∈ s, T i ≤ E) ∧ (∀ i ∈ s, v i ∈ E) ∧
      FiniteDimensional k E ∧ IsSubcoalgebra E := by
  set V : Submodule k C := S ⊔ ⨆ i ∈ s, (T i ⊔ Submodule.span k {v i}) with hV
  have hVfg : V.FG := by
    refine Submodule.FG.sup (fg_of_isSimpleSubcoalgebra hS) ?_
    exact Submodule.fg_biSup s _ fun i _ =>
      Submodule.FG.sup (fg_of_isSimpleSubcoalgebra (hT i)) (Submodule.fg_span_singleton _)
  obtain ⟨E, hVE, hEfin, hE⟩ := exists_fd_subcoalgebra_of_fg hVfg
  refine ⟨E, le_trans le_sup_left hVE, fun i hi => ?_, fun i hi => ?_, hEfin, hE⟩
  · exact le_trans (le_trans le_sup_left (le_iSup₂ (f := fun i (_ : i ∈ s) =>
      (T i ⊔ Submodule.span k {v i})) i hi)) (le_trans le_sup_right hVE)
  · refine hVE (Submodule.mem_sup_right ?_)
    refine Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ?_)
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

variable [IsCocomm k C]

/-- **Kostant's theorem, first half, in general**: the irreducible components of the simple
subcoalgebras of a cocommutative coalgebra over a field span it. -/
theorem iSup_irrComponent_eq_top' :
    (⨆ S ∈ {S : Submodule k C | IsSimpleSubcoalgebra S}, irrComponent S) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨E, hxE, hEfg, hE⟩ := Coalgebra.LocallyFinite.exists_fg_subcoalgebra (k := k) x
  have hEfin : FiniteDimensional k E := (Submodule.fg_iff_finiteDimensional E).1 hEfg
  let : Coalgebra k E := subCoalgebra hE
  have : IsCocomm k E := ⟨subComul_comm hE⟩
  have hcomul : map E.subtype E.subtype ∘ₗ (comul : E →ₗ[k] E ⊗[k] E)
      = comul ∘ₗ E.subtype := map_subtype_comp_subComul hE
  have hmap := congr(Submodule.map E.subtype $(iSup_irrComponent_eq_top (k := k) (C := E)))
  rw [Submodule.map_top, Submodule.range_subtype] at hmap
  have hle : Submodule.map E.subtype
      (⨆ S ∈ {S : Submodule k E | IsSimpleSubcoalgebra S}, irrComponent S)
      ≤ ⨆ S ∈ {S : Submodule k C | IsSimpleSubcoalgebra S}, irrComponent S := by
    rw [Submodule.map_iSup]
    refine iSup_le fun S => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hS => ?_
    rw [map_irrComponent_eq hE hS.1]
    exact le_trans inf_le_left
      (le_iSup₂ (f := fun S (_ : S ∈ {S : Submodule k C | IsSimpleSubcoalgebra S}) =>
        irrComponent S) (Submodule.map E.subtype S)
        (isSimpleSubcoalgebra_map E.subtype_injective hcomul hS))
  refine hle ?_
  rw [hmap]
  exact hxE

/-- The irreducible component of a simple subcoalgebra meets the sum of the others trivially. -/
theorem irrComponent_inf_iSup_eq_bot' {S : Submodule k C} (hS : IsSimpleSubcoalgebra S) :
    irrComponent S ⊓
      (⨆ T ∈ {T : Submodule k C | IsSimpleSubcoalgebra T ∧ T ≠ S}, irrComponent T) = ⊥ := by
  classical
  -- A vector `x` of both sides is a finite sum of vectors of components `irrComponent T`: all of
  -- them, and `S` and the `T`s, lie in one finite-dimensional subcoalgebra `E`.
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  obtain ⟨hxS, hxsup⟩ := hx
  simp only [SetLike.mem_coe] at hxS hxsup
  have hre : (⨆ T ∈ {T : Submodule k C | IsSimpleSubcoalgebra T ∧ T ≠ S}, irrComponent T)
      = ⨆ i : {T : Submodule k C // IsSimpleSubcoalgebra T ∧ T ≠ S},
          irrComponent (i : Submodule k C) := by
    simp only [Set.mem_ofPred_eq]
    exact iSup_subtype' (p := fun T => IsSimpleSubcoalgebra T ∧ T ≠ S)
      (f := fun T _ => irrComponent T)
  rw [hre, Submodule.mem_iSup_iff_exists_finset] at hxsup
  obtain ⟨s, hs⟩ := hxsup
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨μ, hμ⟩ := hs
  obtain ⟨E, hSE, hTE, hμE, hEfin, hE⟩ := exists_fd_subcoalgebra_of_finset hS s
    (fun i => (i : Submodule k C)) (fun i => i.2.1) (fun i => (μ i : C))
  have hxE : x ∈ E := by
    rw [← hμ]; exact Submodule.sum_mem _ fun i hi => hμE i hi
  -- In `E`, `x` lies in the component of `S ∩ E` and in the sum of the components of the
  -- `T ∩ E`, which meet trivially by the finite-dimensional case.
  let : Coalgebra k E := subCoalgebra hE
  have : IsCocomm k E := ⟨subComul_comm hE⟩
  set S' : Submodule k E := Submodule.comap E.subtype S with hS'
  have hS'simple : IsSimpleSubcoalgebra S' := isSimpleSubcoalgebra_comap hE hS hSE
  set ν : {T : Submodule k C // IsSimpleSubcoalgebra T ∧ T ≠ S} → Submodule k E :=
    fun i => Submodule.comap E.subtype (i : Submodule k C) with hν
  have hxS' : (⟨x, hxE⟩ : E) ∈ irrComponent S' :=
    mem_irrComponent_comap hE hS.1 hSE hxS hxE
  have hsum : (⟨x, hxE⟩ : E) ∈ ⨆ i ∈ s, irrComponent (ν i) := by
    rw [Submodule.mem_iSup_finset_iff_exists_sum]
    refine ⟨fun i => if hi : i ∈ s then
      ⟨⟨(μ i : C), hμE i hi⟩, mem_irrComponent_comap hE i.2.1.1 (hTE i hi) (μ i).2 (hμE i hi)⟩
      else 0, ?_⟩
    refine Subtype.ext ?_
    push_cast
    rw [← hμ]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [dite_eq_left hi]
  have hbot := irrComponent_inf_iSup_eq_bot (k := k) (C := E) hS'simple
  have hle : (⨆ i ∈ s, irrComponent (ν i))
      ≤ ⨆ T ∈ {T : Submodule k E | IsSimpleSubcoalgebra T ∧ T ≠ S'}, irrComponent T := by
    refine iSup₂_le fun i hi => ?_
    refine le_iSup₂ (f := fun T (_ : T ∈ {T : Submodule k E | IsSimpleSubcoalgebra T ∧ T ≠ S'}) =>
      irrComponent T) (ν i) ⟨isSimpleSubcoalgebra_comap hE i.2.1 (hTE i hi), ?_⟩
    intro h
    have hh : Submodule.comap E.subtype (i : Submodule k C) = Submodule.comap E.subtype S := h
    exact i.2.2 (by rw [← map_comap_subtype_eq (hTE i hi), hh, map_comap_subtype_eq hSE])
  have hzero : (⟨x, hxE⟩ : E) ∈ (⊥ : Submodule k E) := hbot ▸ ⟨hxS', hle hsum⟩
  simpa using Subtype.ext_iff.1 ((Submodule.mem_bot k).1 hzero)

end General

end Coalgebra.Coradical
