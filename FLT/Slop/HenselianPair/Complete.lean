/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Enlarge
public import FLT.Slop.HenselianPair.Nilpotent
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adically complete rings give Henselian pairs

If `R` is `I`-adically complete then `(R, I)` is a Henselian pair.  This upgrades mathlib's
`IsAdicComplete.henselianRing` (the *root*-lifting form) to the full *factorisation*-lifting
form, and derives a range of consequences for algebras, radicals, finite/Noetherian settings,
and complete local rings.

The proof follows the tower route.  For each `m`, the ring `R ⧸ I ^ (m+1)` is Henselian at the
nilpotent ideal `I·(R ⧸ I ^ (m+1))`, so a coprime monic factorisation of `f mod I` lifts to a
factorisation `𝒢ₘ * 𝓗ₘ` of `f mod I^(m+1)` over `R ⧸ I ^ (m+1)`.  These cohere across the tower
by uniqueness of factorisation, so honest `R`-lifts `Gₘ, Hₘ` have `I`-adically Cauchy coefficient
sequences.  Their limits (assembled coefficient by coefficient via `IsPrecomplete.prec'`) give
monic `G, H` with `f = G * H` and the right reductions mod `I` (checked via `IsHausdorff.haus'`).

## Main results

* `IsHenselianPair.of_isAdicComplete` — if `R` is `I`-adically complete then `(R, I)` is a
  Henselian pair.
* `IsHenselianPair.exists_factorization_mod_pow` — the per-level factorisation over `R ⧸ I ^ (m+1)`.
* `IsHenselianPair.of_isAdicComplete_radical` and the `radical`-comparison variant
  `of_isAdicComplete_of_radical_eq`.
* `IsHenselianPair.of_isAdicComplete_map_algebra` and its variants — completeness transported to
  an algebra.
* `HenselianLocalRing.of_isAdicComplete_maximalIdeal` and variants — the local-ring corollaries.

## Implementation notes

Some upstream results are stated for the tower via a coherence step (`coherence_step`).  See
the Stacks Project (More on Algebra, §15.11, tag 0ALJ) for the surrounding theory.

## References

* [Stacks Project, Tag 0ALJ](https://stacks.math.columbia.edu/tag/0ALJ)
-/

@[expose] public section

open Polynomial
open TensorProduct

universe u

variable {R : Type u} [CommRing R]

namespace IsAdicComplete

/-- A finite module over a Noetherian complete ring is complete for the same
adic topology.  This packages the standard tensor-product comparison
`R̂ ⊗[R] M ≃ M̂`: when `R ≃ R̂`, the completion map `M → M̂` is an isomorphism. -/
theorem of_finite_module_of_isNoetherian {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] {I : Ideal R} [IsAdicComplete I R] :
    IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let eR : R ≃ₗ[R] AdicCompletion I R := AdicCompletion.ofLinearEquiv I R
  let eTensor : R ⊗[R] M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
    TensorProduct.congr eR (LinearEquiv.refl R M)
  let e₁ : M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
    (TensorProduct.lid R M).symm.trans eTensor
  let e₂ : AdicCompletion I R ⊗[R] M ≃ₗ[R] AdicCompletion I M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  convert (EquivLike.bijective (e₁.trans e₂)) using 1
  ext x n
  simp only [AdicCompletion.of_apply, Submodule.mkQ_apply, LinearEquiv.trans_apply]
  exact (one_smul R (Submodule.Quotient.mk x : M ⧸ (I ^ n • ⊤ : Submodule R M))).symm

end IsAdicComplete

namespace IsHenselianPair

/-- **Per-level factorisation over `R ⧸ I ^ (m+1)`.**  Given a coprime monic
factorisation `f mod I = gbar * hbar` (with `f` monic), there are monic lifts `G, H`
over `R` of matching degree, whose reductions mod `I` are `gbar, hbar`, and with
`f ≡ G * H` modulo `I ^ (m+1)`.

The ring `R ⧸ I ^ (m+1)` is Henselian at the nilpotent ideal `I·(R ⧸ I ^ (m+1))`
(`of_pow_eq_bot`); we lift the given factorisation there through the isomorphism
`(R ⧸ I ^ (m+1)) ⧸ (I·) ≃ R ⧸ I` and pull an honest lift back to `R`. -/
theorem exists_factorization_mod_pow {I : Ideal R} [Nontrivial (R ⧸ I)]
    {f : R[X]} (hf : f.Monic) {gbar hbar : (R ⧸ I)[X]} (hg₀ : gbar.Monic) (hh₀ : hbar.Monic)
    (hcop : IsCoprime gbar hbar) (hfact : f.map (Ideal.Quotient.mk I) = gbar * hbar) (m : ℕ) :
    ∃ G H : R[X], G.Monic ∧ H.Monic ∧ G.natDegree = gbar.natDegree ∧
      H.natDegree = hbar.natDegree ∧ G.map (Ideal.Quotient.mk I) = gbar ∧
      H.map (Ideal.Quotient.mk I) = hbar ∧
      (f - G * H).map (Ideal.Quotient.mk (I ^ (m + 1))) = 0 := by
  set K : Ideal R := I ^ (m + 1) with hK
  have hKI : K ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero m)
  set mkK := Ideal.Quotient.mk K with hmkK
  -- `R ⧸ K` is henselian at the nilpotent ideal `I·(R ⧸ K)`.
  have hI'pow : (I.map mkK) ^ (m + 1) = ⊥ := by
    rw [← Ideal.map_pow, ← hK, Ideal.map_quotient_self]
  have hens : IsHenselianPair (R ⧸ K) (I.map mkK) := of_pow_eq_bot hI'pow
  -- `e : (R ⧸ K) ⧸ (I·(R ⧸ K)) ≃+* R ⧸ I`.
  set e := DoubleQuot.quotQuotEquivQuotOfLE hKI with he
  haveI : Nontrivial ((R ⧸ K) ⧸ I.map mkK) := e.symm.injective.nontrivial
  have hcomp : (e.toRingHom.comp (Ideal.Quotient.mk (I.map mkK))).comp mkK
      = Ideal.Quotient.mk I := by
    ext r; exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hKI
  have hee : e.toRingHom.comp e.symm.toRingHom = RingHom.id (R ⧸ I) :=
    RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply]; exact e.apply_symm_apply x
  have hmap3 : ∀ p : R[X],
      ((p.map mkK).map (Ideal.Quotient.mk (I.map mkK))).map e.toRingHom
        = p.map (Ideal.Quotient.mk I) := fun p => by
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  -- Pull the factorisation of `f mod I` back to `(R ⧸ K) ⧸ (I·)`.
  have hcop' : IsCoprime (gbar.map e.symm.toRingHom) (hbar.map e.symm.toRingHom) := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a.map e.symm.toRingHom, b.map e.symm.toRingHom, by
      rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
        Polynomial.map_one]⟩
  have hf1fact : (f.map mkK).map (Ideal.Quotient.mk (I.map mkK))
      = gbar.map e.symm.toRingHom * hbar.map e.symm.toRingHom := by
    apply Polynomial.map_injective e.toRingHom e.injective
    rw [hmap3 f, hfact, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map, hee]
    simp only [Polynomial.map_id]
  -- Lift the factorisation to `R ⧸ K` using the henselian pair.
  obtain ⟨g₁, h₁, hg₁mon, hh₁mon, hf1, hg₁map, hh₁map⟩ :=
    hens.exists_lift_factorization (f.map mkK) (hf.map _) (hg₀.map _) (hh₀.map _) hcop' hf1fact
  -- Honest `R`-lifts of `g₁, h₁`.
  obtain ⟨G, hGmap, hGdeg, hGmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective g₁) hg₁mon
  obtain ⟨H, hHmap, hHdeg, hHmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective h₁) hh₁mon
  refine ⟨G, H, hGmon, hHmon, ?_, ?_, ?_, ?_, ?_⟩
  · -- `G.natDegree = gbar.natDegree`
    rw [hGdeg]
    have h1 : (g₁.map (Ideal.Quotient.mk (I.map mkK))).natDegree = g₁.natDegree :=
      hg₁mon.natDegree_map _
    rw [hg₁map] at h1
    rw [← h1, hg₀.natDegree_map]
  · rw [hHdeg]
    have h1 : (h₁.map (Ideal.Quotient.mk (I.map mkK))).natDegree = h₁.natDegree :=
      hh₁mon.natDegree_map _
    rw [hh₁map] at h1
    rw [← h1, hh₀.natDegree_map]
  · -- `G.map (mk I) = gbar`
    rw [← hmap3 G, hGmap, hg₁map, Polynomial.map_map, hee, Polynomial.map_id]
  · rw [← hmap3 H, hHmap, hh₁map, Polynomial.map_map, hee, Polynomial.map_id]
  · -- `f ≡ G * H  [mod K]`
    rw [Polynomial.map_sub, Polynomial.map_mul, hGmap, hHmap, ← hf1, sub_self]

/-- **Coherence of the per-level factorisations.**  Two monic factorisations of `f`
modulo a nilpotent-quotient ideal `K ≤ I` (both reducing mod `I` to the fixed coprime
pair `gbar, hbar`) agree modulo `K`.  This is `factorization_unique` transported into the
ring `R ⧸ K`, and is what makes the coefficient sequences of the tower `I`-adically
Cauchy. -/
theorem coherence_step {I K : Ideal R} (hKI : K ≤ I)
    (hnil : IsNilpotent (I.map (Ideal.Quotient.mk K)))
    {f : R[X]} {gbar hbar : (R ⧸ I)[X]} (hcop : IsCoprime gbar hbar)
    {G₁ H₁ G₂ H₂ : R[X]} (hG₁ : G₁.Monic) (hG₂ : G₂.Monic)
    (hG₁I : G₁.map (Ideal.Quotient.mk I) = gbar) (hH₁I : H₁.map (Ideal.Quotient.mk I) = hbar)
    (hG₂I : G₂.map (Ideal.Quotient.mk I) = gbar) (hH₂I : H₂.map (Ideal.Quotient.mk I) = hbar)
    (hf₁ : (f - G₁ * H₁).map (Ideal.Quotient.mk K) = 0)
    (hf₂ : (f - G₂ * H₂).map (Ideal.Quotient.mk K) = 0) :
    (G₁ - G₂).map (Ideal.Quotient.mk K) = 0 ∧ (H₁ - H₂).map (Ideal.Quotient.mk K) = 0 := by
  set mkK := Ideal.Quotient.mk K with hmkK
  set I' := I.map mkK with hI'
  set e := DoubleQuot.quotQuotEquivQuotOfLE hKI with he
  have hcomp : (e.toRingHom.comp (Ideal.Quotient.mk I')).comp mkK = Ideal.Quotient.mk I := by
    ext r; exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hKI
  have hmap3 : ∀ p : R[X],
      ((p.map mkK).map (Ideal.Quotient.mk I')).map e.toRingHom = p.map (Ideal.Quotient.mk I) :=
    fun p => by rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  have hee : e.symm.toRingHom.comp e.toRingHom = RingHom.id ((R ⧸ K) ⧸ I') :=
    RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply]; exact e.symm_apply_apply x
  -- Reductions mod `K`.
  set g₁ := G₁.map mkK with hg₁
  set h₁ := H₁.map mkK with hh₁
  set g₂ := G₂.map mkK with hg₂
  set h₂ := H₂.map mkK with hh₂
  have hmon : ∀ {p : R[X]}, p.Monic → (p.map mkK).Monic := fun hp => hp.map _
  -- Both are factorisations of `f.map mkK`.
  have hf₁' : g₁ * h₁ = f.map mkK := by
    have := hf₁; rw [Polynomial.map_sub, Polynomial.map_mul, sub_eq_zero] at this
    exact this.symm
  have hf₂' : g₂ * h₂ = f.map mkK := by
    have := hf₂; rw [Polynomial.map_sub, Polynomial.map_mul, sub_eq_zero] at this
    exact this.symm
  have hgh : g₁ * h₁ = g₂ * h₂ := by rw [hf₁', hf₂']
  -- Reductions mod `I'` agree (pull back through the injective `e`).
  have hinj := Polynomial.map_injective e.toRingHom e.injective
  have hge : (g₁.map (Ideal.Quotient.mk I')).map e.toRingHom = gbar := by
    rw [hg₁, hmap3 G₁, hG₁I]
  have hhe : (h₁.map (Ideal.Quotient.mk I')).map e.toRingHom = hbar := by
    rw [hh₁, hmap3 H₁, hH₁I]
  have hgeqI : g₁.map (Ideal.Quotient.mk I') = g₂.map (Ideal.Quotient.mk I') := by
    apply hinj; rw [hg₁, hg₂, hmap3 G₁, hmap3 G₂, hG₁I, hG₂I]
  have hheqI : h₁.map (Ideal.Quotient.mk I') = h₂.map (Ideal.Quotient.mk I') := by
    apply hinj; rw [hh₁, hh₂, hmap3 H₁, hmap3 H₂, hH₁I, hH₂I]
  -- Coprimality of the mod-`I'` reductions, descended from `hcop` through the iso `e`.
  have hcopI : IsCoprime (g₁.map (Ideal.Quotient.mk I')) (h₁.map (Ideal.Quotient.mk I')) := by
    have hg₁I' : g₁.map (Ideal.Quotient.mk I') = gbar.map e.symm.toRingHom := by
      have := congrArg (Polynomial.map e.symm.toRingHom) hge
      rwa [Polynomial.map_map, hee, Polynomial.map_id] at this
    have hh₁I' : h₁.map (Ideal.Quotient.mk I') = hbar.map e.symm.toRingHom := by
      have := congrArg (Polynomial.map e.symm.toRingHom) hhe
      rwa [Polynomial.map_map, hee, Polynomial.map_id] at this
    rw [hg₁I', hh₁I']
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a.map e.symm.toRingHom, b.map e.symm.toRingHom, by
      rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
        Polynomial.map_one]⟩
  -- Apply uniqueness in `R ⧸ K`.
  obtain ⟨hg, hh⟩ := IsHenselianPair.factorization_unique hnil (hmon hG₁) (hmon hG₂)
    hcopI hgeqI hheqI hgh
  have hgeq : G₁.map mkK = G₂.map mkK := hg
  have hheq : H₁.map mkK = H₂.map mkK := hh
  exact ⟨by rw [Polynomial.map_sub, hgeq, sub_self],
    by rw [Polynomial.map_sub, hheq, sub_self]⟩

/-- **A complete ring gives a Henselian pair** (Stacks Tag 0ALJ).  If `R` is
`I`-adically complete then `(R, I)` is a Henselian pair — the factorisation-lifting
upgrade of mathlib's root-lifting `IsAdicComplete.henselianRing`.

The tower `R ⧸ I ^ (m+1)` of henselian quotients (`exists_factorization_mod_pow`)
produces coherent (`coherence_step`) monic lifts `Gₘ, Hₘ` over `R`; their coefficient
sequences are `I`-adically Cauchy, and the limits (assembled via `IsPrecomplete.prec'`
and pinned down by `IsHausdorff.haus'`) give the required factorisation over `R`. -/
theorem of_isAdicComplete {I : Ideal R} [IsAdicComplete I R] : IsHenselianPair R I where
  le_jacobson := IsAdicComplete.le_jacobson_bot I
  exists_lift_factorization := by
    intro f hf gbar hbar hg₀ hh₀ hcop hfact
    -- `(I ^ k • ⊤ : Ideal R) = I ^ k`, to translate `SModEq` into ideal membership.
    have smul_top : ∀ k : ℕ, (I ^ k • ⊤ : Ideal R) = I ^ k := fun k => by
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    rcases subsingleton_or_nontrivial R with _ | _
    · exact ⟨f, 1, hf, monic_one, (mul_one f).symm,
        Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    -- `I ≠ ⊤`, so `R ⧸ I` is nontrivial (needed to apply `exists_factorization_mod_pow`).
    have hItop : I ≠ ⊤ := by
      intro hI
      have h1 : (1 : R) ∈ Ideal.jacobson ⊥ :=
        IsAdicComplete.le_jacobson_bot I (hI ▸ Submodule.mem_top)
      rw [Ideal.mem_jacobson_bot] at h1
      have h0 := h1 (-1)
      rw [one_mul, neg_add_cancel] at h0
      exact not_isUnit_zero h0
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    -- The tower of per-level factorisations over `R ⧸ I ^ (m+1)`.
    choose G Hp hGmon hHmon hGdeg hHdeg hGmapI hHmapI hfmod using
      fun m => exists_factorization_mod_pow hf hg₀ hh₀ hcop hfact m
    set dG := gbar.natDegree with hdG
    set dH := hbar.natDegree with hdH
    -- Every coefficient of a polynomial killed mod `J` lies in `J`.
    have coeff_of_map_zero : ∀ {J : Ideal R} {p : R[X]},
        p.map (Ideal.Quotient.mk J) = 0 → ∀ i, p.coeff i ∈ J := by
      intro J p h i
      have := Polynomial.ext_iff.mp h i
      rwa [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at this
    -- Coherence of the tower: the coefficient sequences are Cauchy.
    have hcoh : ∀ m n, m ≤ n → ∀ i,
        (G n).coeff i - (G m).coeff i ∈ I ^ (m + 1) ∧
        (Hp n).coeff i - (Hp m).coeff i ∈ I ^ (m + 1) := by
      intro m n hmn i
      have hnil : IsNilpotent (I.map (Ideal.Quotient.mk (I ^ (m + 1)))) := by
        refine ⟨m + 1, ?_⟩
        rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]
      have hfn : (f - G n * Hp n).map (Ideal.Quotient.mk (I ^ (m + 1))) = 0 := by
        ext j
        rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_le_pow_right (by omega) (coeff_of_map_zero (hfmod n) j)
      obtain ⟨hcG, hcH⟩ := coherence_step (Ideal.pow_le_self (Nat.succ_ne_zero m)) hnil hcop
        (hGmon n) (hGmon m)
        (hGmapI n) (hHmapI n) (hGmapI m) (hHmapI m) hfn (hfmod m)
      refine ⟨?_, ?_⟩
      · have := coeff_of_map_zero hcG i; rwa [Polynomial.coeff_sub] at this
      · have := coeff_of_map_zero hcH i; rwa [Polynomial.coeff_sub] at this
    -- Limits of the coefficient sequences.
    have hlimG : ∀ i, ∃ L : R, ∀ n, (G n).coeff i ≡ L [SMOD (I ^ n • ⊤ : Ideal R)] := by
      intro i
      apply IsPrecomplete.prec'
      intro m n hmn
      rw [SModEq.sub_mem, smul_top]
      have h1 : (G n).coeff i - (G m).coeff i ∈ I ^ (m + 1) := (hcoh m n hmn i).1
      have h2 : (G m).coeff i - (G n).coeff i ∈ I ^ (m + 1) := by
        rw [show (G m).coeff i - (G n).coeff i = -((G n).coeff i - (G m).coeff i) by ring]
        exact neg_mem h1
      exact Ideal.pow_le_pow_right (Nat.le_succ m) h2
    have hlimH : ∀ i, ∃ L : R, ∀ n, (Hp n).coeff i ≡ L [SMOD (I ^ n • ⊤ : Ideal R)] := by
      intro i
      apply IsPrecomplete.prec'
      intro m n hmn
      rw [SModEq.sub_mem, smul_top]
      have h1 : (Hp n).coeff i - (Hp m).coeff i ∈ I ^ (m + 1) := (hcoh m n hmn i).2
      have h2 : (Hp m).coeff i - (Hp n).coeff i ∈ I ^ (m + 1) := by
        rw [show (Hp m).coeff i - (Hp n).coeff i = -((Hp n).coeff i - (Hp m).coeff i) by ring]
        exact neg_mem h1
      exact Ideal.pow_le_pow_right (Nat.le_succ m) h2
    choose aG haG using hlimG
    choose aH haH using hlimH
    set Gpoly : R[X] := ∑ i ∈ Finset.range (dG + 1), C (aG i) * X ^ i with hGpoly
    set Hpoly : R[X] := ∑ i ∈ Finset.range (dH + 1), C (aH i) * X ^ i with hHpoly
    have coeffGpoly : ∀ j, Gpoly.coeff j = if j ≤ dG then aG j else 0 := by
      intro j
      rw [hGpoly, finsetSum_coeff]
      simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
    have coeffHpoly : ∀ j, Hpoly.coeff j = if j ≤ dH then aH j else 0 := by
      intro j
      rw [hHpoly, finsetSum_coeff]
      simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
    -- The leading coefficients are `1` (via Hausdorff), giving monicity.
    have haG_top : aG dG = 1 := by
      have hz : (1 : R) - aG dG = 0 := by
        refine IsHausdorff.haus' (I := I) (1 - aG dG) (fun n => ?_)
        rw [SModEq.zero, smul_top]
        have hcoeff1 : (G n).coeff dG = 1 := by
          have := (hGmon n).coeff_natDegree; rwa [hGdeg n] at this
        have := haG dG n
        rw [SModEq.sub_mem, smul_top, hcoeff1] at this
        exact this
      exact (sub_eq_zero.mp hz).symm
    have haH_top : aH dH = 1 := by
      have hz : (1 : R) - aH dH = 0 := by
        refine IsHausdorff.haus' (I := I) (1 - aH dH) (fun n => ?_)
        rw [SModEq.zero, smul_top]
        have hcoeff1 : (Hp n).coeff dH = 1 := by
          have := (hHmon n).coeff_natDegree; rwa [hHdeg n] at this
        have := haH dH n
        rw [SModEq.sub_mem, smul_top, hcoeff1] at this
        exact this
      exact (sub_eq_zero.mp hz).symm
    have hGmonic : Gpoly.Monic := by
      apply monic_of_natDegree_le_of_coeff_eq_one dG
      · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN; rw [coeffGpoly, if_neg (by omega)]
      · rw [coeffGpoly, if_pos le_rfl]; exact haG_top
    have hHmonic : Hpoly.Monic := by
      apply monic_of_natDegree_le_of_coeff_eq_one dH
      · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN; rw [coeffHpoly, if_neg (by omega)]
      · rw [coeffHpoly, if_pos le_rfl]; exact haH_top
    -- Coefficient-wise approximation of the limit polynomials by the tower.
    have approxG : ∀ p n, Gpoly.coeff p - (G n).coeff p ∈ I ^ n := by
      intro p n
      by_cases hp : p ≤ dG
      · rw [coeffGpoly, if_pos hp]
        have := haG p n
        rw [SModEq.sub_mem, smul_top] at this
        rw [show aG p - (G n).coeff p = -((G n).coeff p - aG p) by ring]
        exact neg_mem this
      · rw [coeffGpoly, if_neg (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hGdeg n]; exact not_le.mp hp), sub_zero]
        exact zero_mem _
    have approxH : ∀ q n, Hpoly.coeff q - (Hp n).coeff q ∈ I ^ n := by
      intro q n
      by_cases hq : q ≤ dH
      · rw [coeffHpoly, if_pos hq]
        have := haH q n
        rw [SModEq.sub_mem, smul_top] at this
        rw [show aH q - (Hp n).coeff q = -((Hp n).coeff q - aH q) by ring]
        exact neg_mem this
      · rw [coeffHpoly, if_neg (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hHdeg n]; exact not_le.mp hq), sub_zero]
        exact zero_mem _
    -- `f = Gpoly * Hpoly`, checked coefficient by coefficient via `IsHausdorff.haus'`.
    have hfactor : f = Gpoly * Hpoly := by
      ext k
      have approxGH : ∀ n, (Gpoly * Hpoly).coeff k - (G n * Hp n).coeff k ∈ I ^ n := by
        intro n
        rw [Polynomial.coeff_mul, Polynomial.coeff_mul, ← Finset.sum_sub_distrib]
        apply Submodule.sum_mem
        intro x _
        rw [show Gpoly.coeff x.1 * Hpoly.coeff x.2 - (G n).coeff x.1 * (Hp n).coeff x.2
            = (Gpoly.coeff x.1 - (G n).coeff x.1) * Hpoly.coeff x.2
              + (G n).coeff x.1 * (Hpoly.coeff x.2 - (Hp n).coeff x.2) by ring]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (approxG x.1 n))
          (Ideal.mul_mem_left _ _ (approxH x.2 n))
      have approxfn : ∀ n, f.coeff k - (G n * Hp n).coeff k ∈ I ^ n := by
        intro n
        have := coeff_of_map_zero (hfmod n) k
        rw [Polynomial.coeff_sub] at this
        exact Ideal.pow_le_pow_right (Nat.le_succ n) this
      have hz : f.coeff k - (Gpoly * Hpoly).coeff k = 0 := by
        refine IsHausdorff.haus' (I := I) (f.coeff k - (Gpoly * Hpoly).coeff k) (fun n => ?_)
        rw [SModEq.zero, smul_top,
          show f.coeff k - (Gpoly * Hpoly).coeff k
            = (f.coeff k - (G n * Hp n).coeff k) - ((Gpoly * Hpoly).coeff k - (G n * Hp n).coeff k)
            by ring]
        exact Ideal.sub_mem _ (approxfn n) (approxGH n)
      exact sub_eq_zero.mp hz
    -- Reductions mod `I` are `gbar, hbar`.
    have hGmapfinal : Gpoly.map (Ideal.Quotient.mk I) = gbar := by
      ext j
      rw [coeff_map]
      by_cases hj : j ≤ dG
      · rw [coeffGpoly, if_pos hj]
        have hmem := haG j 1
        rw [SModEq.sub_mem, smul_top, pow_one] at hmem
        have e1 : Ideal.Quotient.mk I (aG j) = Ideal.Quotient.mk I ((G 1).coeff j) := by
          rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
            show aG j - (G 1).coeff j = -((G 1).coeff j - aG j) by ring]
          exact neg_mem hmem
        rw [e1]
        simpa only [coeff_map] using congrArg (fun p => Polynomial.coeff p j) (hGmapI 1)
      · rw [coeffGpoly, if_neg (by omega), map_zero]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hdG ▸ not_le.mp hj)).symm
    have hHmapfinal : Hpoly.map (Ideal.Quotient.mk I) = hbar := by
      ext j
      rw [coeff_map]
      by_cases hj : j ≤ dH
      · rw [coeffHpoly, if_pos hj]
        have hmem := haH j 1
        rw [SModEq.sub_mem, smul_top, pow_one] at hmem
        have e1 : Ideal.Quotient.mk I (aH j) = Ideal.Quotient.mk I ((Hp 1).coeff j) := by
          rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
            show aH j - (Hp 1).coeff j = -((Hp 1).coeff j - aH j) by ring]
          exact neg_mem hmem
        rw [e1]
        simpa only [coeff_map] using congrArg (fun p => Polynomial.coeff p j) (hHmapI 1)
      · rw [coeffHpoly, if_neg (by omega), map_zero]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hdH ▸ not_le.mp hj)).symm
    exact ⟨Gpoly, Hpoly, hGmonic, hHmonic, hfactor, hGmapfinal, hHmapfinal⟩

/-- If `R` is complete for `I`, then it is Henselian for any power-comparable
larger ideal `J` with `I ≤ J` and `J^n ≤ I`. -/
theorem of_isAdicComplete_of_le_of_pow_le {I J : Ideal R} [IsAdicComplete I R]
    (hIJ : I ≤ J) {n : ℕ} (hn : J ^ n ≤ I) : IsHenselianPair R J :=
  (of_isAdicComplete (I := I)).of_le_of_pow_le hIJ hn

/-- If `R` is complete for `I`, then `(R, √I)` is a Henselian pair. -/
theorem of_isAdicComplete_radical {I : Ideal R} [IsAdicComplete I R] :
    IsHenselianPair R I.radical :=
  (iff_radical (I := I)).mp (of_isAdicComplete (I := I))

/-- If `R` is complete for `I` and `I ≤ J ≤ √I`, then `(R, J)` is a
Henselian pair. -/
theorem of_isAdicComplete_of_le_of_le_radical {I J : Ideal R} [IsAdicComplete I R]
    (hIJ : I ≤ J) (hJ : J ≤ I.radical) : IsHenselianPair R J :=
  (of_isAdicComplete (I := I)).of_le_of_le_radical hIJ hJ

/-- Same-radical form of completeness-implies-Henselian: if `R` is complete for
`I` and `I` and `J` have the same radical, then `(R, J)` is Henselian. -/
theorem of_isAdicComplete_of_radical_eq {I J : Ideal R} [IsAdicComplete I R]
    (hrad : I.radical = J.radical) : IsHenselianPair R J :=
  (iff_of_radical_eq hrad).mp (of_isAdicComplete (I := I))

section AlgebraMap

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Algebra-map form of completeness-implies-Henselian.  If an `R`-algebra `S`
is complete for the `I`-adic filtration coming from `R`, then `(S, IS)` is a
Henselian pair. -/
theorem of_isAdicComplete_map_algebra {I : Ideal R} [IsAdicComplete I S] :
    IsHenselianPair S (I.map (algebraMap R S)) := by
  haveI : IsAdicComplete (I.map (algebraMap R S)) S :=
    (IsAdicComplete.map_algebraMap_iff (I := I) (S := S) (M := S)).mpr inferInstance
  exact of_isAdicComplete (I := I.map (algebraMap R S))

/-- If an `R`-algebra `S` is complete for the `I`-adic filtration coming from
`R`, then it is Henselian at the radical of `IS`. -/
theorem of_isAdicComplete_map_algebra_radical {I : Ideal R} [IsAdicComplete I S] :
    IsHenselianPair S (I.map (algebraMap R S)).radical :=
  (iff_radical (I := I.map (algebraMap R S))).mp
    (of_isAdicComplete_map_algebra (R := R) (S := S) (I := I))

/-- Algebra-map form of the power-comparable 0ALJ wrapper. -/
theorem of_isAdicComplete_map_algebra_of_le_of_pow_le {I : Ideal R} {J : Ideal S}
    [IsAdicComplete I S] (hIJ : I.map (algebraMap R S) ≤ J) {n : ℕ}
    (hn : J ^ n ≤ I.map (algebraMap R S)) : IsHenselianPair S J :=
  (of_isAdicComplete_map_algebra (R := R) (S := S) (I := I)).of_le_of_pow_le hIJ hn

/-- Algebra-map form of the radical-bounded 0ALJ wrapper. -/
theorem of_isAdicComplete_map_algebra_of_le_of_le_radical {I : Ideal R} {J : Ideal S}
    [IsAdicComplete I S] (hIJ : I.map (algebraMap R S) ≤ J)
    (hJ : J ≤ (I.map (algebraMap R S)).radical) : IsHenselianPair S J :=
  (of_isAdicComplete_map_algebra (R := R) (S := S) (I := I)).of_le_of_le_radical hIJ hJ

/-- Same-radical algebra-map form of completeness-implies-Henselian. -/
theorem of_isAdicComplete_map_algebra_of_radical_eq {I : Ideal R} {J : Ideal S}
    [IsAdicComplete I S] (hrad : (I.map (algebraMap R S)).radical = J.radical) :
    IsHenselianPair S J :=
  (iff_of_radical_eq hrad).mp
    (of_isAdicComplete_map_algebra (R := R) (S := S) (I := I))

end AlgebraMap

section FiniteNoetherianAlgebra

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Finite-algebra complete case of the base-change theorem.  If `R` is
Noetherian and complete for `I`, then every finite `R`-algebra `S` is Henselian
at the extended ideal `IS`. -/
theorem of_isAdicComplete_map_algebra_of_finite_of_isNoetherian
    [IsNoetherianRing R] [Module.Finite R S] {I : Ideal R} [IsAdicComplete I R] :
    IsHenselianPair S (I.map (algebraMap R S)) := by
  haveI : IsAdicComplete I S :=
    IsAdicComplete.of_finite_module_of_isNoetherian (R := R) (M := S) (I := I)
  exact of_isAdicComplete_map_algebra (R := R) (S := S) (I := I)

/-- Radical form of the finite-algebra complete case. -/
theorem of_isAdicComplete_map_algebra_radical_of_finite_of_isNoetherian
    [IsNoetherianRing R] [Module.Finite R S] {I : Ideal R} [IsAdicComplete I R] :
    IsHenselianPair S (I.map (algebraMap R S)).radical :=
  (iff_radical (I := I.map (algebraMap R S))).mp
    (of_isAdicComplete_map_algebra_of_finite_of_isNoetherian
      (R := R) (S := S) (I := I))

/-- Power-comparable ideal form of the finite-algebra complete case. -/
theorem of_isAdicComplete_map_algebra_of_finite_of_isNoetherian_of_le_of_pow_le
    [IsNoetherianRing R] [Module.Finite R S] {I : Ideal R} {J : Ideal S}
    [IsAdicComplete I R] (hIJ : I.map (algebraMap R S) ≤ J) {n : ℕ}
    (hn : J ^ n ≤ I.map (algebraMap R S)) : IsHenselianPair S J :=
  (of_isAdicComplete_map_algebra_of_finite_of_isNoetherian
    (R := R) (S := S) (I := I)).of_le_of_pow_le hIJ hn

/-- Radical-bounded ideal form of the finite-algebra complete case. -/
theorem of_isAdicComplete_map_algebra_of_finite_of_isNoetherian_of_le_of_le_radical
    [IsNoetherianRing R] [Module.Finite R S] {I : Ideal R} {J : Ideal S}
    [IsAdicComplete I R] (hIJ : I.map (algebraMap R S) ≤ J)
    (hJ : J ≤ (I.map (algebraMap R S)).radical) : IsHenselianPair S J :=
  (of_isAdicComplete_map_algebra_of_finite_of_isNoetherian
    (R := R) (S := S) (I := I)).of_le_of_le_radical hIJ hJ

/-- Same-radical form of the finite-algebra complete case. -/
theorem of_isAdicComplete_map_algebra_of_finite_of_isNoetherian_of_radical_eq
    [IsNoetherianRing R] [Module.Finite R S] {I : Ideal R} {J : Ideal S}
    [IsAdicComplete I R] (hrad : (I.map (algebraMap R S)).radical = J.radical) :
    IsHenselianPair S J :=
  (iff_of_radical_eq hrad).mp
    (of_isAdicComplete_map_algebra_of_finite_of_isNoetherian
      (R := R) (S := S) (I := I))

end FiniteNoetherianAlgebra

end IsHenselianPair

/-- A local ring complete at its maximal ideal is a Henselian local ring.

This is a convenience corollary of the pair-level completeness theorem:
`IsHenselianPair.of_isAdicComplete` proves that `(R, maximalIdeal R)` is a Henselian pair,
and the easy local-ring bridge `IsHenselianPair.henselianLocalRing` gives mathlib's
`HenselianLocalRing` predicate. -/
theorem HenselianLocalRing.of_isAdicComplete_maximalIdeal [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R :=
  IsHenselianPair.of_isAdicComplete.henselianLocalRing

/-- A local ring complete at a positive power of its maximal ideal is Henselian. -/
theorem HenselianLocalRing.of_isAdicComplete_maximalIdeal_pow [IsLocalRing R]
    {n : ℕ} (hn : n ≠ 0) [IsAdicComplete ((IsLocalRing.maximalIdeal R) ^ n) R] :
    HenselianLocalRing R :=
  (IsHenselianPair.of_isAdicComplete
    (I := (IsLocalRing.maximalIdeal R) ^ n)).henselianLocalRing_of_maximalIdeal_pow hn

/-- A local ring complete at an ideal whose radical is the maximal ideal is
Henselian. -/
theorem HenselianLocalRing.of_isAdicComplete_of_radical_eq_maximalIdeal [IsLocalRing R]
    {I : Ideal R} [IsAdicComplete I R]
    (hrad : I.radical = IsLocalRing.maximalIdeal R) : HenselianLocalRing R :=
  (IsHenselianPair.of_isAdicComplete (I := I)).henselianLocalRing_of_radical_eq_maximalIdeal hrad
