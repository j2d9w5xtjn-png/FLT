/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Defs

/-!
# Square-zero ideals give Henselian pairs

This is the essential *infinitesimal lifting* step underlying the Stacks project result that a
locally nilpotent ideal makes `(R, I)` a Henselian pair (Stacks Tag 0ALI, the "henselian pair"
clause).  It is the single new *proof* that unlocks the nilpotent case of the theory (as opposed
to the `⊥` case in `FLT/Slop/HenselianPair.lean`, which is a transport along an isomorphism).

## Main results

* `IsHenselianPair.of_sq_eq_bot` — if `I ^ 2 = ⊥` (i.e. `I` is a square-zero ideal) then `(R, I)`
  is a Henselian pair.

## Implementation notes

Given a monic `f` whose reduction factors as `g0 * h0` with `g0, h0` monic and coprime over
`R ⧸ I`, we lift `g0, h0` to monic `G, H` over `R` of matching degree.  Then `δ := f - G * H` has
all coefficients in `I` and `degree δ` below `degree f`.  Using a Bézout identity
`u0 * g0 + v0 * h0 = 1` (from coprimality) and the fact that products of two `I`-coefficient
polynomials vanish (as `I ^ 2 = ⊥`), we solve `G * T + H * S = δ` for correction terms `S, T` with
`I`-coefficients, using polynomial division by the monic `G` to force the degree bound
`degree S < degree G`.  Then `(G + S) * (H + T) = f` exactly (the `S * T` cross term vanishes),
and `G + S`, `H + T` are the required monic lifts.  See the Stacks Project
(More on Algebra, §15.11, tags 0ALI/0ALJ) for how this feeds the complete/nilpotent theory.

## References

* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace IsHenselianPair

/-- If `p.map (Quotient.mk I) = 0` then every coefficient of `p` lies in `I`. -/
private theorem coeff_mem_of_map_eq_zero {I : Ideal R} {p : R[X]}
    (h : p.map (Ideal.Quotient.mk I) = 0) (n : ℕ) : p.coeff n ∈ I := by
  have hn := Polynomial.ext_iff.mp h n
  rwa [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at hn

/-- In a ring with a square-zero ideal `I`, the product of two polynomials whose
coefficients all lie in `I` is zero (each coefficient of the product lies in
`I ^ 2 = ⊥`). -/
private theorem mul_eq_zero_of_map_eq_zero {I : Ideal R} (hI : I ^ 2 = ⊥) {p q : R[X]}
    (hp : p.map (Ideal.Quotient.mk I) = 0) (hq : q.map (Ideal.Quotient.mk I) = 0) :
    p * q = 0 := by
  ext k
  rw [coeff_mul, coeff_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  have hmem : p.coeff x.1 * q.coeff x.2 ∈ I ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul (coeff_mem_of_map_eq_zero hp _) (coeff_mem_of_map_eq_zero hq _)
  rw [hI, Ideal.mem_bot] at hmem
  exact hmem

/-- **A square-zero ideal gives a Henselian pair** (Stacks Tag 0ALI, the
"henselian pair" clause, in the special case `I ^ 2 = ⊥`).  This is the core
infinitesimal factorisation-lifting step. -/
@[stacks 0ALI "square-zero case"]
theorem of_sq_eq_bot {I : Ideal R} (hI : I ^ 2 = ⊥) : IsHenselianPair R I where
  le_jacobson := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    have hxy : x * y ∈ I := I.mul_mem_right y hx
    have hsq : (x * y) ^ 2 = 0 := by
      have hmem : (x * y) ^ 2 ∈ I ^ 2 := by rw [sq, sq]; exact Ideal.mul_mem_mul hxy hxy
      rwa [hI, Ideal.mem_bot] at hmem
    exact (IsNilpotent.isUnit_add_one ⟨2, hsq⟩ : IsUnit (x * y + 1))
  exists_lift_factorization := by
    intro f hf g₀ h₀ hg₀ hh₀ hcop hfact
    set mk := Ideal.Quotient.mk I with hmk
    rcases subsingleton_or_nontrivial R with _ | hnt
    · -- Everything is trivial over a subsingleton ring.
      haveI : Subsingleton (R ⧸ I) := Function.Surjective.subsingleton Ideal.Quotient.mk_surjective
      haveI : Subsingleton (R ⧸ I)[X] := inferInstance
      exact ⟨f, 1, hf, monic_one, (mul_one f).symm,
        Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    -- `I ≠ ⊤`, so `R ⧸ I` is nontrivial.
    have hItop : I ≠ ⊤ := by
      intro htop
      have h1I : (1 : R) ∈ I := htop ▸ Submodule.mem_top
      have hmem : (1 : R) ∈ I ^ 2 := by rw [sq]; simpa using Ideal.mul_mem_mul h1I h1I
      rw [hI, Ideal.mem_bot] at hmem
      exact one_ne_zero hmem
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    -- Lift `g₀, h₀` to monic `G, H` over `R` of matching degree.
    obtain ⟨G, hGmap, hGdeg, hGmon⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic
        (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective g₀) hg₀
    obtain ⟨H, hHmap, hHdeg, hHmon⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic
        (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective h₀) hh₀
    -- Lift a Bézout identity for `g₀, h₀`.
    obtain ⟨u₀, v₀, hbez⟩ := hcop
    obtain ⟨u, hu⟩ := Polynomial.map_surjective mk Ideal.Quotient.mk_surjective u₀
    obtain ⟨v, hv⟩ := Polynomial.map_surjective mk Ideal.Quotient.mk_surjective v₀
    -- The defect and its Bézout "witness of the error".
    set δ : R[X] := f - G * H with hδ_def
    set w : R[X] := u * G + v * H - 1 with hw_def
    have hGHmon : (G * H).Monic := hGmon.mul hHmon
    have hδmap : δ.map mk = 0 := by
      rw [hδ_def, Polynomial.map_sub, hfact, Polynomial.map_mul, hGmap, hHmap, sub_self]
    have hwmap : w.map mk = 0 := by
      rw [hw_def, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        hu, hv, hGmap, hHmap, Polynomial.map_one, hbez, sub_self]
    have hδw : δ * w = 0 := mul_eq_zero_of_map_eq_zero hI hδmap hwmap
    -- Key Bézout consequence: `G * (δ * u) + H * (δ * v) = δ`.
    have hkey : G * (δ * u) + H * (δ * v) = δ := by
      have hexp : δ * (u * G + v * H) = δ := by
        have huv : u * G + v * H = w + 1 := by rw [hw_def]; ring
        rw [huv, mul_add, mul_one, hδw, zero_add]
      rw [show G * (δ * u) + H * (δ * v) = δ * (u * G + v * H) from by ring]
      exact hexp
    -- Divide `δ * v` by the monic `G` to control degrees.
    set S : R[X] := (δ * v) %ₘ G with hS_def
    set Q : R[X] := (δ * v) /ₘ G with hQ_def
    set T : R[X] := δ * u + H * Q with hT_def
    have hSGQ : S + G * Q = δ * v := Polynomial.modByMonic_add_div (δ * v) G
    have hkey2 : G * T + H * S = δ := by
      have e : G * T + H * S = G * (δ * u) + H * (S + G * Q) := by rw [hT_def]; ring
      rw [e, hSGQ]; exact hkey
    -- The correction terms have `I`-coefficients.
    have hSmap : S.map mk = 0 := by
      rw [hS_def, Polynomial.map_modByMonic mk hGmon, Polynomial.map_mul, hδmap, zero_mul,
        zero_modByMonic]
    have hTmap : T.map mk = 0 := by
      have hQmap : Q.map mk = 0 := by
        rw [hQ_def, Polynomial.map_divByMonic mk hGmon, Polynomial.map_mul, hδmap, zero_mul,
          zero_divByMonic]
      rw [hT_def, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hδmap, zero_mul,
        zero_add, hQmap, mul_zero]
    have hST : S * T = 0 := mul_eq_zero_of_map_eq_zero hI hSmap hTmap
    -- Degree bookkeeping.
    have hGne : degree G ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hGmon.ne_zero
    have hHne : degree H ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hHmon.ne_zero
    have hnatf : f.natDegree = G.natDegree + H.natDegree := by
      have hmapdeg : (f.map mk).natDegree = f.natDegree := hf.natDegree_map mk
      rw [hfact, hg₀.natDegree_mul hh₀] at hmapdeg
      rw [← hmapdeg, hGdeg, hHdeg]
    have hdegf : degree f = degree (G * H) := by
      rw [degree_eq_natDegree hf.ne_zero, degree_eq_natDegree hGHmon.ne_zero,
        hGmon.natDegree_mul hHmon]
      exact_mod_cast hnatf
    have hdegGH : degree (G * H) = degree G + degree H := hHmon.degree_mul
    have hδdeg : degree δ < degree f :=
      degree_sub_lt hdegf hf.ne_zero (hf.leadingCoeff.trans hGHmon.leadingCoeff.symm)
    have hSdeg : degree S < degree G := degree_modByMonic_lt (δ * v) hGmon
    have hTdeg : degree T < degree H := by
      have hGT : degree (G * T) = degree T + degree G := by rw [mul_comm]; exact hGmon.degree_mul
      have hHS : degree (H * S) = degree S + degree H := by rw [mul_comm]; exact hHmon.degree_mul
      have hbound : degree (G * T) < degree G + degree H := by
        have hGTeq : G * T = δ - H * S := by rw [← hkey2]; ring
        rw [hGTeq]
        refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
        · exact hδdeg.trans_eq (hdegf.trans hdegGH)
        · rw [hHS, add_comm (degree S) (degree H), add_comm (degree G) (degree H)]
          exact (WithBot.add_lt_add_iff_left hHne).mpr hSdeg
      rw [hGT] at hbound
      rw [add_comm (degree G) (degree H)] at hbound
      exact (WithBot.add_lt_add_iff_right hGne).mp hbound
    -- Assemble the lifted factorisation.
    refine ⟨G + S, H + T, hGmon.add_of_left hSdeg, hHmon.add_of_left hTdeg, ?_, ?_, ?_⟩
    · have hprod : (G + S) * (H + T) = f := by
        have hexpand : (G + S) * (H + T) = G * H + (G * T + H * S) + S * T := by ring
        rw [hexpand, hST, add_zero, hkey2, hδ_def]; ring
      exact hprod.symm
    · rw [Polynomial.map_add, hGmap, hSmap, add_zero]
    · rw [Polynomial.map_add, hHmap, hTmap, add_zero]

end IsHenselianPair
