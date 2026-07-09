/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Nilpotent

/-!
# Enlarging the ideal of a Henselian pair within its radical

This is the "enlargement" half of Stacks Tag 09XJ (`V(I) = V(J)` implies the pairs `(A, I)` and
`(A, J)` are equivalently Henselian) and a corollary of the hard direction of Tag 0DYD, combined
with the locally nilpotent case of Tag 0ALI.

If `(R, I)` is a Henselian pair, `I ⊆ J`, and `J ⊆ radical I`, then `(R, J)` is again a Henselian
pair.  Consequently the Henselian-pair condition on `(R, I)` only depends on `radical I`, and it
is stable under passing to powers, to sups with nilpotent/radical-bounded ideals, and along
radical-preserving comparisons.

## Main results

* `IsHenselianPair.of_le_of_le_radical` — enlargement within the radical: `I ≤ J ≤ radical I`
  preserves the Henselian-pair condition.
* `IsHenselianPair.iff_radical` — `(R, I)` is Henselian iff `(R, radical I)` is.
* `IsHenselianPair.iff_pow` / `pow` / `of_pow` — invariance under passing to powers `I ^ n`.
* `IsHenselianPair.iff_of_radical_eq` — equal radicals give equivalent Henselian-pair conditions.
* `IsHenselianPair.sup_of_isNilpotent` — adjoining a nilpotent ideal to `I` preserves the
  Henselian-pair condition (Stacks Tag 0G1R).
* `IsHenselianPair.iff_sup_quotient_right` / `iff_sup_quotient_left` — the sum `I ⊔ J` is
  Henselian iff `I` is and the image of `J` in `R ⧸ I` is (Stacks Tag 0DYD).
* `IsHenselianPair.henselianLocalRing_of_radical_eq_maximalIdeal` and
  `henselianLocalRing_of_maximalIdeal_pow` — local-ring corollaries.

## Implementation notes

The shrinking direction is unconditional and lives in `Pair/Quotient.lean` as
`IsHenselianPair.of_le`: if `(R, J)` is a Henselian pair and `I ≤ J`, then so is `(R, I)`, with no
nilpotence or radical hypothesis. Every `iff` below therefore discharges its reverse implication by
`of_le`, and the hypotheses are needed only for the enlarging direction.

## References

* [Stacks Project, Tag 09XJ](https://stacks.math.columbia.edu/tag/09XJ)
* [Stacks Project, Tag 0DYD](https://stacks.math.columbia.edu/tag/0DYD)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 0G1R](https://stacks.math.columbia.edu/tag/0G1R)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace Ideal

/-- Modulo the left summand of a binary sum, the image of the sum is just the
image of the right summand. -/
theorem map_sup_quotient_left (I J : Ideal R) :
    (I ⊔ J).map (Ideal.Quotient.mk I) = J.map (Ideal.Quotient.mk I) := by
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

/-- Modulo the right summand of a binary sum, the image of the sum is just the
image of the left summand. -/
theorem map_sup_quotient_right (I J : Ideal R) :
    (I ⊔ J).map (Ideal.Quotient.mk J) = I.map (Ideal.Quotient.mk J) := by
  rw [sup_comm, map_sup_quotient_left]

end Ideal

namespace IsHenselianPair

/-- **Power-comparable enlargement** (a compatibility form of Stacks Tag 09XJ).
If `(R, I)` is a Henselian pair, `I ≤ J`, and `J ^ n ≤ I` for some `n` (so
`J / I` is nilpotent), then `(R, J)` is a Henselian pair. -/
theorem of_le_of_pow_le {I J : Ideal R} (h : IsHenselianPair R I) (hIJ : I ≤ J)
    {n : ℕ} (hn : J ^ n ≤ I) : IsHenselianPair R J := by
  -- `J` lies in the Jacobson radical: `jacobson ⊥` is a radical ideal and
  -- `J ^ n ≤ I ≤ jacobson ⊥`, so `J ≤ jacobson ⊥`.
  have hJjac : J ≤ Ideal.jacobson (⊥ : Ideal R) := fun x hx =>
    Ideal.isRadical_jacobson (⊥ : Ideal R)
      (Ideal.mem_radical_iff.mpr ⟨n, le_trans hn h.le_jacobson (Ideal.pow_mem_pow hx n)⟩)
  -- `J / I` is nilpotent because `J ^ n ≤ I`.
  have hnil : IsNilpotent (J.map (Ideal.Quotient.mk I)) :=
    Ideal.isNilpotent_map_quotient_of_pow_le hn
  -- Dévissage: `(R, I)` Henselian and `(R/I, J/I)` Henselian (nilpotent) give `(R, J)`.
  exact of_quotient hIJ h (of_isNilpotent hnil)

/-- Power-comparable ideals define equivalent Henselian-pair conditions.  This is
the power-comparable case of Stacks Tag 09XJ. -/
theorem iff_of_le_of_pow_le {I J : Ideal R} (hIJ : I ≤ J) {n : ℕ} (hn : J ^ n ≤ I) :
    IsHenselianPair R I ↔ IsHenselianPair R J :=
  ⟨fun h => of_le_of_pow_le h hIJ hn, fun h => h.of_le hIJ⟩

/-- **Enlargement within the radical** (Stacks Tag 09XJ, enlarging direction).
If `(R, I)` is Henselian, `I ≤ J`, and `J ≤ √I`, then `(R, J)` is Henselian. -/
@[stacks 09XJ]
theorem of_le_of_le_radical {I J : Ideal R} (h : IsHenselianPair R I) (hIJ : I ≤ J)
    (hJ : J ≤ I.radical) : IsHenselianPair R J :=
  of_le_of_quotient hIJ h
    (of_le_nilradical (Ideal.map_quotient_le_nilradical_of_le_radical hJ))

/-- If `I ≤ J ≤ √I`, then `(R, I)` is Henselian iff `(R, J)` is Henselian. -/
theorem iff_of_le_of_le_radical {I J : Ideal R} (hIJ : I ≤ J) (hJ : J ≤ I.radical) :
    IsHenselianPair R I ↔ IsHenselianPair R J :=
  ⟨fun h => of_le_of_le_radical h hIJ hJ, fun h => h.of_le hIJ⟩

/-- Enlargement when the quotient ideal `J / I` is nilpotent, phrased directly
as nilpotence of the image of `J` in `R ⧸ I`. -/
theorem of_le_of_isNilpotent_map_quotient {I J : Ideal R} (h : IsHenselianPair R I)
    (hIJ : I ≤ J) (hJ : IsNilpotent (J.map (Ideal.Quotient.mk I))) :
    IsHenselianPair R J := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_isNilpotent_map_quotient hJ
  exact of_le_of_pow_le h hIJ hn

/-- Replacing an ideal by a positive power does not change the Henselian-pair
condition. -/
theorem iff_pow {I : Ideal R} {n : ℕ} (hn : n ≠ 0) :
    IsHenselianPair R (I ^ n) ↔ IsHenselianPair R I :=
  iff_of_le_of_pow_le (Ideal.pow_le_self hn) (n := n) le_rfl

/-- If `(R, I)` is a Henselian pair, then so is `(R, I ^ n)` for `n > 0`. -/
theorem pow {I : Ideal R} (h : IsHenselianPair R I) {n : ℕ} (hn : n ≠ 0) :
    IsHenselianPair R (I ^ n) :=
  (iff_pow hn).mpr h

/-- If `(R, I ^ n)` is a Henselian pair for `n > 0`, then so is `(R, I)`. -/
theorem of_pow {I : Ideal R} {n : ℕ} (hn : n ≠ 0) (h : IsHenselianPair R (I ^ n)) :
    IsHenselianPair R I :=
  (iff_pow hn).mp h

/-- Passing from an ideal to its radical does not change the Henselian-pair
condition. -/
theorem iff_radical {I : Ideal R} : IsHenselianPair R I ↔ IsHenselianPair R I.radical :=
  iff_of_le_of_le_radical Ideal.le_radical le_rfl

/-- Adding an ideal that is nilpotent modulo `I` does not change the
Henselian-pair condition.  If `J ^ n ≤ I`, then `(R, I)` is Henselian iff
`(R, I ⊔ J)` is Henselian. -/
theorem iff_sup_of_pow_le {I J : Ideal R} {n : ℕ} (hn : J ^ n ≤ I) :
    IsHenselianPair R I ↔ IsHenselianPair R (I ⊔ J) := by
  rcases n with _ | n
  · have hItop : I = ⊤ := by
      rw [pow_zero, Ideal.one_eq_top] at hn
      exact le_antisymm le_top hn
    rw [hItop, top_sup_eq]
  · have hpow : (I ⊔ J) ^ (1 + Nat.succ n) ≤ I := by
      exact (Ideal.sup_pow_add_le_pow_sup_pow (I := I) (J := J)
        (n := 1) (m := Nat.succ n)).trans (by
          rw [pow_one]
          exact sup_le le_rfl hn)
    exact iff_of_le_of_pow_le le_sup_left hpow

/-- Adding an ideal that is nilpotent modulo `I`, phrased as nilpotence of its
image in `R ⧸ I`, does not change the Henselian-pair condition. -/
theorem iff_sup_of_isNilpotent_map_quotient {I J : Ideal R}
    (hJ : IsNilpotent (J.map (Ideal.Quotient.mk I))) :
    IsHenselianPair R I ↔ IsHenselianPair R (I ⊔ J) := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_isNilpotent_map_quotient hJ
  exact iff_sup_of_pow_le hn

/-- Adding a nilpotent ideal does not change the Henselian-pair condition. -/
theorem iff_sup_of_isNilpotent {I J : Ideal R} (hJ : IsNilpotent J) :
    IsHenselianPair R I ↔ IsHenselianPair R (I ⊔ J) :=
  iff_sup_of_isNilpotent_map_quotient (I := I) (J := J)
    (Ideal.isNilpotent_map (Ideal.Quotient.mk I) hJ)

/-- If `(R, I)` is Henselian and `J` is nilpotent, then `(R, I ⊔ J)` is
Henselian.  This is the nilpotent-addend case of the sum theorem (Stacks Tag
0G1R). -/
@[stacks 0G1R]
theorem sup_of_isNilpotent {I J : Ideal R} (h : IsHenselianPair R I)
    (hJ : IsNilpotent J) : IsHenselianPair R (I ⊔ J) :=
  (iff_sup_of_isNilpotent hJ).mp h

/-- Symmetric nilpotent-addend form of `sup_of_isNilpotent`. -/
theorem sup_of_isNilpotent_left {I J : Ideal R} (hI : IsNilpotent I)
    (h : IsHenselianPair R J) : IsHenselianPair R (I ⊔ J) := by
  rw [sup_comm]
  exact h.sup_of_isNilpotent hI

/-- **Quotient form of the sum criterion.**  A binary sum `I ⊔ J` is Henselian
exactly when `I` is Henselian and the image of `J` is Henselian after quotienting
by `I`.

This is Stacks Tag 0DYD applied to `I ≤ I ⊔ J`, with the quotient ideal
identified as `J·(R ⧸ I)`.  It is the main reduction needed for the full sum
theorem (Stacks Tag 0G1R). -/
theorem iff_sup_quotient_right {I J : Ideal R} :
    IsHenselianPair R (I ⊔ J) ↔
      IsHenselianPair R I ∧ IsHenselianPair (R ⧸ I) (J.map (Ideal.Quotient.mk I)) := by
  simpa [Ideal.map_sup_quotient_left]
    using (iff_of_le_quotient (R := R) (I := I) (J := I ⊔ J) le_sup_left)

/-- If `(R, I)` is Henselian and the image of `J` in `R ⧸ I` is Henselian, then
the sum pair `(R, I ⊔ J)` is Henselian. -/
theorem sup_of_quotient_right {I J : Ideal R} (hI : IsHenselianPair R I)
    (hJ : IsHenselianPair (R ⧸ I) (J.map (Ideal.Quotient.mk I))) :
    IsHenselianPair R (I ⊔ J) :=
  (iff_sup_quotient_right (R := R) (I := I) (J := J)).mpr ⟨hI, hJ⟩

/-- If `(R, I ⊔ J)` is Henselian, then the image of `J` in `R ⧸ I` is
Henselian. -/
theorem quotient_right_of_sup {I J : Ideal R} (h : IsHenselianPair R (I ⊔ J)) :
    IsHenselianPair (R ⧸ I) (J.map (Ideal.Quotient.mk I)) :=
  ((iff_sup_quotient_right (R := R) (I := I) (J := J)).mp h).2

/-- Symmetric quotient form of the sum criterion, quotienting by `J` instead of
`I`. -/
theorem iff_sup_quotient_left {I J : Ideal R} :
    IsHenselianPair R (I ⊔ J) ↔
      IsHenselianPair R J ∧ IsHenselianPair (R ⧸ J) (I.map (Ideal.Quotient.mk J)) := by
  simpa [sup_comm] using (iff_sup_quotient_right (R := R) (I := J) (J := I))

/-- Symmetric form of `sup_of_quotient_right`. -/
theorem sup_of_quotient_left {I J : Ideal R} (hJ : IsHenselianPair R J)
    (hI : IsHenselianPair (R ⧸ J) (I.map (Ideal.Quotient.mk J))) :
    IsHenselianPair R (I ⊔ J) :=
  (iff_sup_quotient_left (R := R) (I := I) (J := J)).mpr ⟨hJ, hI⟩

/-- Symmetric form of `quotient_right_of_sup`. -/
theorem quotient_left_of_sup {I J : Ideal R} (h : IsHenselianPair R (I ⊔ J)) :
    IsHenselianPair (R ⧸ J) (I.map (Ideal.Quotient.mk J)) :=
  ((iff_sup_quotient_left (R := R) (I := I) (J := J)).mp h).2

/-- Adding an ideal whose image in `R ⧸ I` is contained in the nilradical does
not change the Henselian-pair condition.  This is the quotient-image form of
`iff_sup_of_le_radical`. -/
theorem iff_sup_of_map_quotient_le_nilradical {I J : Ideal R}
    (hJ : J.map (Ideal.Quotient.mk I) ≤ nilradical (R ⧸ I)) :
    IsHenselianPair R I ↔ IsHenselianPair R (I ⊔ J) := by
  refine ⟨fun hI => ?_, fun hsup => hsup.of_le le_sup_left⟩
  exact sup_of_quotient_right hI (of_le_nilradical hJ)

/-- Same-radical invariance (Stacks Tag 09XJ).  If `I` and `J` have the same
radical, then `(R, I)` is Henselian iff `(R, J)` is Henselian. -/
theorem iff_of_radical_eq {I J : Ideal R} (hrad : I.radical = J.radical) :
    IsHenselianPair R I ↔ IsHenselianPair R J := by
  calc
    IsHenselianPair R I ↔ IsHenselianPair R I.radical := iff_radical
    _ ↔ IsHenselianPair R J.radical := by rw [hrad]
    _ ↔ IsHenselianPair R J := iff_radical.symm

/-- If a local ring is Henselian as a pair at a positive power of its maximal
ideal, then it is a Henselian local ring. -/
theorem henselianLocalRing_of_maximalIdeal_pow [IsLocalRing R] {n : ℕ}
    (h : IsHenselianPair R ((IsLocalRing.maximalIdeal R) ^ n)) (hn : n ≠ 0) :
    HenselianLocalRing R :=
  (of_pow hn h).henselianLocalRing

/-- If a local ring is Henselian as a pair at an ideal whose radical is the
maximal ideal, then it is a Henselian local ring. -/
theorem henselianLocalRing_of_radical_eq_maximalIdeal [IsLocalRing R]
    {I : Ideal R} (h : IsHenselianPair R I)
    (hrad : I.radical = IsLocalRing.maximalIdeal R) : HenselianLocalRing R := by
  have hradmax :
      (IsLocalRing.maximalIdeal R).radical = IsLocalRing.maximalIdeal R :=
    (show (IsLocalRing.maximalIdeal R).IsPrime from inferInstance).radical
  have hrad' : I.radical = (IsLocalRing.maximalIdeal R).radical := by
    rw [hradmax, hrad]
  exact ((iff_of_radical_eq hrad').mp h).henselianLocalRing

end IsHenselianPair
