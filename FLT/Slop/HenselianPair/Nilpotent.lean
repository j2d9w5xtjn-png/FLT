/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Quotient
public import FLT.Slop.HenselianPair.SquareZero
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Nilpotent ideals give Henselian pairs

The general case of Stacks Tag 0ALI.

Building on the square-zero case (`FLT/Slop/HenselianPair/SquareZero.lean`), we prove that if
`I` is a *nilpotent* ideal (`I ^ N = ⊥` for some `N`) then `(R, I)` is a Henselian
pair.  The proof is a dévissage: writing `K := I ^ n`, the ideal `K` is square-zero
in `R` (so `(R, K)` is a Henselian pair by `of_sq_eq_bot`), while the image of `I`
in `R ⧸ K` is nilpotent of smaller index, so `(R ⧸ K, I·(R ⧸ K))` is a Henselian
pair by induction.  Given a coprime monic factorisation of `f mod I`, we first lift
it to `R ⧸ K` using the inductive hypothesis, then lift *that* to `R` using the
square-zero result — the second lift needs coprimality over `R ⧸ K`, which we obtain
by lifting coprimality along the nilpotent ideal `I·(R ⧸ K)`.

## Main results

* `isCoprime_of_isNilpotent_of_map` — coprimality of polynomials lifts along a
  surjection with nilpotent kernel.
* `IsHenselianPair.of_pow_eq_bot` — `I ^ N = ⊥ ⇒ (R, I)` is a Henselian pair.
* `IsHenselianPair.of_isNilpotent` — the same phrased with `IsNilpotent I`.
* `IsHenselianPair.of_le_nilradical` — the full locally nilpotent pair clause of
  Stacks Tag 0ALI (`I ≤ nilradical R`).
* `IsHenselianPair.factorization_unique` — the coprime monic factorisation lift is
  unique over a nilpotent ideal.
* `HenselianLocalRing.of_isNilpotent_maximalIdeal` — a local ring with nilpotent
  maximal ideal is Henselian; in particular every Artinian local ring is.

## References

* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
-/

@[expose] public section

open Polynomial

universe u

variable {R : Type*} [CommRing R]

/-- An element of a nilpotent ideal is nilpotent. -/
theorem Ideal.isNilpotent_of_mem {S : Type*} [CommRing S] {J : Ideal S}
    (hJ : IsNilpotent J) {x : S} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have hmem : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hmem
  simpa using hmem

/-- If a polynomial maps to zero modulo an ideal, every coefficient lies in that ideal. -/
theorem Polynomial.coeff_mem_ideal_of_map_quotient_eq_zero {I : Ideal R} {p : R[X]}
    (hp : p.map (Ideal.Quotient.mk I) = 0) (n : ℕ) : p.coeff n ∈ I := by
  have hn : (p.map (Ideal.Quotient.mk I)).coeff n = 0 := by
    simpa using congrArg (fun q : (R ⧸ I)[X] => q.coeff n) hp
  rwa [coeff_map, Ideal.Quotient.eq_zero_iff_mem] at hn

/-- **Coprimality lifts along a nilpotent ideal.** If `J` is a nilpotent ideal of a
commutative ring `S` and the reductions of `g, h : S[X]` modulo `J` are coprime, then
`g` and `h` are themselves coprime. -/
theorem isCoprime_of_isNilpotent_of_map {S : Type*} [CommRing S] {J : Ideal S}
    (hJ : IsNilpotent J) {g h : S[X]}
    (hco : IsCoprime (g.map (Ideal.Quotient.mk J)) (h.map (Ideal.Quotient.mk J))) :
    IsCoprime g h := by
  set mk := Ideal.Quotient.mk J with hmk
  obtain ⟨a₀, b₀, hab⟩ := hco
  obtain ⟨a, ha⟩ := Polynomial.map_surjective mk Ideal.Quotient.mk_surjective a₀
  obtain ⟨b, hb⟩ := Polynomial.map_surjective mk Ideal.Quotient.mk_surjective b₀
  set u : S[X] := a * g + b * h with hu
  have hmap : u.map mk = 1 := by
    rw [hu, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ha, hb]; exact hab
  -- Each coefficient of `u` except the constant one is nilpotent; the constant one is a unit.
  have hcoeff_mem : ∀ i, i ≠ 0 → u.coeff i ∈ J := by
    intro i hi
    have h1 : (u.map mk).coeff i = 0 := by rw [hmap, coeff_one, if_neg hi]
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hconst : u.coeff 0 - 1 ∈ J := by
    have h1 : (u.map mk).coeff 0 = 1 := by rw [hmap, coeff_one, if_pos rfl]
    rw [coeff_map] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
  have hunit0 : IsUnit (u.coeff 0) := by
    have : u.coeff 0 = 1 + (u.coeff 0 - 1) := by ring
    rw [this]
    exact IsNilpotent.isUnit_one_add (Ideal.isNilpotent_of_mem hJ hconst)
  have hnil : ∀ i, i ≠ 0 → IsNilpotent (u.coeff i) := fun i hi =>
    Ideal.isNilpotent_of_mem hJ (hcoeff_mem i hi)
  have huunit : IsUnit u := Polynomial.isUnit_of_coeff_isUnit_isNilpotent hunit0 hnil
  obtain ⟨u', hu'⟩ := huunit.exists_left_inv
  refine ⟨u' * a, u' * b, ?_⟩
  have hexp : u' * a * g + u' * b * h = u' * u := by rw [hu]; ring
  rw [hexp]; exact hu'

namespace IsHenselianPair

/-- Auxiliary induction on the nilpotency index for `of_pow_eq_bot`.  Quantifying over
all rings is needed because the inductive step passes to the quotient `R ⧸ Iⁿ`. -/
private theorem of_pow_eq_bot_aux (N : ℕ) :
    ∀ {R : Type*} [CommRing R] (I : Ideal R), I ^ N = ⊥ → IsHenselianPair R I := by
  induction N with
  | zero =>
    intro R _ I hI
    rw [pow_zero, Ideal.one_eq_top] at hI
    have hIbot : I = ⊥ := le_antisymm (hI ▸ le_top) bot_le
    rw [hIbot]; exact IsHenselianPair.bot
  | succ n ih =>
    intro R _ I hI
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one] at hI; rw [hI]; exact IsHenselianPair.bot
    · -- `n ≥ 1`: set `K := Iⁿ`, square-zero, and dévissage over `R ⧸ K`.
      set K : Ideal R := I ^ n with hK
      have hKI : K ≤ I := by rw [hK]; exact Ideal.pow_le_self (by omega)
      have hK2 : K ^ 2 = ⊥ := by
        rw [hK, ← pow_mul]
        exact le_antisymm (le_trans (Ideal.pow_le_pow_right (by omega)) hI.le) bot_le
      have hI'pow : (I.map (Ideal.Quotient.mk K)) ^ n = ⊥ := by
        rw [← Ideal.map_pow, ← hK, Ideal.map_quotient_self]
      have hIjac : I ≤ Ideal.jacobson ⊥ := by
        intro x hx
        rw [Ideal.mem_jacobson_bot]
        intro y
        exact (Ideal.isNilpotent_of_mem (⟨n + 1, by rw [hI, Ideal.zero_eq_bot]⟩ : IsNilpotent I)
          (I.mul_mem_right y hx)).isUnit_add_one
      exact of_quotient hKI (of_sq_eq_bot hK2) (ih _ hI'pow)

/-- **A nilpotent ideal gives a Henselian pair** (Stacks Tag 0ALI, the "henselian pair"
clause).  If `I ^ N = ⊥` for some `N`, then `(R, I)` is a Henselian pair. -/
theorem of_pow_eq_bot {I : Ideal R} {N : ℕ} (hI : I ^ N = ⊥) : IsHenselianPair R I :=
  of_pow_eq_bot_aux N I hI

/-- **A nilpotent ideal gives a Henselian pair** (Stacks Tag 0ALI), phrased via
`IsNilpotent`. -/
theorem of_isNilpotent {I : Ideal R} (hI : IsNilpotent I) : IsHenselianPair R I := by
  obtain ⟨N, hN⟩ := hI
  exact of_pow_eq_bot (hN.trans Ideal.zero_eq_bot)

/-- An ideal contained in the nilradical is contained in the Jacobson radical. -/
theorem le_jacobson_bot_of_le_nilradical {I : Ideal R} (hI : I ≤ nilradical R) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxnil : IsNilpotent x := (mem_nilradical.mp (hI hx))
  have hxy : IsNilpotent (x * y) := by
    simpa [mul_comm] using (Commute.all y x).isNilpotent_mul_left hxnil
  exact hxy.isUnit_add_one

/-- Nilpotence of ideals is preserved by image under any ring homomorphism. -/
theorem _root_.Ideal.isNilpotent_map {S : Type*} [CommRing S] (f : R →+* S) {I : Ideal R}
    (hI : IsNilpotent I) : IsNilpotent (I.map f) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have hbot : I ^ n = (⊥ : Ideal R) := hn.trans Ideal.zero_eq_bot
  rw [Ideal.zero_eq_bot, ← Ideal.map_pow, hbot, Ideal.map_bot]

/-- If a map kills a power of an ideal, then the image ideal is nilpotent. -/
theorem _root_.Ideal.isNilpotent_map_of_pow_le_ker {S : Type*} [CommRing S] (f : R →+* S)
    {I : Ideal R} {n : ℕ} (hn : I ^ n ≤ RingHom.ker f) : IsNilpotent (I.map f) := by
  refine ⟨n, ?_⟩
  rw [Ideal.zero_eq_bot, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
  exact hn

/-- If `J ^ n ≤ I`, then the image of `J` in `R ⧸ I` is nilpotent. -/
theorem _root_.Ideal.isNilpotent_map_quotient_of_pow_le {I J : Ideal R} {n : ℕ}
    (hn : J ^ n ≤ I) : IsNilpotent (J.map (Ideal.Quotient.mk I)) := by
  exact Ideal.isNilpotent_map_of_pow_le_ker (Ideal.Quotient.mk I)
    (by simpa [Ideal.mk_ker] using hn)

/-- If the image of `J` in `R ⧸ I` is nilpotent, then some power of `J` lies in `I`. -/
theorem _root_.Ideal.exists_pow_le_of_isNilpotent_map_quotient {I J : Ideal R}
    (hJ : IsNilpotent (J.map (Ideal.Quotient.mk I))) : ∃ n, J ^ n ≤ I := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have hmap : (J ^ n).map (Ideal.Quotient.mk I) = ⊥ := by
    rw [Ideal.map_pow, hn, Ideal.zero_eq_bot]
  have hker : J ^ n ≤ RingHom.ker (Ideal.Quotient.mk I) :=
    (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk I)).mp hmap
  simpa [Ideal.mk_ker] using hker

/-- The image of an ideal contained in the nilradical is contained in the
nilradical. -/
theorem _root_.Ideal.map_le_nilradical {S : Type*} [CommRing S] (f : R →+* S)
    {I : Ideal R} (hI : I ≤ nilradical R) : I.map f ≤ nilradical S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact mem_nilradical.mpr ((mem_nilradical.mp (hI hx)).map f)

/-- If `J ≤ √I`, then the image of `J` in `R ⧸ I` lies in the nilradical. -/
theorem _root_.Ideal.map_quotient_le_nilradical_of_le_radical {I J : Ideal R}
    (hJ : J ≤ I.radical) : J.map (Ideal.Quotient.mk I) ≤ nilradical (R ⧸ I) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hJ hx)
  rw [Ideal.mem_comap]
  exact mem_nilradical.mpr ⟨n, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hn⟩

/-- **A locally nilpotent ideal gives a Henselian pair** (Stacks Tag 0ALI, the
"henselian pair" clause).  Here "locally nilpotent" is expressed as
`I ≤ nilradical R`, i.e. every element of `I` is nilpotent.

The proof reduces each requested factorisation to the nilpotent case.  Choose
monic lifts `G, H` of the prescribed factors and lifts `u, v` of a Bézout
identity.  The finitely many coefficients of the factorisation defect
`f - G*H` and the Bézout defect `u*G + v*H - 1` generate a finitely generated
subideal `K ≤ I`; since `K ≤ nilradical R`, this `K` is nilpotent.  The already
proved nilpotent case gives a lift modulo `K`, and hence modulo `I`. -/
@[stacks 0ALI]
theorem of_le_nilradical {I : Ideal R} (hI : I ≤ nilradical R) : IsHenselianPair R I where
  le_jacobson := le_jacobson_bot_of_le_nilradical hI
  exists_lift_factorization := by
    intro f hf g₀ h₀ hg₀ hh₀ hcop hfact
    rcases subsingleton_or_nontrivial R with _ | hnt
    · haveI : Subsingleton (R ⧸ I) :=
        Function.Surjective.subsingleton Ideal.Quotient.mk_surjective
      haveI : Subsingleton (R ⧸ I)[X] := inferInstance
      exact ⟨f, 1, hf, monic_one, (mul_one f).symm,
        Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    set mkI := Ideal.Quotient.mk I with hmkI
    -- Monic lifts of the prescribed factors and arbitrary lifts of a Bézout identity.
    obtain ⟨G, hGmap, -, hGmon⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic
        (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective g₀) hg₀
    obtain ⟨H, hHmap, -, hHmon⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic
        (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective h₀) hh₀
    obtain ⟨u₀, v₀, hbez⟩ := hcop
    obtain ⟨u, hu⟩ := Polynomial.map_surjective mkI Ideal.Quotient.mk_surjective u₀
    obtain ⟨v, hv⟩ := Polynomial.map_surjective mkI Ideal.Quotient.mk_surjective v₀
    -- The two finite errors whose coefficients generate the nilpotent subideal.
    set δ : R[X] := f - G * H with hδ_def
    set w : R[X] := u * G + v * H - 1 with hw_def
    have hδmapI : δ.map mkI = 0 := by
      rw [hδ_def, Polynomial.map_sub, hfact, Polynomial.map_mul, hGmap, hHmap, sub_self]
    have hwmapI : w.map mkI = 0 := by
      rw [hw_def, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_mul, hu, hv, hGmap, hHmap, Polynomial.map_one, hbez, sub_self]
    set K : Ideal R := Ideal.span ((δ.coeffs : Set R) ∪ (w.coeffs : Set R)) with hK_def
    have hK_le_I : K ≤ I := by
      rw [hK_def, Ideal.span_le]
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
        exact Polynomial.coeff_mem_ideal_of_map_quotient_eq_zero hδmapI n
      · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
        exact Polynomial.coeff_mem_ideal_of_map_quotient_eq_zero hwmapI n
    have hKfg : K.FG := by
      rw [hK_def]
      exact Submodule.fg_span (δ.coeffs.finite_toSet.union w.coeffs.finite_toSet)
    have hKnil : IsNilpotent K :=
      (Ideal.FG.isNilpotent_iff_le_nilradical hKfg).mpr (hK_le_I.trans hI)
    set mkK := Ideal.Quotient.mk K with hmkK
    -- The errors vanish modulo `K` by construction.
    have hδmapK : δ.map mkK = 0 := by
      ext n
      rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      by_cases hn : δ.coeff n = 0
      · rw [hn]
        exact K.zero_mem
      · rw [hK_def]
        exact Ideal.subset_span (Or.inl (Polynomial.coeff_mem_coeffs hn))
    have hwmapK : w.map mkK = 0 := by
      ext n
      rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      by_cases hn : w.coeff n = 0
      · rw [hn]
        exact K.zero_mem
      · rw [hK_def]
        exact Ideal.subset_span (Or.inr (Polynomial.coeff_mem_coeffs hn))
    have hfactK : f.map mkK = G.map mkK * H.map mkK := by
      have := hδmapK
      rwa [hδ_def, Polynomial.map_sub, Polynomial.map_mul, sub_eq_zero] at this
    have hcopK : IsCoprime (G.map mkK) (H.map mkK) := by
      refine ⟨u.map mkK, v.map mkK, ?_⟩
      have := hwmapK
      rwa [hw_def, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_mul, Polynomial.map_one, sub_eq_zero] at this
    obtain ⟨g, h, hgmon, hhmon, hfgh, hgK, hhK⟩ :=
      (of_isNilpotent hKnil).exists_lift_factorization f hf (hGmon.map _) (hHmon.map _)
        hcopK hfactK
    -- Descend the congruences from `K` to the original ideal `I`.
    set qKI : R ⧸ K →+* R ⧸ I :=
      Ideal.quotientMap I (RingHom.id R) (by simpa using hK_le_I) with hqKI
    have hcompKI : qKI.comp mkK = mkI := by
      ext r
      simp [qKI, mkK, mkI]
    refine ⟨g, h, hgmon, hhmon, hfgh, ?_, ?_⟩
    · calc
        g.map mkI = (g.map mkK).map qKI := by rw [Polynomial.map_map, hcompKI]
        _ = (G.map mkK).map qKI := by rw [hgK]
        _ = G.map mkI := by rw [Polynomial.map_map, hcompKI]
        _ = g₀ := hGmap
    · calc
        h.map mkI = (h.map mkK).map qKI := by rw [Polynomial.map_map, hcompKI]
        _ = (H.map mkK).map qKI := by rw [hhK]
        _ = H.map mkI := by rw [Polynomial.map_map, hcompKI]
        _ = h₀ := hHmap

/-- **Uniqueness of a Henselian (coprime, monic) factorisation lift over a nilpotent
ideal.**  If `I` is nilpotent and `g * h = g' * h'` with `g, g'` monic having the same
reduction modulo `I` (and likewise `h, h'`), where the reductions of `g` and `h` are coprime,
then `g = g'` and `h = h'`.

The reductions being coprime lifts (along the nilpotent `I`) to the two mixed coprimality
statements `IsCoprime g h'` and `IsCoprime g' h`; mutual divisibility of the monic `g, g'`
then forces `g = g'`, and monic cancellation gives `h = h'`.  This is the coherence needed
to assemble factorisations through the tower `R ⧸ Iⁿ` in the complete case
(Stacks Tag 0ALJ). -/
theorem factorization_unique {I : Ideal R} (hI : IsNilpotent I)
    {g h g' h' : R[X]} (hgmon : g.Monic) (hg'mon : g'.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)))
    (hg' : g.map (Ideal.Quotient.mk I) = g'.map (Ideal.Quotient.mk I))
    (hhh' : h.map (Ideal.Quotient.mk I) = h'.map (Ideal.Quotient.mk I))
    (hgh : g * h = g' * h') : g = g' ∧ h = h' := by
  -- Coprimality of the reductions lifts to coprimality over `R` (nilpotent ideal).
  have hcop_gh' : IsCoprime g h' :=
    isCoprime_of_isNilpotent_of_map hI (by rw [← hhh']; exact hcop)
  have hcop_g'h : IsCoprime g' h :=
    isCoprime_of_isNilpotent_of_map hI
      (show IsCoprime (g'.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)) by
        rw [← hg']; exact hcop)
  -- `g ∣ g'` and `g' ∣ g`, hence (both monic) `g = g'`.
  have hdvd1 : g ∣ g' := hcop_gh'.dvd_of_dvd_mul_right ⟨h, hgh.symm⟩
  have hdvd2 : g' ∣ g := hcop_g'h.dvd_of_dvd_mul_right ⟨h', hgh⟩
  obtain ⟨c, hc⟩ := hdvd1
  obtain ⟨d, hd⟩ := hdvd2
  have cmon : c.Monic := hgmon.of_mul_monic_left (hc ▸ hg'mon)
  have hg_cd : g * (c * d) = g := by rw [← mul_assoc, ← hc, ← hd]
  have hcd1 : c * d = 1 :=
    sub_eq_zero.mp (hgmon.mul_right_eq_zero_iff.mp (by rw [mul_sub, mul_one, hg_cd, sub_self]))
  have hcunit : IsUnit c := ⟨⟨c, d, hcd1, by rw [mul_comm]; exact hcd1⟩, rfl⟩
  have hgeq : g = g' := by
    rw [hc, cmon.eq_one_of_isUnit hcunit, mul_one]
  -- Monic cancellation of `g` gives `h = h'`.
  have hheq : h = h' :=
    sub_eq_zero.mp (hgmon.mul_right_eq_zero_iff.mp (by rw [mul_sub, hgh, hgeq, sub_self]))
  exact ⟨hgeq, hheq⟩

end IsHenselianPair

/-- **A local ring whose maximal ideal is nilpotent is a Henselian local ring.**
In particular every Artinian local ring is Henselian.  (Stacks Tag 0ALI for the maximal
ideal, combined with the local-ring bridge `IsHenselianPair.henselianLocalRing`.) -/
theorem HenselianLocalRing.of_isNilpotent_maximalIdeal [IsLocalRing R]
    (h : IsNilpotent (IsLocalRing.maximalIdeal R)) : HenselianLocalRing R :=
  (IsHenselianPair.of_isNilpotent h).henselianLocalRing
