/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
import FiniteFlatGroupSchemes.ConvolutionPower
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The Grothendieck power question at an arbitrary prime

This file develops the uniform construction suggested by the rank-four counterexample at
`p = 2`, which is formalized separately, via quadratic algebras, in
`FiniteFlatGroupSchemes.GrothendieckCounterexample`.  For a prime `p`, the base ring is

`R p = ℤ[a, b] / (a^(p+1), b^(2*p-1), a^p * b^(p-1) + p)`.

Writing `wᵢ = (p.choose i) / p`, the coordinate algebra is obtained by adjoining `V` and `U`
successively along the two monic degree-`p` equations

* `V^p - a^p * W_b(V) = 0`,
* `U^p - a * b^(p-1) * W_a(U) + b^p * W_b(V) = 0`,

where `W_c(T) = ∑ 0 ≤ i < p, wᵢ c^(i-1) T^i`; its `i = 0` term is zero because a prime is
at least two.  The nested `AdjoinRoot` presentation makes the power basis and the rank `p^2`
formal consequences of Mathlib's monic-polynomial API.

## Main definitions

* `Counterexample.GrothendieckPowerAllPrimes.R`: the Artinian base ring displayed above.
* `Counterexample.GrothendieckPowerAllPrimes.A`: the coordinate algebra, finite free of rank
  `p^2` over `R p`.
* `Counterexample.GrothendieckPowerAllPrimes.HopfPackage`: the explicit data of a
  Hopf-algebra structure on `A p` with the expected skew-primitive coproduct.
* `Counterexample.GrothendieckPowerAllPrimes.HopfPackage.PowerCertificate`: the two
  geometric-sum identities at `p^2` predicted by the rank-four calculation.

## Main results

* `Counterexample.GrothendieckPowerAllPrimes.finrank_A`: `A p` is free of rank `p^2` over
  `R p`.
* `Counterexample.GrothendieckPowerAllPrimes.carry_ne_zero`: the carry term
  `p * b^(p-1) * U * V^(p-1)` is nonzero in `A p`.
* `Counterexample.GrothendieckPowerAllPrimes.HopfPackage.counterexample`: given a
  `HopfPackage` and its `PowerCertificate`, the coordinate algebra `A p` is finite free of
  rank `p^2` and its `p^2`-th power map is not the convolution unit.

## Implementation notes

At `p = 2`, the complete Hopf-algebra construction is proved by explicit polynomial
normalization in `FiniteFlatGroupSchemes.GrothendieckCounterexample`.  At odd primes, the
corresponding closure calculation uses the divided bridge/truncated-log lemma from the
accompanying mathematical note.  The present file formalizes the uniform base, the defining
equations, finite freeness, and the power-map formulas (through the general convolution-power
API of `FiniteFlatGroupSchemes.ConvolutionPower`), without using `sorry` or adding an axiom.
The remaining closure theorem is stated as the input structure `HopfPackage`; once a term of
it is supplied, the final non-annihilation theorem is fully formal.  This keeps the exact
proof boundary visible to Lean.

Nontriviality of `p * b^(p-1)` in the base ring is certified by an explicit linear functional
(`topCoefficientDetector`) with values in `ZMod (p^2)`, which annihilates every generator of
the base ideal; no Gröbner-basis computation is involved.

The construction of this group scheme as well as its formalization were carried out by the
AI assistants Codex (OpenAI) and Claude (Anthropic).

## References

* [F. Oort, J. Tate, *Group schemes of prime order*][oorttate1970]: Deligne's proof that a
  commutative finite locally free group scheme is killed by its order is reproduced in §1,
  and the question for possibly non-commutative group schemes is raised on p. 5.
* [J. Tate, *Finite flat group schemes*][tate1997]: records the question as open in §3.8.

## Tags

group scheme, Hopf algebra, counterexample
-/

namespace Counterexample.GrothendieckPowerAllPrimes

noncomputable section

open Polynomial

open scoped TensorProduct

/-!
## Divided binomial coefficients and the polynomial `W`
-/

/-- The integral divided binomial coefficient `wᵢ = (p.choose i) / p`. -/
def dividedChoose (p i : ℕ) : ℕ := p.choose i / p

theorem prime_mul_dividedChoose {p i : ℕ} (hp : p.Prime) (hi0 : i ≠ 0) (hip : i < p) :
    p * dividedChoose p i = p.choose i := by
  rw [dividedChoose, Nat.mul_div_cancel' (hp.dvd_choose_self hi0 hip)]

/-- The polynomial `W_c(T)`, written as a sum indexed by `Fin p` so its degree bound is
definitionally visible to `Polynomial.degree_sum_fin_lt`. -/
def WPolynomial {S : Type*} [CommRing S] (p : ℕ) (c : S) : S[X] :=
  ∑ i : Fin p, C ((dividedChoose p i : ℕ) * c ^ (i.1 - 1)) *
    X ^ i.1

/-- Evaluation of `W_c(T)`. -/
def W {S : Type*} [CommRing S] (p : ℕ) (c t : S) : S :=
  ∑ i : Fin p, (dividedChoose p i : ℕ) * c ^ (i.1 - 1) * t ^ i.1

@[simp] theorem map_W {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (p : ℕ) (c t : S) :
    f (W p c t) = W p (f c) (f t) := by
  simp [W, map_sum, map_mul, map_pow]

@[simp] theorem eval₂_WPolynomial {S T : Type*} [CommRing S] [CommRing T]
    (p : ℕ) (c : S) (f : S →+* T) (t : T) :
    (WPolynomial p c).eval₂ f t = W p (f c) t := by
  simp only [WPolynomial, W, eval₂_finsetSum, eval₂_mul,
    eval₂_pow, eval₂_C, eval₂_X, eval₂_natCast,
    map_mul, map_pow, map_natCast]

/-- A monic degree-`p` polynomial with prescribed coefficients below degree `p`. -/
def monicPolynomial {S : Type*} [CommRing S] (p : ℕ) (coeff : Fin p → S) : S[X] :=
  X ^ p + ∑ i : Fin p, C (coeff i) * X ^ i.1

theorem monicPolynomial_isMonicOfDegree {S : Type*} [CommRing S] [Nontrivial S]
    {p : ℕ} (hp : 0 < p) (coeff : Fin p → S) :
    IsMonicOfDegree (monicPolynomial p coeff) p := by
  apply (isMonicOfDegree_X_pow S p).add_right
  let q : S[X] := ∑ i : Fin p, C (coeff i) * X ^ i.1
  change q.natDegree < p
  by_cases hq : q = 0
  · simp [hq, hp]
  · exact (natDegree_lt_iff_degree_lt hq).2 (degree_sum_fin_lt coeff)

theorem monicPolynomial_monic {S : Type*} [CommRing S] [Nontrivial S]
    {p : ℕ} (hp : 0 < p) (coeff : Fin p → S) :
    (monicPolynomial p coeff).Monic :=
  (monicPolynomial_isMonicOfDegree hp coeff).monic

theorem monicPolynomial_natDegree {S : Type*} [CommRing S] [Nontrivial S]
    {p : ℕ} (hp : 0 < p) (coeff : Fin p → S) :
    (monicPolynomial p coeff).natDegree = p :=
  (monicPolynomial_isMonicOfDegree hp coeff).natDegree_eq

section Prime

variable (p : ℕ) [Fact p.Prime]

private theorem p_pos : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
private theorem p_ne_zero : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : p.Prime)
private theorem p_pred_succ : p - 1 + 1 = p :=
  Nat.sub_one_add_one (Nat.Prime.ne_zero (Fact.out : p.Prime))

/-- The polynomial ring `ℤ[a,b]`. -/
abbrev P := MvPolynomial (Fin 2) ℤ

/-- The variable `a` in `P`. -/
def ap : P := MvPolynomial.X 0

/-- The variable `b` in `P`. -/
def bp : P := MvPolynomial.X 1

/-! ## A coefficient detector for the top class in the base -/

/-- The bidegree `(i,j)` in the two-variable polynomial ring. -/
def bidegree (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

@[simp] private theorem bidegree_apply_zero (i j : ℕ) : bidegree i j 0 = i := by
  simp [bidegree]

@[simp] private theorem bidegree_apply_one (i j : ℕ) : bidegree i j 1 = j := by
  simp [bidegree]

private theorem bidegree_le_iff {i j k l : ℕ} :
    bidegree i j ≤ bidegree k l ↔ i ≤ k ∧ j ≤ l := by
  rw [Finsupp.le_iff]
  constructor
  · intro h
    constructor
    · by_cases hi0 : i = 0
      · simp [hi0]
      · simpa using h 0 (by simp [bidegree, hi0])
    · by_cases hj0 : j = 0
      · simp [hj0]
      · simpa using h 1 (by simp [bidegree, hj0])
  · rintro ⟨hi, hj⟩ x hx
    fin_cases x <;> simp [hi, hj]

private theorem bidegree_sub (i j k l : ℕ) :
    bidegree i j - bidegree k l = bidegree (i - k) (j - l) := by
  ext x
  fin_cases x <;> simp

private theorem monomial_bidegree (i j : ℕ) :
    MvPolynomial.monomial (bidegree i j) (1 : ℤ) = ap ^ i * bp ^ j := by
  simp [bidegree, ap, bp, MvPolynomial.monomial_eq]

/-- The ideal `(a^(p+1), b^(2*p-1), a^p*b^(p-1)+p)`. -/
def baseIdeal : Ideal P :=
  Ideal.span ({ap ^ (p + 1), bp ^ (2 * p - 1),
    ap ^ p * bp ^ (p - 1) + MvPolynomial.C (p : ℤ)} : Set P)

/-- The Artinian base ring of the construction. -/
abbrev R := P ⧸ baseIdeal p

/-- The class of `a` in `R`. -/
def a : R p := Ideal.Quotient.mk (baseIdeal p) ap

/-- The class of `b` in `R`. -/
def b : R p := Ideal.Quotient.mk (baseIdeal p) bp

omit [Fact p.Prime] in
@[simp] theorem a_pow_succ_eq_zero : a p ^ (p + 1) = 0 := by
  rw [show a p ^ (p + 1) = Ideal.Quotient.mk (baseIdeal p) (ap ^ (p + 1)) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

omit [Fact p.Prime] in
@[simp] theorem b_pow_two_mul_sub_one_eq_zero : b p ^ (2 * p - 1) = 0 := by
  rw [show b p ^ (2 * p - 1) =
      Ideal.Quotient.mk (baseIdeal p) (bp ^ (2 * p - 1)) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

omit [Fact p.Prime] in
@[simp] theorem base_relation :
    a p ^ p * b p ^ (p - 1) + (p : R p) = 0 := by
  rw [show a p ^ p * b p ^ (p - 1) + (p : R p) =
      Ideal.Quotient.mk (baseIdeal p)
        (ap ^ p * bp ^ (p - 1) + MvPolynomial.C (p : ℤ)) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- Evaluation at `a=b=0` in `ZMod p`; it proves that the base ideal is proper. -/
def evalResidue : P →+* ZMod p :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) ![0, 0]

theorem baseIdeal_le_ker_evalResidue :
    baseIdeal p ≤ RingHom.ker (evalResidue p) := by
  apply Ideal.span_le.2
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · apply (RingHom.mem_ker).2
    simp [evalResidue, ap]
  · apply (RingHom.mem_ker).2
    have htwo : 0 < 2 * p - 1 := by
      have := p_pos p
      omega
    simp [evalResidue, bp, htwo.ne']
  · apply (RingHom.mem_ker).2
    simp [evalResidue, ap, bp, p_ne_zero p]

noncomputable instance instNontrivialR : Nontrivial (R p) := by
  letI : NeZero p := ⟨p_ne_zero p⟩
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top (evalResidue p))
    (baseIdeal_le_ker_evalResidue p)

omit [Fact p.Prime] in
theorem p_mul_a_eq_zero : (p : R p) * a p = 0 := by
  have h := congr_arg (fun x : R p ↦ x * a p) (base_relation p)
  have hfirst : a p ^ p * b p ^ (p - 1) * a p = 0 := by
    calc
      a p ^ p * b p ^ (p - 1) * a p = a p ^ (p + 1) * b p ^ (p - 1) := by
        rw [mul_assoc, mul_comm (b p ^ (p - 1)) (a p), ← mul_assoc, ← pow_succ]
      _ = 0 := by rw [a_pow_succ_eq_zero, zero_mul]
  rw [add_mul, hfirst, zero_add, zero_mul] at h
  exact h

theorem p_mul_a_pow_eq_zero : (p : R p) * a p ^ p = 0 := by
  calc
    (p : R p) * a p ^ p = (p : R p) * (a p * a p ^ (p - 1)) := by
      rw [← pow_succ', p_pred_succ p]
    _ = ((p : R p) * a p) * a p ^ (p - 1) := by rw [mul_assoc]
    _ = 0 := by rw [p_mul_a_eq_zero, zero_mul]

theorem p_sq_eq_zero : ((p : R p) ^ 2) = 0 := by
  have h := congr_arg (fun x : R p ↦ (p : R p) * x) (base_relation p)
  have hfirst : (p : R p) * (a p ^ p * b p ^ (p - 1)) = 0 := by
    rw [← mul_assoc, p_mul_a_pow_eq_zero, zero_mul]
  rw [mul_add, hfirst, zero_add, mul_zero] at h
  simpa [pow_two] using h

omit [Fact p.Prime] in
theorem p_mul_b_pow_eq_zero : (p : R p) * b p ^ p = 0 := by
  have h := congr_arg (fun x : R p ↦ x * b p ^ p) (base_relation p)
  have hexp : p - 1 + p = 2 * p - 1 := by omega
  have hfirst : a p ^ p * b p ^ (p - 1) * b p ^ p = 0 := by
    rw [mul_assoc, ← pow_add, hexp, b_pow_two_mul_sub_one_eq_zero, mul_zero]
  rw [add_mul, hfirst, zero_add, zero_mul] at h
  exact h

/-! Although `p * b^p = 0`, the preceding power of `b` is nonzero after multiplication by
`p`.  We prove this without appealing to a normal-form tactic.  The detector below compares the
coefficients of `b^(p-1)` and `a^p b^(2p-2)` modulo `p^2`; this is exactly the linear functional
adapted to the inhomogeneous relation `a^p b^(p-1) + p`. -/

/-- The top-coefficient detector
`[b^(p-1)]q - p [a^p b^(2p-2)]q`, with values in `ZMod (p^2)`. -/
def topCoefficientDetector (q : P) : ZMod (p ^ 2) :=
  ((MvPolynomial.coeff (bidegree 0 (p - 1)) q : ℤ) : ZMod (p ^ 2)) -
    (p : ZMod (p ^ 2)) *
      ((MvPolynomial.coeff (bidegree p (2 * p - 2)) q : ℤ) : ZMod (p ^ 2))

omit [Fact p.Prime] in
private theorem topCoefficientDetector_add (q r : P) :
    topCoefficientDetector p (q + r) =
      topCoefficientDetector p q + topCoefficientDetector p r := by
  simp [topCoefficientDetector]
  ring

omit [Fact p.Prime] in
private theorem topCoefficientDetector_mul_a_generator (q : P) :
    topCoefficientDetector p (q * ap ^ (p + 1)) = 0 := by
  have hlow : ¬ bidegree (p + 1) 0 ≤ bidegree 0 (p - 1) := by
    rw [bidegree_le_iff]
    omega
  have htop : ¬ bidegree (p + 1) 0 ≤ bidegree p (2 * p - 2) := by
    rw [bidegree_le_iff]
    omega
  rw [← show MvPolynomial.monomial (bidegree (p + 1) 0) (1 : ℤ) =
      ap ^ (p + 1) by simpa using monomial_bidegree (p + 1) 0]
  simp [topCoefficientDetector, MvPolynomial.coeff_mul_monomial', hlow, htop]

private theorem topCoefficientDetector_mul_b_generator (q : P) :
    topCoefficientDetector p (q * bp ^ (2 * p - 1)) = 0 := by
  have hp : 0 < p := p_pos p
  have hlow : ¬ bidegree 0 (2 * p - 1) ≤ bidegree 0 (p - 1) := by
    rw [bidegree_le_iff]
    omega
  have htop : ¬ bidegree 0 (2 * p - 1) ≤ bidegree p (2 * p - 2) := by
    rw [bidegree_le_iff]
    omega
  rw [← show MvPolynomial.monomial (bidegree 0 (2 * p - 1)) (1 : ℤ) =
      bp ^ (2 * p - 1) by simpa using monomial_bidegree 0 (2 * p - 1)]
  simp [topCoefficientDetector, MvPolynomial.coeff_mul_monomial', hlow, htop]

private theorem topCoefficientDetector_mul_relation_generator (q : P) :
    topCoefficientDetector p
      (q * (ap ^ p * bp ^ (p - 1) + MvPolynomial.C (p : ℤ))) = 0 := by
  have hp : 0 < p := p_pos p
  have hnot : ¬ bidegree p (p - 1) ≤ bidegree 0 (p - 1) := by
    rw [bidegree_le_iff]
    omega
  have hle : bidegree p (p - 1) ≤ bidegree p (2 * p - 2) := by
    rw [bidegree_le_iff]
    omega
  have hsub : bidegree p (2 * p - 2) - bidegree p (p - 1) =
      bidegree 0 (p - 1) := by
    rw [bidegree_sub, Nat.sub_self]
    congr 1
    omega
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [← monomial_bidegree p (p - 1)]
  simp only [mul_add, topCoefficientDetector, MvPolynomial.coeff_add, Int.cast_add,
    MvPolynomial.coeff_mul_monomial', hnot, if_false, Int.cast_zero,
    hle, if_true, hsub, mul_one,
    mul_comm q (MvPolynomial.C (p : ℤ)), MvPolynomial.coeff_C_mul, Int.cast_mul,
    Int.cast_natCast]
  ring_nf
  rw [hp2]
  ring

private theorem topCoefficientDetector_eq_zero_of_mem_baseIdeal
    {q : P} (hq : q ∈ baseIdeal p) : topCoefficientDetector p q = 0 := by
  change q ∈ Ideal.span ({ap ^ (p + 1), bp ^ (2 * p - 1),
    ap ^ p * bp ^ (p - 1) + MvPolynomial.C (p : ℤ)} : Set P) at hq
  rcases Ideal.mem_span_insert.mp hq with ⟨r₁, q₁, hq₁, rfl⟩
  rcases Ideal.mem_span_insert.mp hq₁ with ⟨r₂, q₂, hq₂, rfl⟩
  rcases Ideal.mem_span_singleton'.mp hq₂ with ⟨r₃, hr₃⟩
  rw [← hr₃, topCoefficientDetector_add, topCoefficientDetector_add,
    topCoefficientDetector_mul_a_generator, topCoefficientDetector_mul_b_generator,
    topCoefficientDetector_mul_relation_generator]
  simp

private theorem topCoefficientDetector_top :
    topCoefficientDetector p (MvPolynomial.C (p : ℤ) * bp ^ (p - 1)) =
      (p : ZMod (p ^ 2)) := by
  have hp : 0 < p := p_pos p
  have hne : bidegree 0 (p - 1) ≠ bidegree p (2 * p - 2) := by
    intro h
    have h0 := DFunLike.congr_fun h 0
    simp at h0
    omega
  rw [← show MvPolynomial.monomial (bidegree 0 (p - 1)) (p : ℤ) =
      MvPolynomial.C (p : ℤ) * bp ^ (p - 1) by
    simp [bidegree, bp, MvPolynomial.monomial_eq]]
  simp [topCoefficientDetector, MvPolynomial.coeff_monomial, hne]

/-- The coefficient `p * b^(p-1)` is nonzero in the Artinian base.  Equivalently, by the base
relation it is the nonzero top monomial `-a^p b^(2p-2)`. -/
theorem p_mul_b_pow_sub_one_ne_zero : (p : R p) * b p ^ (p - 1) ≠ 0 := by
  intro hzero
  have hmem : MvPolynomial.C (p : ℤ) * bp ^ (p - 1) ∈ baseIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [b] using hzero
  have hdet := topCoefficientDetector_eq_zero_of_mem_baseIdeal p hmem
  rw [topCoefficientDetector_top] at hdet
  have hp' : (p : ZMod (p ^ 2)) ≠ 0 := by
    have hlt : p < p ^ 2 := by
      rw [pow_two]
      exact (lt_mul_iff_one_lt_left (p_pos p)).mpr (Fact.out : p.Prime).one_lt
    rw [← ZMod.val_ne_zero]
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, (p_pos p).ne']
  exact hp' hdet

/-- In a monic `AdjoinRoot`, a nonzero scalar times one of the canonical power-basis vectors is
nonzero.  This form does not require the coefficient ring to be a domain. -/
theorem algebraMap_mul_root_pow_ne_zero
    {S : Type*} [CommRing S] [Nontrivial S] (f : S[X]) (hf : f.Monic)
    (c : S) (hc : c ≠ 0) (i : ℕ) (hi : i < f.natDegree) :
    algebraMap S (AdjoinRoot f) c * AdjoinRoot.root f ^ i ≠ 0 := by
  intro hzero
  let j : Fin f.natDegree := ⟨i, hi⟩
  have hzero' : c • (AdjoinRoot.powerBasis' hf).basis j = 0 := by
    rw [(AdjoinRoot.powerBasis' hf).basis_eq_pow,
      show (j : ℕ) = i by rfl, Algebra.smul_def]
    exact hzero
  apply hc
  calc
    c = (AdjoinRoot.powerBasis' hf).basis.repr
        (c • (AdjoinRoot.powerBasis' hf).basis j) j := by
      simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    _ = (AdjoinRoot.powerBasis' hf).basis.repr 0 j := by rw [hzero']
    _ = 0 := by simp only [map_zero, Finsupp.zero_apply]

/-! ## The two nested monic extensions -/

/-- Coefficients below degree `p` in the equation for `V`. -/
def gCoeff (i : Fin p) : R p :=
  -(a p ^ p) * (dividedChoose p i : ℕ) * b p ^ (i.1 - 1)

/-- The monic polynomial `G(T) = T^p - a^p W_b(T)`. -/
def gPolynomial : (R p)[X] :=
  monicPolynomial p (gCoeff p)

theorem gPolynomial_isMonicOfDegree :
    IsMonicOfDegree (gPolynomial p) p :=
  monicPolynomial_isMonicOfDegree (p_pos p) (gCoeff p)

theorem gPolynomial_monic : (gPolynomial p).Monic :=
  (gPolynomial_isMonicOfDegree p).monic

theorem gPolynomial_natDegree : (gPolynomial p).natDegree = p :=
  (gPolynomial_isMonicOfDegree p).natDegree_eq

/-- The intermediate algebra `B = R[V]/(G)`. -/
abbrev B := AdjoinRoot (gPolynomial p)

/-- The coordinate `V` in the intermediate algebra. -/
def V : B p := AdjoinRoot.root (gPolynomial p)

noncomputable instance instNontrivialB : Nontrivial (B p) := by
  have hne : AdjoinRoot.mk (gPolynomial p) (1 : (R p)[X]) ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt (gPolynomial_monic p) one_ne_zero (by
      rw [gPolynomial_natDegree p]
      simpa using p_pos p)
  exact ⟨⟨1, 0, by simpa using hne⟩⟩

noncomputable instance instFreeRB : Module.Free (R p) (B p) :=
  (gPolynomial_monic p).free_adjoinRoot

noncomputable instance instFiniteRB : Module.Finite (R p) (B p) :=
  (gPolynomial_monic p).finite_adjoinRoot

theorem finrank_B : Module.finrank (R p) (B p) = p := by
  calc
    Module.finrank (R p) (B p) = (gPolynomial p).natDegree :=
      (AdjoinRoot.powerBasis' (gPolynomial_monic p)).finrank
    _ = p := gPolynomial_natDegree p

/-- The image of `a` in the intermediate algebra `B`. -/
abbrev aB : B p := algebraMap (R p) (B p) (a p)

/-- The image of `b` in the intermediate algebra `B`. -/
abbrev bB : B p := algebraMap (R p) (B p) (b p)

omit [Fact p.Prime] in
theorem V_relation :
    V p ^ p = aB p ^ p * W p (bB p) (V p) := by
  have h := AdjoinRoot.eval₂_root (gPolynomial p)
  change (gPolynomial p).eval₂ (algebraMap (R p) (B p)) (V p) = 0 at h
  simp only [gPolynomial, monicPolynomial, eval₂_add, eval₂_pow,
    eval₂_X, eval₂_finsetSum, eval₂_mul,
    eval₂_C] at h
  rw [eq_neg_of_add_eq_zero_left h]
  simp only [AdjoinRoot.algebraMap_eq, gCoeff, map_mul, map_neg, map_pow, map_natCast,
    neg_mul, Finset.sum_neg_distrib, neg_neg, W, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change aB p ^ p * (dividedChoose p i : ℕ) * bB p ^ (i.1 - 1) * V p ^ i.1 = _
  ring

/-- Coefficients below degree `p` in the `U`-polynomial before adding its `V`-dependent
constant term. -/
def fCoeff (i : Fin p) : B p :=
  -(aB p * bB p ^ (p - 1)) * (dividedChoose p i : ℕ) * aB p ^ (i.1 - 1)

/-- The bridge term `b^p W_b(V)` in the equation for `U`. -/
def bridge : B p := bB p ^ p * W p (bB p) (V p)

/-- The monic polynomial
`F(T) = T^p - a*b^(p-1) W_a(T) + b^p W_b(V)` over `B`. -/
def fPolynomial : (B p)[X] :=
  monicPolynomial p (fCoeff p) + C (bridge p)

private theorem degree_C_lt_p {S : Type*} [CommRing S] (x : S) :
    (C x).degree < (p : WithBot ℕ) :=
  degree_C_lt.trans_le (WithBot.coe_le_coe.mpr (p_pos p))

theorem fPolynomial_monic : (fPolynomial p).Monic := by
  let hmonic := monicPolynomial_monic (S := B p) (p_pos p) (fCoeff p)
  apply hmonic.add_of_left
  rw [degree_eq_natDegree hmonic.ne_zero,
    monicPolynomial_natDegree (p_pos p) (fCoeff p)]
  exact degree_C_lt_p p (bridge p)

theorem fPolynomial_natDegree : (fPolynomial p).natDegree = p := by
  let hmonic := monicPolynomial_monic (S := B p) (p_pos p) (fCoeff p)
  have hdeg : (C (bridge p)).degree <
      (monicPolynomial p (fCoeff p)).degree := by
    rw [degree_eq_natDegree hmonic.ne_zero,
      monicPolynomial_natDegree (p_pos p) (fCoeff p)]
    exact degree_C_lt_p p (bridge p)
  rw [fPolynomial, natDegree_add_eq_left_of_degree_lt hdeg,
    monicPolynomial_natDegree (p_pos p) (fCoeff p)]

/-- The coordinate algebra `A`, obtained by adjoining `U` to `B`. -/
abbrev A := AdjoinRoot (fPolynomial p)

/-- The coordinate `U` in `A`. -/
def U : A p := AdjoinRoot.root (fPolynomial p)

/-- The image of `V` in `A`. -/
def VA : A p := algebraMap (B p) (A p) (V p)

noncomputable instance instNontrivialA : Nontrivial (A p) := by
  have hne : AdjoinRoot.mk (fPolynomial p) (1 : (B p)[X]) ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt (fPolynomial_monic p) one_ne_zero (by
      rw [fPolynomial_natDegree p]
      simpa using p_pos p)
  exact ⟨⟨1, 0, by simpa using hne⟩⟩

noncomputable instance instFreeBA : Module.Free (B p) (A p) :=
  (fPolynomial_monic p).free_adjoinRoot

noncomputable instance instFiniteBA : Module.Finite (B p) (A p) :=
  (fPolynomial_monic p).finite_adjoinRoot

noncomputable instance instFreeRA : Module.Free (R p) (A p) :=
  Module.Free.trans (R := R p) (S := B p) (M := A p)

noncomputable instance instFiniteRA : Module.Finite (R p) (A p) :=
  Module.Finite.trans (R := R p) (A := B p) (M := A p)

theorem finrank_A_over_B : Module.finrank (B p) (A p) = p := by
  calc
    Module.finrank (B p) (A p) = (fPolynomial p).natDegree :=
      (AdjoinRoot.powerBasis' (fPolynomial_monic p)).finrank
    _ = p := fPolynomial_natDegree p

theorem finrank_A : Module.finrank (R p) (A p) = p ^ 2 := by
  calc
    Module.finrank (R p) (A p) =
        Module.finrank (R p) (B p) * Module.finrank (B p) (A p) :=
      (Module.finrank_mul_finrank (R p) (B p) (A p)).symm
    _ = p ^ 2 := by rw [finrank_B p, finrank_A_over_B p, pow_two]

omit [Fact p.Prime] in
theorem U_relation :
    U p ^ p = algebraMap (B p) (A p) (aB p * bB p ^ (p - 1)) * W p
        (algebraMap (B p) (A p) (aB p)) (U p) -
      algebraMap (B p) (A p) (bridge p) := by
  have h := AdjoinRoot.eval₂_root (fPolynomial p)
  change (fPolynomial p).eval₂ (algebraMap (B p) (A p)) (U p) = 0 at h
  simp only [fPolynomial, monicPolynomial, eval₂_add, eval₂_pow,
    eval₂_X, eval₂_finsetSum, eval₂_mul,
    eval₂_C] at h
  have hsum :
      (∑ i : Fin p, algebraMap (B p) (A p) (fCoeff p i) * U p ^ i.1) =
        -algebraMap (B p) (A p) (aB p * bB p ^ (p - 1)) *
          W p (algebraMap (B p) (A p) (aB p)) (U p) := by
    simp only [AdjoinRoot.algebraMap_eq, fCoeff, neg_mul, map_neg, map_mul, map_pow,
      map_natCast, Finset.sum_neg_distrib, W, Finset.mul_sum, neg_inj]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at h
  linear_combination h

omit [Fact p.Prime] in
theorem VA_relation :
    VA p ^ p = algebraMap (R p) (A p) (a p ^ p) * W p
      (algebraMap (R p) (A p) (b p)) (VA p) := by
  change (algebraMap (B p) (A p) (V p)) ^ p = _
  rw [← map_pow, V_relation p, map_mul]
  rw [map_W]
  simp only [VA, aB, bB, map_pow,
    IsScalarTower.algebraMap_apply (R p) (B p) (A p)]

/-! The preceding theorem is the formal finite-freeness core: `A p` has the iterated power
basis `U^i V^j`, indexed by `Fin p × Fin p`, and `finrank_A` records its cardinality as `p^2`.

## The Hopf-algebra proof boundary

The following definitions package the expected character and coproduct in Mathlib's bialgebra
language.  The structure is explicit data rather than an axiom: a term of `HopfPackage p` must
give the coproduct, counit, antipode, and proofs of every displayed identity.  Mathlib
`Bialgebra` and `HopfAlgebra` instances are then constructed from those fields.  The odd-prime
divided bridge lemma is precisely what remains necessary to construct such a term for `A p`.
-/

/-- The image of `a` in the coordinate algebra `A`. -/
abbrev aA : A p := algebraMap (R p) (A p) (a p)

/-- The image of `b` in the coordinate algebra `A`. -/
abbrev bA : A p := algebraMap (R p) (A p) (b p)

/-- The carry term witnessing that the `p^2`-th power map differs from the convolution unit
is nonzero.  The proof uses the detector theorem in `R`, followed successively by the `V`-
and `U`-power bases. -/
theorem carry_ne_zero :
    (p : A p) * bA p ^ (p - 1) * U p * VA p ^ (p - 1) ≠ 0 := by
  have hpred : p - 1 < (gPolynomial p).natDegree := by
    rw [gPolynomial_natDegree]
    exact Nat.sub_one_lt (p_ne_zero p)
  have hB : algebraMap (R p) (B p) ((p : R p) * b p ^ (p - 1)) *
      V p ^ (p - 1) ≠ 0 :=
    algebraMap_mul_root_pow_ne_zero (gPolynomial p) (gPolynomial_monic p)
      ((p : R p) * b p ^ (p - 1)) (p_mul_b_pow_sub_one_ne_zero p) (p - 1) hpred
  have hone : 1 < (fPolynomial p).natDegree := by
    rw [fPolynomial_natDegree]
    exact (Fact.out : p.Prime).one_lt
  have hA := algebraMap_mul_root_pow_ne_zero
    (fPolynomial p) (fPolynomial_monic p)
    (algebraMap (R p) (B p) ((p : R p) * b p ^ (p - 1)) * V p ^ (p - 1))
    hB 1 hone
  have heq :
      (p : A p) * bA p ^ (p - 1) * U p * VA p ^ (p - 1) =
        algebraMap (B p) (A p)
          (algebraMap (R p) (B p) ((p : R p) * b p ^ (p - 1)) * V p ^ (p - 1)) *
            U p ^ 1 := by
    simp only [map_mul, map_pow, pow_one, VA, bA,
      IsScalarTower.algebraMap_apply (R p) (B p) (A p)]
    rw [← IsScalarTower.algebraMap_apply (R p) (B p) (A p)]
    simp only [map_natCast]
    ring
  rw [heq]
  exact hA

/-- A completed Hopf-algebra closure certificate for the uniform equations.

The fields `lambda_spec` and `lambdaInv_spec` express that `lambda` is the ratio of the two
affine coordinates `1 + a * U` and `1 + b * V`, that is, `lambda = (1 + aU) * (1 + bV)⁻¹`
and `lambdaInv = (1 + bV) * (1 + aU)⁻¹`, without choosing a `Units` wrapper.  The fields
`comul_lambda` and `counit_lambda` say precisely that `lambda` is a group-like element
(`IsGroupLikeElem`) for the certified bialgebra structure, and similarly for `lambdaInv`. -/
structure HopfPackage where
  /-- The group-like unit controlling the semidirect-product law. -/
  lambda : A p
  /-- The inverse of the group-like unit `lambda`. -/
  lambdaInv : A p
  /-- `lambda` is the ratio of the affine coordinates `1 + aU` and `1 + bV`. -/
  lambda_spec : lambda * (1 + bA p * VA p) = 1 + aA p * U p
  /-- `lambdaInv` is the ratio of the affine coordinates `1 + bV` and `1 + aU`. -/
  lambdaInv_spec : lambdaInv * (1 + aA p * U p) = 1 + bA p * VA p
  /-- `lambda` and `lambdaInv` are mutually inverse. -/
  lambda_mul_lambdaInv : lambda * lambdaInv = 1
  /-- `lambda` and `lambdaInv` are mutually inverse. -/
  lambdaInv_mul_lambda : lambdaInv * lambda = 1
  /-- The coproduct algebra homomorphism. -/
  comul : A p →ₐ[R p] A p ⊗[R p] A p
  /-- The counit algebra homomorphism. -/
  counit : A p →ₐ[R p] R p
  /-- The coproduct is coassociative. -/
  comul_coassoc :
    (Algebra.TensorProduct.assoc (R p) (R p) (R p) (A p) (A p) (A p)).toAlgHom.comp
        ((Algebra.TensorProduct.map comul (.id (R p) (A p))).comp comul) =
      (Algebra.TensorProduct.map (.id (R p) (A p)) comul).comp comul
  /-- The counit axiom on the left tensor factor. -/
  counit_left :
    (Algebra.TensorProduct.map counit (.id (R p) (A p))).comp comul =
      (Algebra.TensorProduct.lid (R p) (A p)).symm
  /-- The counit axiom on the right tensor factor. -/
  counit_right :
    (Algebra.TensorProduct.map (.id (R p) (A p)) counit).comp comul =
      (Algebra.TensorProduct.rid (R p) (R p) (A p)).symm
  /-- `U` is skew-primitive: `Δ(U) = U ⊗ 1 + lambda ⊗ U`. -/
  comul_U : comul (U p) = U p ⊗ₜ[R p] 1 + lambda ⊗ₜ[R p] U p
  /-- `V` is skew-primitive: `Δ(V) = V ⊗ lambdaInv + 1 ⊗ V`. -/
  comul_VA : comul (VA p) = VA p ⊗ₜ[R p] lambdaInv + 1 ⊗ₜ[R p] VA p
  /-- `lambda` is group-like: `Δ(lambda) = lambda ⊗ lambda`. -/
  comul_lambda : comul lambda = lambda ⊗ₜ[R p] lambda
  /-- `lambdaInv` is group-like: `Δ(lambdaInv) = lambdaInv ⊗ lambdaInv`. -/
  comul_lambdaInv : comul lambdaInv = lambdaInv ⊗ₜ[R p] lambdaInv
  /-- The counit vanishes on `U`. -/
  counit_U : counit (U p) = 0
  /-- The counit vanishes on `V`. -/
  counit_VA : counit (VA p) = 0
  /-- The counit is `1` on the group-like element `lambda`. -/
  counit_lambda : counit lambda = 1
  /-- The counit is `1` on the group-like element `lambdaInv`. -/
  counit_lambdaInv : counit lambdaInv = 1
  /-- The antipode algebra homomorphism. -/
  antipode : A p →ₐ[R p] A p
  /-- The right antipode identity. -/
  antipode_right_identity :
    ((Algebra.TensorProduct.lift antipode (.id (R p) (A p)) fun _ ↦ Commute.all _).comp
      comul) = (Algebra.ofId (R p) (A p)).comp counit
  /-- The left antipode identity. -/
  antipode_left_identity :
    ((Algebra.TensorProduct.lift (.id (R p) (A p)) antipode fun _ _ ↦ Commute.all _ _).comp
      comul) = (Algebra.ofId (R p) (A p)).comp counit

/-- The bialgebra instance certified by a `HopfPackage`. -/
@[reducible] noncomputable def HopfPackage.toBialgebra
    (H : HopfPackage p) : Bialgebra (R p) (A p) :=
  Bialgebra.ofAlgHom H.comul H.counit H.comul_coassoc H.counit_left H.counit_right

/-- The Hopf-algebra instance certified by a `HopfPackage`. -/
@[reducible] noncomputable def HopfPackage.toHopfAlgebra
    (H : HopfPackage p) : HopfAlgebra (R p) (A p) :=
  letI := H.toBialgebra
  HopfAlgebra.ofAlgHom H.antipode H.antipode_right_identity H.antipode_left_identity

namespace HopfPackage

/-- The `n`-th convolution power of the identity of `A`, with respect to the bialgebra
structure certified by `H`: the coordinate-ring map of the pointwise `n`-th power map of the
group scheme. -/
noncomputable def powerMap (H : HopfPackage p) (n : ℕ) : A p →ₐ[R p] A p :=
  letI := H.toBialgebra
  AlgHom.convPowId (R p) (A p) n

omit [Fact p.Prime] in
/-- On the skew-primitive coordinate `U`, the `n`-th power map is the geometric sum
`(1 + lambda + ⋯ + lambdaⁿ⁻¹) * U`. -/
theorem powerMap_U (H : HopfPackage p) (n : ℕ) :
    powerMap p H n (U p) = (∑ i ∈ Finset.range n, H.lambda ^ i) * U p := by
  letI := H.toBialgebra
  exact AlgHom.convPowId_apply_of_comul_eq_tmul_one_add_tmul H.comul_U H.counit_U n

omit [Fact p.Prime] in
/-- On the skew-primitive coordinate `V`, the `n`-th power map is the geometric sum
`V * (1 + lambdaInv + ⋯ + lambdaInvⁿ⁻¹)`. -/
theorem powerMap_VA (H : HopfPackage p) (n : ℕ) :
    powerMap p H n (VA p) = VA p * ∑ i ∈ Finset.range n, H.lambdaInv ^ i := by
  letI := H.toBialgebra
  exact AlgHom.convPowId_apply_of_comul_eq_tmul_add_one_tmul H.comul_VA H.counit_VA n

/-- The arithmetic certificate needed after Hopf closure: the two geometric sums have the
predicted carry.  Its nonvanishing against `U` is already the unconditional theorem
`carry_ne_zero`. -/
structure PowerCertificate (H : HopfPackage p) : Prop where
  /-- The geometric sum of `lambda` of length `p^2` equals the carry term. -/
  geom_sum_lambda :
    ∑ i ∈ Finset.range (p ^ 2), H.lambda ^ i =
      (p : A p) * bA p ^ (p - 1) * VA p ^ (p - 1)
  /-- The geometric sum of `lambdaInv` of length `p^2` equals the carry term. -/
  geom_sum_lambdaInv :
    ∑ i ∈ Finset.range (p ^ 2), H.lambdaInv ^ i =
      (p : A p) * bA p ^ (p - 1) * VA p ^ (p - 1)

omit [Fact p.Prime] in
/-- Given the power certificate, the `p^2`-th power map sends `U` to the carry term. -/
theorem powerMap_p_squared_U (H : HopfPackage p) (hpow : PowerCertificate p H) :
    powerMap p H (p ^ 2) (U p) =
      (p : A p) * bA p ^ (p - 1) * U p * VA p ^ (p - 1) := by
  rw [powerMap_U p, hpow.geom_sum_lambda]
  ring

/-- Given the power certificate, the `p^2`-th power map does not vanish on `U`. -/
theorem powerMap_p_squared_U_ne_zero (H : HopfPackage p) (hpow : PowerCertificate p H) :
    powerMap p H (p ^ 2) (U p) ≠ 0 := by
  rw [powerMap_p_squared_U p H hpow]
  exact carry_ne_zero p

/-- The bundled commutative Hopf algebra, conditional only on the explicit closure package. -/
noncomputable def coordinateHopfAlgebra (H : HopfPackage p) : CommHopfAlgCat (R p) :=
  letI := H.toHopfAlgebra
  CommHopfAlgCat.of (R p) (A p)

/-- Once the divided bridge and carry certificates are supplied, the uniform construction is a
finite free Hopf algebra of rank `p^2`, over the nontrivial base ring `R p`, whose
`p^2`-th power map is not the convolution unit.

The freeness and finiteness conjuncts guarantee that the `Module.finrank` conjunct expresses
the honest rank of `A p` over `R p`. -/
theorem counterexample (H : HopfPackage p) (hpow : PowerCertificate p H) :
    Nontrivial (R p) ∧ Module.Free (R p) (A p) ∧ Module.Finite (R p) (A p) ∧
      Module.finrank (R p) (A p) = p ^ 2 ∧
      powerMap p H (p ^ 2) ≠
        (Algebra.ofId (R p) (A p)).comp H.counit := by
  refine ⟨inferInstance, inferInstance, inferInstance, finrank_A p, ?_⟩
  intro h
  apply powerMap_p_squared_U_ne_zero p H hpow
  have hU := DFunLike.congr_fun h (U p)
  simpa [H.counit_U] using hU

end HopfPackage

end Prime

end

end Counterexample.GrothendieckPowerAllPrimes
