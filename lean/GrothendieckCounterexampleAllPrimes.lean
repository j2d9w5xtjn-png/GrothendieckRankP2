/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-!
# The arbitrary-prime Grothendieck power counterexample

This file develops the uniform construction suggested by the rank-four example.  For a prime
`p`, the base is

`Rₚ = ℤ[a, b] / (a^(p+1), b^(2*p-1), a^p * b^(p-1) + p)`.

Writing `wᵢ = (p.choose i) / p`, the coordinate algebra is obtained by adjoining `V` and `U`
successively along the two monic degree-`p` equations

`V^p - a^p * W_b(V) = 0`,

`U^p - a * b^(p-1) * W_a(U) + b^p * W_b(V) = 0`.

Here `W_c(T) = ∑ 0 ≤ i < p, wᵢ c^(i-1) T^i`; its `i = 0` term is zero because a prime is
at least two.  The nested `AdjoinRoot` presentation makes the power basis and rank `p^2`
formal consequences of Mathlib's monic-polynomial API.

The p=2 file `GrothendieckCounterexample.lean` proves the complete Hopf-algebra construction by
explicit polynomial normalization.  At odd primes, the corresponding closure calculation uses
the divided bridge/truncated-log lemma from the accompanying mathematical note.  The present file
formalizes the uniform base, equations, finite freeness, and the reusable skew-primitive
power-map API without using `sorry` or adding an axiom.  The remaining closure theorem is stated
as the input structure `HopfPackage`; once supplied, the final non-annihilation theorem is fully
formal.  This keeps the exact proof boundary visible to Lean.
-/

namespace FiniteFlatGroupSchemes.GrothendieckCounterexampleAllPrimes

noncomputable section

open scoped BigOperators
open Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The integral divided binomial coefficient `wᵢ = (p.choose i) / p`. -/
def dividedChoose (p i : ℕ) : ℕ := p.choose i / p

theorem prime_mul_dividedChoose {p i : ℕ} (hp : p.Prime) (hi0 : i ≠ 0) (hip : i < p) :
    p * dividedChoose p i = p.choose i := by
  rw [dividedChoose, Nat.mul_div_cancel' (hp.dvd_choose_self hi0 hip)]

/-- The polynomial `W_c(T)`, written as a sum indexed by `Fin p` so its degree bound is
definitionally visible to `Polynomial.degree_sum_fin_lt`. -/
def WPolynomial {S : Type*} [CommRing S] (p : ℕ) (c : S) : S[X] :=
  ∑ i : Fin p, Polynomial.C ((dividedChoose p i : ℕ) * c ^ (i.1 - 1)) *
    Polynomial.X ^ i.1

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
  unfold WPolynomial W
  rw [show
    Polynomial.eval₂ f t
        (∑ i : Fin p, Polynomial.C ((dividedChoose p i : ℕ) * c ^ (i.1 - 1)) *
          Polynomial.X ^ i.1) =
      ∑ i : Fin p,
        Polynomial.eval₂ f t
          (Polynomial.C ((dividedChoose p i : ℕ) * c ^ (i.1 - 1)) *
            Polynomial.X ^ i.1) by
      exact map_sum (Polynomial.eval₂AddMonoidHom f t) _ _]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_natCast, map_mul, map_pow, map_natCast]

/-- A monic degree-`p` polynomial with prescribed coefficients below degree `p`. -/
def monicPolynomial {S : Type*} [CommRing S] (p : ℕ) (coeff : Fin p → S) : S[X] :=
  Polynomial.X ^ p + ∑ i : Fin p, Polynomial.C (coeff i) * Polynomial.X ^ i.1

theorem monicPolynomial_isMonicOfDegree {S : Type*} [CommRing S] [Nontrivial S]
    {p : ℕ} (hp : 0 < p) (coeff : Fin p → S) :
    IsMonicOfDegree (monicPolynomial p coeff) p := by
  apply (isMonicOfDegree_X_pow S p).add_right
  let q : S[X] := ∑ i : Fin p, Polynomial.C (coeff i) * Polynomial.X ^ i.1
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

@[simp] theorem a_pow_succ : a p ^ (p + 1) = 0 := by
  rw [show a p ^ (p + 1) = Ideal.Quotient.mk (baseIdeal p) (ap ^ (p + 1)) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

@[simp] theorem b_pow_two_mul_sub_one : b p ^ (2 * p - 1) = 0 := by
  rw [show b p ^ (2 * p - 1) =
      Ideal.Quotient.mk (baseIdeal p) (bp ^ (2 * p - 1)) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

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

theorem p_mul_a : (p : R p) * a p = 0 := by
  have h := congr_arg (fun x : R p ↦ x * a p) (base_relation p)
  have hfirst : a p ^ p * b p ^ (p - 1) * a p = 0 := by
    calc
      a p ^ p * b p ^ (p - 1) * a p = a p ^ (p + 1) * b p ^ (p - 1) := by
        rw [mul_assoc, mul_comm (b p ^ (p - 1)) (a p), ← mul_assoc, ← pow_succ]
      _ = 0 := by rw [a_pow_succ, zero_mul]
  rw [add_mul, hfirst, zero_add, zero_mul] at h
  exact h

theorem p_mul_a_pow : (p : R p) * a p ^ p = 0 := by
  calc
    (p : R p) * a p ^ p = (p : R p) * (a p * a p ^ (p - 1)) := by
      rw [← pow_succ', p_pred_succ p]
    _ = ((p : R p) * a p) * a p ^ (p - 1) := by rw [mul_assoc]
    _ = 0 := by rw [p_mul_a, zero_mul]

theorem p_squared_eq_zero : ((p : R p) ^ 2) = 0 := by
  have h := congr_arg (fun x : R p ↦ (p : R p) * x) (base_relation p)
  have hfirst : (p : R p) * (a p ^ p * b p ^ (p - 1)) = 0 := by
    rw [← mul_assoc, p_mul_a_pow, zero_mul]
  rw [mul_add, hfirst, zero_add, mul_zero] at h
  simpa [pow_two] using h

theorem p_mul_b_pow : (p : R p) * b p ^ p = 0 := by
  have h := congr_arg (fun x : R p ↦ x * b p ^ p) (base_relation p)
  have hexp : p - 1 + p = 2 * p - 1 := by omega
  have hfirst : a p ^ p * b p ^ (p - 1) * b p ^ p = 0 := by
    rw [mul_assoc, ← pow_add, hexp, b_pow_two_mul_sub_one, mul_zero]
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

private theorem topCoefficientDetector_add (q r : P) :
    topCoefficientDetector p (q + r) =
      topCoefficientDetector p q + topCoefficientDetector p r := by
  simp [topCoefficientDetector]
  ring

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
theorem p_mul_b_pred_ne_zero : (p : R p) * b p ^ (p - 1) ≠ 0 := by
  intro hzero
  have hmem : MvPolynomial.C (p : ℤ) * bp ^ (p - 1) ∈ baseIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [b] using hzero
  have hdet := topCoefficientDetector_eq_zero_of_mem_baseIdeal p hmem
  rw [topCoefficientDetector_top] at hdet
  exact (show (p : ZMod (p ^ 2)) ≠ 0 by
    rw [← ZMod.val_ne_zero]
    have hlt : p < p ^ 2 := by
      rw [pow_two]
      nlinarith [(Fact.out : p.Prime).two_le]
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, (p_pos p).ne']) hdet

/-- In a monic `AdjoinRoot`, a nonzero scalar times one of the canonical power-basis vectors is
nonzero.  This form does not require the coefficient ring to be a domain. -/
theorem scalar_mul_adjoinRoot_pow_ne_zero
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
    IsMonicOfDegree (gPolynomial p) p := by
  exact monicPolynomial_isMonicOfDegree (p_pos p) (gCoeff p)

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

/-- The images of the two base parameters in `B`. -/
abbrev aB : B p := algebraMap (R p) (B p) (a p)
abbrev bB : B p := algebraMap (R p) (B p) (b p)

theorem V_relation :
    V p ^ p = aB p ^ p * W p (bB p) (V p) := by
  have h := AdjoinRoot.eval₂_root (gPolynomial p)
  change (gPolynomial p).eval₂ (algebraMap (R p) (B p)) (V p) = 0 at h
  simp only [gPolynomial, monicPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, map_mul, map_neg, map_pow, map_natCast] at h
  rw [eq_neg_of_add_eq_zero_left h]
  simp [gCoeff, W, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
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
  monicPolynomial p (fCoeff p) + Polynomial.C (bridge p)

private theorem degree_C_lt_p {S : Type*} [CommRing S] (x : S) :
    (Polynomial.C x).degree < (p : WithBot ℕ) := by
  exact Polynomial.degree_C_lt.trans_le (WithBot.coe_le_coe.mpr (p_pos p))

theorem fPolynomial_monic : (fPolynomial p).Monic := by
  let hmonic := monicPolynomial_monic (S := B p) (p_pos p) (fCoeff p)
  apply hmonic.add_of_left
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
    monicPolynomial_natDegree (p_pos p) (fCoeff p)]
  exact degree_C_lt_p p (bridge p)

theorem fPolynomial_natDegree : (fPolynomial p).natDegree = p := by
  let hmonic := monicPolynomial_monic (S := B p) (p_pos p) (fCoeff p)
  have hdeg : (Polynomial.C (bridge p)).degree <
      (monicPolynomial p (fCoeff p)).degree := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
      monicPolynomial_natDegree (p_pos p) (fCoeff p)]
    exact degree_C_lt_p p (bridge p)
  rw [fPolynomial, Polynomial.natDegree_add_eq_left_of_degree_lt hdeg,
    monicPolynomial_natDegree (p_pos p) (fCoeff p)]

/-- The coordinate algebra `A`, obtained by adjoining `U` to `B`. -/
abbrev A := AdjoinRoot (fPolynomial p)

/-- The coordinate `U` in `A`. -/
def U : A p := AdjoinRoot.root (fPolynomial p)

/-- The image of `V` in `A`. -/
def v : A p := algebraMap (B p) (A p) (V p)

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

theorem U_relation :
    U p ^ p = algebraMap (B p) (A p) (aB p * bB p ^ (p - 1)) * W p
        (algebraMap (B p) (A p) (aB p)) (U p) -
      algebraMap (B p) (A p) (bridge p) := by
  have h := AdjoinRoot.eval₂_root (fPolynomial p)
  change (fPolynomial p).eval₂ (algebraMap (B p) (A p)) (U p) = 0 at h
  simp only [fPolynomial, monicPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, map_mul, map_neg, map_pow, map_natCast] at h
  have hsum :
      (∑ i : Fin p, algebraMap (B p) (A p) (fCoeff p i) * U p ^ i.1) =
        -algebraMap (B p) (A p) (aB p * bB p ^ (p - 1)) *
          W p (algebraMap (B p) (A p) (aB p)) (U p) := by
    simp [fCoeff, W, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at h
  linear_combination h

theorem v_relation :
    v p ^ p = algebraMap (R p) (A p) (a p ^ p) * W p
      (algebraMap (R p) (A p) (b p)) (v p) := by
  change (algebraMap (B p) (A p) (V p)) ^ p = _
  rw [← map_pow, V_relation p, map_mul]
  rw [map_W]
  simp only [v, aB, bB, map_pow,
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

/-- The images of the base parameters in the coordinate algebra. -/
abbrev aA : A p := algebraMap (R p) (A p) (a p)
abbrev bA : A p := algebraMap (R p) (A p) (b p)

/-- The carry term which will witness failure of the `p^2` power word is nonzero.  The proof
uses the detector theorem in `R`, followed successively by the `V`- and `U`-power bases. -/
theorem carry_ne_zero :
    (p : A p) * bA p ^ (p - 1) * U p * v p ^ (p - 1) ≠ 0 := by
  have hpred : p - 1 < (gPolynomial p).natDegree := by
    rw [gPolynomial_natDegree]
    exact Nat.sub_one_lt (p_ne_zero p)
  have hB : algebraMap (R p) (B p) ((p : R p) * b p ^ (p - 1)) *
      V p ^ (p - 1) ≠ 0 :=
    scalar_mul_adjoinRoot_pow_ne_zero (gPolynomial p) (gPolynomial_monic p)
      ((p : R p) * b p ^ (p - 1)) (p_mul_b_pred_ne_zero p) (p - 1) hpred
  have hone : 1 < (fPolynomial p).natDegree := by
    rw [fPolynomial_natDegree]
    exact (Fact.out : p.Prime).one_lt
  have hA := scalar_mul_adjoinRoot_pow_ne_zero
    (fPolynomial p) (fPolynomial_monic p)
    (algebraMap (R p) (B p) ((p : R p) * b p ^ (p - 1)) * V p ^ (p - 1))
    hB 1 hone
  have heq :
      (p : A p) * bA p ^ (p - 1) * U p * v p ^ (p - 1) =
        algebraMap (B p) (A p)
          (algebraMap (R p) (B p) ((p : R p) * b p ^ (p - 1)) * V p ^ (p - 1)) *
            U p ^ 1 := by
    simp only [map_mul, map_pow, pow_one, v, bA,
      IsScalarTower.algebraMap_apply (R p) (B p) (A p)]
    rw [← IsScalarTower.algebraMap_apply (R p) (B p) (A p)]
    simp only [map_natCast]
    ring
  rw [heq]
  exact hA

/-- The two affine coordinates used to define the group-like character. -/
def L : A p := 1 + aA p * U p
def M : A p := 1 + bA p * v p

abbrev TensorSquare := TensorProduct (R p) (A p) (A p)

abbrev left : A p →ₐ[R p] TensorSquare p :=
  Algebra.TensorProduct.includeLeft

abbrev right : A p →ₐ[R p] TensorSquare p :=
  Algebra.TensorProduct.includeRight

/-- A completed Hopf-algebra closure certificate for the uniform equations.

The fields `lambda_mul_M` and `lambdaInv_mul_L` express
`lambda = L M⁻¹` and `lambdaInv = M L⁻¹` without choosing a `Units` wrapper. -/
structure HopfPackage where
  lambda : A p
  lambdaInv : A p
  lambda_mul_M : lambda * M p = L p
  lambdaInv_mul_L : lambdaInv * L p = M p
  lambda_mul_lambdaInv : lambda * lambdaInv = 1
  lambdaInv_mul_lambda : lambdaInv * lambda = 1
  comul : A p →ₐ[R p] TensorSquare p
  counit : A p →ₐ[R p] R p
  comul_coassoc :
    (Algebra.TensorProduct.assoc (R p) (R p) (R p) (A p) (A p) (A p)).toAlgHom.comp
        ((Algebra.TensorProduct.map comul (.id (R p) (A p))).comp comul) =
      (Algebra.TensorProduct.map (.id (R p) (A p)) comul).comp comul
  counit_left :
    (Algebra.TensorProduct.map counit (.id (R p) (A p))).comp comul =
      (Algebra.TensorProduct.lid (R p) (A p)).symm
  counit_right :
    (Algebra.TensorProduct.map (.id (R p) (A p)) counit).comp comul =
      (Algebra.TensorProduct.rid (R p) (R p) (A p)).symm
  comul_U : comul (U p) =
      left p (U p) + left p lambda * right p (U p)
  comul_v : comul (v p) =
      left p (v p) * right p lambdaInv + right p (v p)
  comul_lambda : comul lambda =
    left p lambda * right p lambda
  comul_lambdaInv : comul lambdaInv =
      left p lambdaInv * right p lambdaInv
  counit_U : counit (U p) = 0
  counit_v : counit (v p) = 0
  counit_lambda : counit lambda = 1
  counit_lambdaInv : counit lambdaInv = 1
  antipode : A p →ₐ[R p] A p
  antipode_right_identity :
    ((Algebra.TensorProduct.lift antipode (.id (R p) (A p)) fun _ ↦ Commute.all _).comp
      comul) = (Algebra.ofId (R p) (A p)).comp counit
  antipode_left_identity :
    ((Algebra.TensorProduct.lift (.id (R p) (A p)) antipode fun _ _ ↦ Commute.all _ _).comp
      comul) = (Algebra.ofId (R p) (A p)).comp counit

/-- The bialgebra instance certified by a `HopfPackage`. -/
@[reducible] noncomputable def HopfPackage.toBialgebra
    (H : HopfPackage p) : Bialgebra (R p) (A p) :=
  Bialgebra.ofAlgHom H.comul H.counit H.comul_coassoc H.counit_left H.counit_right

/-- The Hopf-algebra instance certified by a `HopfPackage`. -/
@[reducible] noncomputable def HopfPackage.toHopfAlgebra
    (H : HopfPackage p) : HopfAlgebra (R p) (A p) := by
  letI := H.toBialgebra
  exact HopfAlgebra.ofAlgHom H.antipode H.antipode_right_identity H.antipode_left_identity

namespace HopfPackage

open WithConv

/-- The universal `A`-valued point in the convolution monoid. -/
noncomputable def universalPoint (H : HopfPackage p) : WithConv (A p →ₐ[R p] A p) := by
  letI := H.toBialgebra
  exact toConv (AlgHom.id (R p) (A p))

/-- The coordinate-ring map of the `n`-th power word. -/
noncomputable def powerMap (H : HopfPackage p) (n : ℕ) : A p →ₐ[R p] A p := by
  letI := H.toBialgebra
  exact (universalPoint p H ^ n).ofConv

private theorem bialgebra_comulAlgHom (H : HopfPackage p) :
    letI := H.toBialgebra
    Bialgebra.comulAlgHom (R p) (A p) = H.comul := by
  rfl

/-- The geometric sum controlling a skew-primitive coordinate. -/
def geomSum (x : A p) (n : ℕ) : A p :=
  ∑ i ∈ Finset.range n, x ^ i

@[simp] theorem geomSum_zero (x : A p) : geomSum p x 0 = 0 := by
  simp [geomSum]

theorem geomSum_succ (x : A p) (n : ℕ) :
    geomSum p x (n + 1) = geomSum p x n + x ^ n := by
  simpa [geomSum] using Finset.sum_range_succ (fun i ↦ x ^ i) n

theorem geomSum_mul_add_one (x : A p) (n : ℕ) :
    geomSum p x n * x + 1 = geomSum p x (n + 1) := by
  induction n with
  | zero => simp [geomSum]
  | succ n ih =>
      calc
        geomSum p x (n + 1) * x + 1 = (geomSum p x n + x ^ n) * x + 1 := by
          rw [geomSum_succ p]
        _ = (geomSum p x n * x + 1) + x ^ n * x := by ring
        _ = geomSum p x (n + 1) + x ^ n * x := by rw [ih]
        _ = geomSum p x (n + 1) + x ^ (n + 1) := by rw [pow_succ]
        _ = geomSum p x (n + 1 + 1) := (geomSum_succ p x (n + 1)).symm

@[simp] theorem powerMap_zero_apply (H : HopfPackage p) (x : A p) :
    powerMap p H 0 x = algebraMap (R p) (A p)
      (H.counit x) := by
  letI := H.toBialgebra
  rfl

theorem powerMap_succ_U (H : HopfPackage p) (n : ℕ) :
    powerMap p H (n + 1) (U p) =
      powerMap p H n (U p) + powerMap p H n H.lambda * U p := by
  letI := H.toBialgebra
  calc
    powerMap p H (n + 1) (U p) =
        (universalPoint p H ^ n * universalPoint p H).ofConv (U p) :=
      congr_arg (fun f : WithConv (A p →ₐ[R p] A p) ↦ f.ofConv (U p))
        (pow_succ (universalPoint p H) n)
    _ = powerMap p H n (U p) + powerMap p H n H.lambda * U p := by
      rw [AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
        bialgebra_comulAlgHom p H, H.comul_U]
      simp [universalPoint, powerMap]

theorem powerMap_succ_v (H : HopfPackage p) (n : ℕ) :
    powerMap p H (n + 1) (v p) =
      powerMap p H n (v p) * H.lambdaInv + v p := by
  letI := H.toBialgebra
  calc
    powerMap p H (n + 1) (v p) =
        (universalPoint p H ^ n * universalPoint p H).ofConv (v p) :=
      congr_arg (fun f : WithConv (A p →ₐ[R p] A p) ↦ f.ofConv (v p))
        (pow_succ (universalPoint p H) n)
    _ = powerMap p H n (v p) * H.lambdaInv + v p := by
      rw [AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
        bialgebra_comulAlgHom p H, H.comul_v]
      simp [universalPoint, powerMap]

theorem powerMap_succ_lambda (H : HopfPackage p) (n : ℕ) :
    powerMap p H (n + 1) H.lambda = powerMap p H n H.lambda * H.lambda := by
  letI := H.toBialgebra
  calc
    powerMap p H (n + 1) H.lambda =
        (universalPoint p H ^ n * universalPoint p H).ofConv H.lambda :=
      congr_arg (fun f : WithConv (A p →ₐ[R p] A p) ↦ f.ofConv H.lambda)
        (pow_succ (universalPoint p H) n)
    _ = powerMap p H n H.lambda * H.lambda := by
      rw [AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
        bialgebra_comulAlgHom p H, H.comul_lambda]
      simp [universalPoint, powerMap]

theorem powerMap_succ_lambdaInv (H : HopfPackage p) (n : ℕ) :
    powerMap p H (n + 1) H.lambdaInv = powerMap p H n H.lambdaInv * H.lambdaInv := by
  letI := H.toBialgebra
  calc
    powerMap p H (n + 1) H.lambdaInv =
        (universalPoint p H ^ n * universalPoint p H).ofConv H.lambdaInv :=
      congr_arg (fun f : WithConv (A p →ₐ[R p] A p) ↦ f.ofConv H.lambdaInv)
        (pow_succ (universalPoint p H) n)
    _ = powerMap p H n H.lambdaInv * H.lambdaInv := by
      rw [AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
        bialgebra_comulAlgHom p H, H.comul_lambdaInv]
      simp [universalPoint, powerMap]

theorem powerMap_lambda (H : HopfPackage p) (n : ℕ) :
    powerMap p H n H.lambda = H.lambda ^ n := by
  induction n with
  | zero =>
      letI := H.toBialgebra
      simp [powerMap_zero_apply, H.counit_lambda]
  | succ n ih =>
      rw [powerMap_succ_lambda p, ih, pow_succ]

theorem powerMap_lambdaInv (H : HopfPackage p) (n : ℕ) :
    powerMap p H n H.lambdaInv = H.lambdaInv ^ n := by
  induction n with
  | zero =>
      letI := H.toBialgebra
      simp [powerMap_zero_apply, H.counit_lambdaInv]
  | succ n ih =>
      rw [powerMap_succ_lambdaInv p, ih, pow_succ]

theorem powerMap_U (H : HopfPackage p) (n : ℕ) :
    powerMap p H n (U p) = geomSum p H.lambda n * U p := by
  induction n with
  | zero =>
      letI := H.toBialgebra
      simp [powerMap_zero_apply, H.counit_U]
  | succ n ih =>
      calc
        powerMap p H (n + 1) (U p) =
            powerMap p H n (U p) + powerMap p H n H.lambda * U p :=
          powerMap_succ_U p H n
        _ = geomSum p H.lambda n * U p + H.lambda ^ n * U p := by
          rw [ih, powerMap_lambda p]
        _ = geomSum p H.lambda (n + 1) * U p := by rw [geomSum_succ p, add_mul]

theorem powerMap_v (H : HopfPackage p) (n : ℕ) :
    powerMap p H n (v p) = v p * geomSum p H.lambdaInv n := by
  induction n with
  | zero =>
      letI := H.toBialgebra
      simp [powerMap_zero_apply, H.counit_v]
  | succ n ih =>
      calc
        powerMap p H (n + 1) (v p) =
            powerMap p H n (v p) * H.lambdaInv + v p := powerMap_succ_v p H n
        _ = v p * geomSum p H.lambdaInv n * H.lambdaInv + v p := by rw [ih]
        _ = v p * (geomSum p H.lambdaInv n * H.lambdaInv + 1) := by ring
        _ = v p * geomSum p H.lambdaInv (n + 1) := by rw [geomSum_mul_add_one p]

/-- The arithmetic certificate needed after Hopf closure: the two geometric sums have the
predicted carry.  Its nonvanishing on `U` is already the unconditional theorem `carry_ne_zero`. -/
structure PowerCertificate (H : HopfPackage p) : Prop where
  geomSum_lambda :
    geomSum p H.lambda (p ^ 2) = (p : A p) * bA p ^ (p - 1) * v p ^ (p - 1)
  geomSum_lambdaInv :
    geomSum p H.lambdaInv (p ^ 2) = (p : A p) * bA p ^ (p - 1) * v p ^ (p - 1)

theorem powerMap_p_squared_U (H : HopfPackage p) (hpow : PowerCertificate p H) :
    powerMap p H (p ^ 2) (U p) =
      (p : A p) * bA p ^ (p - 1) * U p * v p ^ (p - 1) := by
  rw [powerMap_U p, hpow.geomSum_lambda]
  ring

theorem powerMap_p_squared_U_ne_zero (H : HopfPackage p) (hpow : PowerCertificate p H) :
    powerMap p H (p ^ 2) (U p) ≠ 0 := by
  rw [powerMap_p_squared_U p H hpow]
  exact carry_ne_zero p

/-- The bundled commutative Hopf algebra, conditional only on the explicit closure package. -/
noncomputable def coordinateHopfAlgebra (H : HopfPackage p) : CommHopfAlgCat (R p) := by
  letI := H.toHopfAlgebra
  exact CommHopfAlgCat.of (R p) (A p)

/-- Once the divided bridge and carry certificates are supplied, the uniform construction is a
finite free Hopf algebra of rank `p^2` whose `p^2`-power word is not the unit word. -/
theorem counterexample (H : HopfPackage p) (hpow : PowerCertificate p H) :
    Module.finrank (R p) (A p) = p ^ 2 ∧
      powerMap p H (p ^ 2) ≠
        (Algebra.ofId (R p) (A p)).comp H.counit := by
  refine ⟨finrank_A p, ?_⟩
  intro h
  apply powerMap_p_squared_U_ne_zero p H hpow
  have hU := DFunLike.congr_fun h (U p)
  simpa [H.counit_U] using hU

end HopfPackage

end Prime

end

end FiniteFlatGroupSchemes.GrothendieckCounterexampleAllPrimes
