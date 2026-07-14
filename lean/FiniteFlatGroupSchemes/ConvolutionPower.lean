/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Convolution powers of the identity of a bialgebra

For an `R`-bialgebra `C` and a commutative `R`-algebra `A`, the algebra homomorphisms
`C →ₐ[R] A` form a monoid under the convolution product, constructed in
`Mathlib.RingTheory.Bialgebra.Convolution`.  This file computes convolution products, and
convolution powers of the identity map, on group-like and skew-primitive elements.

## Main definitions

* `AlgHom.convPowId R A n`: the `n`-th convolution power of the identity map of a commutative
  `R`-bialgebra `A`.  On the affine monoid scheme `Spec A`, this is the coordinate-ring map of
  the pointwise `n`-th power map `x ↦ xⁿ`.

## Main results

* `AlgHom.convMul_apply_of_isGroupLikeElem`: on a group-like element, a convolution product
  `f * g` evaluates to the pointwise product of `f` and `g`.
* `AlgHom.convPowId_apply_of_isGroupLikeElem`: on a group-like element `a`, the `n`-th
  convolution power of the identity is `a ^ n`.
* `AlgHom.convPowId_apply_of_comul_eq_tmul_one_add_tmul` and
  `AlgHom.convPowId_apply_of_comul_eq_tmul_add_one_tmul`: on a skew-primitive element `x`,
  with `Δ(x) = x ⊗ 1 + a ⊗ x` (respectively `Δ(x) = x ⊗ a + 1 ⊗ x`), the `n`-th convolution
  power of the identity is the geometric sum `(1 + a + ⋯ + aⁿ⁻¹) * x` (respectively
  `x * (1 + a + ⋯ + aⁿ⁻¹)`).

## Implementation notes

This file was written by the AI assistants Codex (OpenAI) and Claude (Anthropic).

## Tags

bialgebra, convolution, group-like, skew-primitive, power map
-/

namespace AlgHom

open Coalgebra Finset TensorProduct WithConv

section ConvMul

variable {R C A : Type*} [CommSemiring R] [Semiring C] [Bialgebra R C] [CommSemiring A]
  [Algebra R A]

/-- The convolution product of two algebra homomorphisms, evaluated on a group-like element,
is the pointwise product. -/
theorem convMul_apply_of_isGroupLikeElem (f g : WithConv (C →ₐ[R] A)) {a : C}
    (ha : IsGroupLikeElem R a) : (f * g) a = f a * g a := by
  rw [convMul_apply, ha.comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul]

/-- The convolution product of two algebra homomorphisms, evaluated on an element `x` with
`Δ(x) = x ⊗ 1 + a ⊗ x`. -/
theorem convMul_apply_of_comul_eq_tmul_one_add_tmul (f g : WithConv (C →ₐ[R] A)) {x a : C}
    (hx : comul (R := R) x = x ⊗ₜ[R] 1 + a ⊗ₜ[R] x) : (f * g) x = f x + f a * g x := by
  rw [convMul_apply, hx, map_add, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul, map_one, mul_one]

/-- The convolution product of two algebra homomorphisms, evaluated on an element `x` with
`Δ(x) = x ⊗ a + 1 ⊗ x`. -/
theorem convMul_apply_of_comul_eq_tmul_add_one_tmul (f g : WithConv (C →ₐ[R] A)) {x a : C}
    (hx : comul (R := R) x = x ⊗ₜ[R] a + 1 ⊗ₜ[R] x) : (f * g) x = f x * g a + g x := by
  rw [convMul_apply, hx, map_add, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end ConvMul

section ConvPowId

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Bialgebra R A]

/-- The `n`-th convolution power of the identity map of a commutative `R`-bialgebra `A`.
On the affine monoid scheme `Spec A`, this is the coordinate-ring map of the pointwise
`n`-th power map `x ↦ xⁿ`. -/
noncomputable def convPowId (n : ℕ) : A →ₐ[R] A :=
  (toConv (AlgHom.id R A) ^ n).ofConv

@[simp] theorem convPowId_zero_apply (x : A) :
    convPowId R A 0 x = algebraMap R A (counit x) := rfl

@[simp] theorem convPowId_one : convPowId R A 1 = AlgHom.id R A := by
  rw [convPowId, pow_one]

variable {R A}

/-- On a group-like element `a`, the `n`-th convolution power of the identity is `a ^ n`. -/
theorem convPowId_apply_of_isGroupLikeElem {a : A} (ha : IsGroupLikeElem R a) (n : ℕ) :
    convPowId R A n a = a ^ n := by
  induction n with
  | zero => rw [convPowId_zero_apply, ha.counit_eq_one, map_one, pow_zero]
  | succ n ih =>
      calc convPowId R A (n + 1) a
          = (toConv (AlgHom.id R A) ^ n * toConv (AlgHom.id R A)) a := by
            rw [convPowId, pow_succ]
        _ = convPowId R A n a * a := convMul_apply_of_isGroupLikeElem _ _ ha
        _ = a ^ (n + 1) := by rw [ih, pow_succ]

/-- On an element `x` with `Δ(x) = x ⊗ 1 + a ⊗ x` and `ε(x) = 0`, the `n`-th convolution
power of the identity is the geometric sum `(1 + a + ⋯ + aⁿ⁻¹) * x`. -/
theorem convPowId_apply_of_comul_eq_tmul_one_add_tmul {x a : A}
    (hx : comul (R := R) x = x ⊗ₜ[R] 1 + a ⊗ₜ[R] x) (hx0 : counit (R := R) x = 0) (n : ℕ) :
    convPowId R A n x = (∑ i ∈ range n, a ^ i) * x := by
  induction n with
  | zero => rw [convPowId_zero_apply, hx0, map_zero, geom_sum_zero, zero_mul]
  | succ n ih =>
      calc convPowId R A (n + 1) x
          = (toConv (AlgHom.id R A) * toConv (AlgHom.id R A) ^ n) x := by
            rw [convPowId, pow_succ']
        _ = x + a * convPowId R A n x :=
            convMul_apply_of_comul_eq_tmul_one_add_tmul _ _ hx
        _ = (∑ i ∈ range (n + 1), a ^ i) * x := by rw [ih, geom_sum_succ]; ring

/-- On an element `x` with `Δ(x) = x ⊗ a + 1 ⊗ x` and `ε(x) = 0`, the `n`-th convolution
power of the identity is the geometric sum `x * (1 + a + ⋯ + aⁿ⁻¹)`. -/
theorem convPowId_apply_of_comul_eq_tmul_add_one_tmul {x a : A}
    (hx : comul (R := R) x = x ⊗ₜ[R] a + 1 ⊗ₜ[R] x) (hx0 : counit (R := R) x = 0) (n : ℕ) :
    convPowId R A n x = x * ∑ i ∈ range n, a ^ i := by
  induction n with
  | zero => rw [convPowId_zero_apply, hx0, map_zero, geom_sum_zero, mul_zero]
  | succ n ih =>
      calc convPowId R A (n + 1) x
          = (toConv (AlgHom.id R A) ^ n * toConv (AlgHom.id R A)) x := by
            rw [convPowId, pow_succ]
        _ = convPowId R A n x * a + x :=
            convMul_apply_of_comul_eq_tmul_add_one_tmul _ _ hx
        _ = x * ∑ i ∈ range (n + 1), a ^ i := by rw [ih, geom_sum_succ]; ring

end ConvPowId

end AlgHom
