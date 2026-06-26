/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-!
# `L`-function of an elliptic curve at a prime of good reduction (completion variant)

For an elliptic curve `E / ℚ` and a height-one prime `v` of `𝓞 ℚ` of good reduction, the value of
`E.LFunction` at the residue cardinality `‖v‖ = #κ_v` is `aᵥ = ‖v‖ + 1 - #E(κ_v)`, where `E(κ_v)`
is the (affine) point group of the reduction of `E` over the residue field of the local ring of
integers `v.adicCompletionIntegers ℚ`.

We work over the **abstract adic completion** `v.adicCompletion ℚ` — which is exactly the local
field that `WeierstrassCurve.LFunction` is *defined* with via its Euler product — rather than over
`ℚ_[p]`. This avoids transporting `minimal` / `reduction` / point counts across an isomorphism
`v.adicCompletion ℚ ≃ ℚ_[p]` (mathlib has the isomorphism, `Padic.adicCompletionEquiv`, but not the
functoriality of those constructions), which is what blocks a direct `ℚ_[p]` phrasing.

The argument has two parts:

* `localEulerFactor_apply_of_hasGoodReduction` (**fully proved**, the elliptic-curve content):
  reading off the linear coefficient `aᵥ` of the reciprocal `1 / (1 - aᵥ T + ‖v‖ T²)` of the local
  polynomial. Concretely `localEulerFactor` at `‖v‖ = ‖v‖¹` is `coeff 1` of `invOfUnit` of the local
  polynomial, which is minus its degree-`1` coefficient, namely `aᵥ`.
* The Euler-product evaluation `E.LFunction ‖v‖ = (local factor at v) ‖v‖`. This is pure
  Dirichlet-series plumbing (every other local factor `ofPowerSeries ‖w‖ _` is supported on powers
  of a different rational prime `‖w‖` and so vanishes at `‖v‖`); it is independent of elliptic
  curves. We take it as the named hypothesis `hEuler` of the final theorem rather than reproving the
  Euler-product machinery here.
-/

open ArithmeticFunction IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
  IsLocalRing PowerSeries

namespace ArithmeticFunction

/-- A finite Dirichlet convolution evaluated at `1` is the product of the values at `1`. -/
theorem prod_apply_one {ι : Type*} (g : ι → ArithmeticFunction ℤ) (s : Finset ι) :
    (∏ i ∈ s, g i) 1 = ∏ i ∈ s, (g i) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_apply_one, ih, Finset.prod_insert ha]

/-- A finite Dirichlet convolution of arithmetic functions each taking value `1` at `1`, evaluated
at a prime `ℓ`, equals the sum of the values at `ℓ`. -/
theorem prod_apply_prime {ι : Type*} (g : ι → ArithmeticFunction ℤ) (s : Finset ι)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hg1 : ∀ i ∈ s, (g i) 1 = 1) :
    (∏ i ∈ s, g i) ℓ = ∑ i ∈ s, (g i) ℓ := by
  classical
  induction s using Finset.induction with
  | empty => simp [one_apply_ne hℓ.ne_one]
  | insert a s ha ih =>
    have hmem : ∀ i ∈ s, (g i) 1 = 1 := fun i hi => hg1 i (Finset.mem_insert_of_mem hi)
    have hsum : (g a * ∏ i ∈ s, g i) ℓ =
        (g a) 1 * (∏ i ∈ s, g i) ℓ + (g a) ℓ * (∏ i ∈ s, g i) 1 := by
      rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => (g a) x * (∏ i ∈ s, g i) y),
        hℓ.divisors, Finset.sum_pair hℓ.ne_one.symm]
      simp [Nat.div_self hℓ.pos]
    have hone : (∏ i ∈ s, g i) 1 = 1 := by
      rw [prod_apply_one]; exact Finset.prod_eq_one hmem
    rw [Finset.prod_insert ha, Finset.sum_insert ha, hsum, hone, ih hmem,
      hg1 a (Finset.mem_insert_self a s)]
    ring

open Filter in
/-- The Euler product of a Northcott family of local factors `ofPowerSeries (q i) (f i)`, evaluated
at the prime `q i₀`, collapses to the single factor at `i₀` (all others vanish there). -/
theorem eulerProduct_ofPowerSeries_apply_prime {ι : Type*} (q : ι → ℕ) [Northcott q]
    (f : ι → PowerSeries ℤ) (hf : ∀ i, (f i).constantCoeff = 1)
    (i₀ : ι) (hprime : (q i₀).Prime)
    (hvanish : ∀ i, i ≠ i₀ → ofPowerSeries (q i) (f i) (q i₀) = 0) :
    eulerProduct (fun i ↦ ofPowerSeries (q i) (f i)) (q i₀)
      = ofPowerSeries (q i₀) (f i₀) (q i₀) := by
  classical
  have hg1 : ∀ i, (ofPowerSeries (q i) (f i)) 1 = 1 := fun i => by
    rw [ofPowerSeries_apply_one]; exact hf i
  have htend := tendsTo_eulerProduct_ofPowerSeries q f hf (q i₀)
  rw [eventually_atTop] at htend
  obtain ⟨s₀, hs₀⟩ := htend
  rw [← hs₀ (insert i₀ s₀) (Finset.subset_insert i₀ s₀),
    prod_apply_prime _ _ hprime (fun i _ => hg1 i),
    Finset.sum_eq_single i₀ (fun i _ hii₀ => hvanish i hii₀)
      (fun h => absurd (Finset.mem_insert_self i₀ s₀) h)]

end ArithmeticFunction

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))

/-- **The elliptic-curve content.** For a prime `v` of good reduction (with finite residue field of
size `> 1`), the local Euler factor of `E` evaluated at the residue cardinality `‖v‖` equals
`aᵥ = ‖v‖ + 1 - #E(κ_v)`. -/
theorem localEulerFactor_apply_of_hasGoodReduction
    (hq : 1 < Nat.card (ResidueField (v.adicCompletionIntegers ℚ)))
    (hgood : ((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    (E.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ)
        (Nat.card (ResidueField (v.adicCompletionIntegers ℚ))) =
      Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) + 1 -
        Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal
          (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point := by
  set R := v.adicCompletionIntegers ℚ with hR
  set W := E.baseChange (v.adicCompletion ℚ) with hW
  set q := Nat.card (ResidueField R) with hqdef
  -- The local Euler factor is `ofPowerSeries q (localPowerSeries)`, so at `q = q¹` it is the
  -- degree-`1` coefficient of the local power series.
  have hloc : W.localEulerFactor R q = (W.localPowerSeries R).coeff 1 := by
    have h := ofPowerSeries_apply_pow hq (W.localPowerSeries R) 1
    rw [pow_one] at h
    exact h
  -- For a power series with constant term `1`, `coeff 1` of its inverse is minus its `coeff 1`.
  have key : ∀ φ : PowerSeries ℤ, constantCoeff φ = 1 →
      coeff 1 (φ.invOfUnit 1) = - coeff 1 φ := by
    intro φ hφ
    have hcc : constantCoeff (φ.invOfUnit 1) = 1 := by simp
    have h2 : coeff 1 (φ * φ.invOfUnit 1) = 0 := by
      rw [mul_invOfUnit φ 1 (by simpa using hφ)]; simp
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ] at h2
    simp [coeff_zero_eq_constantCoeff, hφ, hcc] at h2
    linarith [h2]
  -- The local polynomial in the good-reduction case is `1 - aᵥ X + ‖v‖ X²`, whose `coeff 1` is
  -- `-aᵥ`; hence the inverse has `coeff 1` equal to `aᵥ = ‖v‖ + 1 - #E(κ_v)`.
  rw [hloc, WeierstrassCurve.localPowerSeries, WeierstrassCurve.localPolynomial, if_pos hgood,
    key _ (by simp)]
  rw [Polynomial.coeff_coe]
  simp [Polynomial.coeff_one, hqdef]
  rfl

/-- **Completion variant of the good-reduction `L`-function formula.** For an elliptic curve `E / ℚ`
and a height-one prime `v` of `𝓞 ℚ` of good reduction, the value of `E.LFunction` at the residue
cardinality `‖v‖` is `aᵥ = ‖v‖ + 1 - #E(κ_v)`.

The hypothesis `hEuler` is the (elliptic-curve-independent) statement that the Euler product
defining `E.LFunction` collapses, at the prime `‖v‖`, to its single local factor at `v`. -/
theorem lFunction_eq_of_hasGoodReduction
    (hq : 1 < Nat.card (ResidueField (v.adicCompletionIntegers ℚ)))
    (hEuler : E.LFunction (Nat.card (ResidueField (v.adicCompletionIntegers ℚ))) =
      (E.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ)
        (Nat.card (ResidueField (v.adicCompletionIntegers ℚ))))
    (hgood : ((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    E.LFunction (Nat.card (ResidueField (v.adicCompletionIntegers ℚ))) =
      Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) + 1 -
        Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal
          (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point := by
  rw [hEuler, localEulerFactor_apply_of_hasGoodReduction E v hq hgood]

open Rat.HeightOneSpectrum in
/-- The residue field of `p.adicCompletionIntegers ℚ` is, via the isomorphisms
`adicCompletionIntegers ℚ p ≃ ℤ_[‖p‖]` and `ResidueField ℤ_[ℓ] ≃ ZMod ℓ`, the finite field of size
the rational prime `‖p‖ = primesEquiv p`. -/
theorem card_residueField_eq (p : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (ResidueField (p.adicCompletionIntegers ℚ)) = (primesEquiv p : ℕ) := by
  haveI : Fact (primesEquiv p).1.Prime := ⟨(primesEquiv p).2⟩
  have e := (IsLocalRing.ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv p).toRingEquiv).trans PadicInt.residueField
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

/-- The residue cardinality `‖p‖` is a prime number. -/
theorem prime_card_residueField (p : HeightOneSpectrum (𝓞 ℚ)) :
    (Nat.card (ResidueField (p.adicCompletionIntegers ℚ))).Prime := by
  rw [card_residueField_eq]; exact (Rat.HeightOneSpectrum.primesEquiv p).2

theorem one_lt_card_residueField (p : HeightOneSpectrum (𝓞 ℚ)) :
    1 < Nat.card (ResidueField (p.adicCompletionIntegers ℚ)) :=
  (prime_card_residueField p).one_lt

open Rat.HeightOneSpectrum in
/-- The residue cardinalities `‖w‖` form a Northcott family: only finitely many primes `w` have
`‖w‖ ≤ b`, since `‖w‖ = primesEquiv w` and `primesEquiv` is a bijection onto `Nat.Primes`. -/
instance instNorthcottResidue :
    Northcott (fun w : HeightOneSpectrum (𝓞 ℚ) ↦
      Nat.card (ResidueField (w.adicCompletionIntegers ℚ))) where
  finite_le b := by
    have hfin : (Subtype.val ⁻¹' Set.Iic b : Set Nat.Primes).Finite :=
      (Set.finite_Iic b).preimage Subtype.val_injective.injOn
    have heq : {w : HeightOneSpectrum (𝓞 ℚ) |
        Nat.card (ResidueField (w.adicCompletionIntegers ℚ)) ≤ b}
        = primesEquiv ⁻¹' (Subtype.val ⁻¹' Set.Iic b) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, card_residueField_eq]
    rw [heq]
    exact hfin.preimage primesEquiv.injective.injOn

open Rat.HeightOneSpectrum in
/-- **Euler-product evaluation.** The `L`-function (an Euler product of the local factors) evaluated
at the residue cardinality `‖p‖` collapses to the single local factor at `p`: every other factor
`ofPowerSeries ‖w‖ _` is supported on powers of a different rational prime `‖w‖` and so vanishes at
the prime `‖p‖`. -/
theorem lFunction_apply_eq_localEulerFactor (E : WeierstrassCurve ℚ)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    E.LFunction (Nat.card (ResidueField (p.adicCompletionIntegers ℚ))) =
      (E.baseChange (p.adicCompletion ℚ)).localEulerFactor (p.adicCompletionIntegers ℚ)
        (Nat.card (ResidueField (p.adicCompletionIntegers ℚ))) := by
  have hf : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ((E.baseChange (w.adicCompletion ℚ)).localPowerSeries
        (w.adicCompletionIntegers ℚ)).constantCoeff = 1 := by
    intro w; simp [WeierstrassCurve.localPowerSeries]
  have hvanish : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ p →
      ofPowerSeries (Nat.card (ResidueField (w.adicCompletionIntegers ℚ)))
        ((E.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ))
        (Nat.card (ResidueField (p.adicCompletionIntegers ℚ))) = 0 := by
    intro w hwp
    have hnot : ¬ ∃ k, (Nat.card (ResidueField (w.adicCompletionIntegers ℚ))) ^ k
        = Nat.card (ResidueField (p.adicCompletionIntegers ℚ)) := by
      rintro ⟨k, hk⟩
      have hqwp : Nat.card (ResidueField (w.adicCompletionIntegers ℚ))
          ≠ Nat.card (ResidueField (p.adicCompletionIntegers ℚ)) := by
        rw [card_residueField_eq, card_residueField_eq]
        exact fun h => hwp (primesEquiv.injective (Subtype.val_injective h))
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [pow_zero] at hk; exact (prime_card_residueField p).ne_one hk.symm
      · exact hqwp ((Nat.prime_dvd_prime_iff_eq (prime_card_residueField w)
          (prime_card_residueField p)).mp (hk ▸ dvd_pow_self _ hk1.ne'))
    rw [ofPowerSeries_apply (one_lt_card_residueField w),
      Function.extend_apply' _ _ _ hnot, Pi.zero_apply]
  simp only [WeierstrassCurve.LFunction, WeierstrassCurve.localEulerFactor]
  exact ArithmeticFunction.eulerProduct_ofPowerSeries_apply_prime _ _ hf p
    (prime_card_residueField p) hvanish

example (E : WeierstrassCurve ℚ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ((E.baseChange (p.adicCompletion ℚ)).minimal
      (p.adicCompletionIntegers ℚ)).HasGoodReduction (p.adicCompletionIntegers ℚ)) :
    letI R := p.adicCompletionIntegers ℚ
    E.LFunction (Nat.card (ResidueField R)) = Nat.card (ResidueField R) + 1 -
      Nat.card (((E.baseChange (p.adicCompletion ℚ)).minimal R).reduction R).toAffine.Point :=
  lFunction_eq_of_hasGoodReduction E p (one_lt_card_residueField p)
    (lFunction_apply_eq_localEulerFactor E p) hp

open Rat.HeightOneSpectrum in
example (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hp : ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]) :
    E.LFunction p = p + 1 -
      Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point := by
  -- Work at the height-one prime `v` of `𝓞 ℚ` corresponding to `p`; then `‖v‖ = p`.
  set v : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm ⟨p, Fact.out⟩ with hv
  have hcard : Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = p := by
    rw [card_residueField_eq, hv, Equiv.apply_symm_apply]
  -- The two facts still needed are the *functoriality* of the reduction theory across the
  -- continuous ℚ-algebra isomorphism `v.adicCompletion ℚ ≃ ℚ_[p]` (and `v.adicCompletionIntegers ℚ
  -- ≃ ℤ_[p]`): that good reduction transfers, and that the two reductions have the same number of
  -- points. Mathlib has the isomorphism (`Padic.adicCompletionEquiv`) but not this functoriality of
  -- `minimal` / `reduction` / `HasGoodReduction`.
  have hgood' : ((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ) := by
    sorry
  have hpoint : Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point
      = Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal
          (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point := by
    sorry
  have main := lFunction_eq_of_hasGoodReduction E v (one_lt_card_residueField v)
    (lFunction_apply_eq_localEulerFactor E v) hgood'
  rw [hcard] at main
  rw [hpoint]
  exact main

end WeierstrassCurve
