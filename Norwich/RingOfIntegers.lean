import Norwich.Instances
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.ModCases
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Tactic.Qify

namespace QuadraticInteger

open QuadraticAlgebra NumberField Set Polynomial Algebra Int IntermediateField

variable {d : ℤ}

local notation3 "K" => QuadraticAlgebra ℚ d 0

local notation3 "R" => QuadraticAlgebra ℤ d 0

variable [sf : Fact (Squarefree d)] [hd1 : Fact (d ≠ 1)]

instance field : Fact (∀ (r : ℚ), r ^ 2 ≠ d + 0 * r) := by
  refine ⟨fun r h ↦ ?_⟩
  rsuffices ⟨s, hs⟩ : IsSquare d
  · have hu : IsUnit s := sf.1 s (dvd_of_eq hs.symm)
    have hd : d = 1 := by
      have h0 : 0 ≤ d := by rw [hs]; exact mul_self_nonneg s
      rcases Int.isUnit_iff.1 (hs ▸ hu.mul hu) with h1 | h1 <;> omega
    exact hd1.1 hd
  exact Rat.isSquare_intCast_iff.1 ⟨r, by grind⟩

instance : NumberField K where

section trace_and_norm

variable {a b : ℚ}

local notation3 "z" => a + b • (ω : K)

lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  simp only [mem_range, eq_ratCast]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, by simp +contextual⟩
  rw [← im_C (a := (d : ℚ)) (b := 0) y, QuadraticAlgebra.C_eq_algebraMap, eq_ratCast, hy]
  simp

lemma minpoly (hb : b ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  refine (minpoly.unique' _ _ (by monicity!) ?_ (fun q qdeg_lt_2 ↦ ?_)).symm
  · calc
      _ = z ^ 2 - 2 * a * z + (a ^ 2 - d * b ^ 2) := by simp
      _ = (b • (ω : K)) ^ 2 - d * b ^ 2 := by ring
      _ = b ^ 2 • ((ω : K) * (ω : K)) - d * b ^ 2 := by rw [smul_pow, pow_two ω]
      _ = 0 := by simp [omega_mul_omega_eq_add, Algebra.smul_def] ; ring
  · replace qdeg_lt_2 : q.degree ≤ 1 := by
      apply Order.le_of_lt_succ
      convert qdeg_lt_2; symm; compute_degree!
    rw [eq_X_add_C_of_degree_le_one qdeg_lt_2]
    refine imp_iff_or_not.1 (fun h ↦ ?_)
    simp only [map_add, map_mul, aeval_C, eq_ratCast, aeval_X] at h
    by_cases hcoe_one : (q.coeff 1 : K) = 0
    · simp_all
    replace h : z = - (q.coeff 0) / (q.coeff 1) := by grind [eq_div_iff]
    contrapose hb
    exact (rational_iff (a := a) (d := d)).1 ⟨-q.coeff 0 / q.coeff 1, by simp [h]⟩

lemma adjoin_z_eq_top (h : b ≠ 0) : ℚ⟮z⟯ = ⊤ := by
  apply (Field.primitive_element_iff_minpoly_natDegree_eq ℚ z).mpr
  rw [finrank_eq_two, minpoly h]
  compute_degree!

lemma trace : trace ℚ K z = 2 * a := by
  rcases eq_or_ne b 0 with rfl | h
  · simpa [finrank_eq_two] using trace_algebraMap (S := K) a
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff ℚ z, minpoly h, adjoin_z_eq_top h]
    set p := X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) with hp_def
    have p_deg_2 : p.natDegree = 2 := by rw [hp_def]; compute_degree!
    rw [nextCoeff_of_natDegree_pos (p := p) (by grind)]
    simp only [IntermediateField.finrank_top, Nat.cast_one, p_deg_2, Nat.add_one_sub_one, mul_neg,
      one_mul]
    simp only [hp_def, map_mul, map_sub, map_pow, map_intCast, coeff_add, coeff_sub, coeff_X_pow,
      OfNat.one_ne_ofNat, ↓reduceIte, coeff_mul_X, mul_coeff_zero, coeff_C_zero, zero_sub,
      coeff_intCast_mul, neg_add_rev, neg_sub, neg_neg, add_eq_right]
    rw [← Polynomial.C_pow, ← Polynomial.C_pow, coeff_C, coeff_C]
    simp

lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
    rcases eq_or_ne b 0 with rfl | h
    · rw [← eq_ratCast (algebraMap ℚ K)]
      simp [-eq_ratCast, finrank_eq_two]
    · let pb := PowerBasis.ofAdjoinEqTop' (IsIntegral.isIntegral z)
        (by simpa using adjoin_z_eq_top h)
      have : z = pb.gen := by simp [pb]
      rw [this, pb.norm_gen_eq_coeff_zero_minpoly, ← this, minpoly h, ← pb.finrank]
      simp [finrank_eq_two, coeff_zero_eq_eval_zero]

section integrality

lemma trace_int (hz : IsIntegral ℤ z) : ∃ (t : ℤ), t = 2 * a := by
  simpa [trace, IsIntegrallyClosed.isIntegral_iff] using isIntegral_trace (L := ℚ) hz

lemma a_half_int (hz : IsIntegral ℤ z) (ha : ¬(∃ (A : ℤ), A = a)) :
    ∃ (A : ℤ), A = a - 2⁻¹ := by
  obtain ⟨t, ht⟩ := trace_int hz
  refine ⟨(t - 1) / 2, ?_⟩
  obtain ⟨k, rfl⟩ : Odd t := by
    refine not_even_iff_odd.1 (fun ⟨n, hn⟩ ↦ ha ⟨t / 2, ?_⟩)
    rw [hn] at ht
    grind
  rw [cast_div ⟨k, by grind⟩ (by norm_num)]
  grind

lemma norm_int (hz : IsIntegral ℤ z) : ∃ (n : ℤ), n = a ^ 2 - d * b ^ 2 := by
  simpa [norm, IsIntegrallyClosed.isIntegral_iff] using isIntegral_norm ℚ hz

noncomputable def n (hz : IsIntegral ℤ z) := (norm_int hz).choose

lemma n_spec (hz : IsIntegral ℤ z) : n hz = a ^ 2 - d * b ^ 2 := (norm_int hz).choose_spec

lemma four_n (hz : IsIntegral ℤ z) : 4 * n hz = (2 * a)^2 - d * (2 * b) ^ 2 := by
  grind [n_spec]

lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  refine ⟨r.num, ?_⟩
  suffices IsUnit (r.den : ℤ) by
    rcases isUnit_iff.1 this with H | H
    · simpa using r.coe_int_num_of_den_eq_one (by grind)
    · grind
  refine hn _ ?_
  rw [← pow_two, ← Nat.cast_pow, ofNat_dvd_left, ← ofNat_dvd_left, Nat.cast_pow]
  obtain ⟨m, hm⟩ := hnr
  refine dvd_of_dvd_mul_left_of_gcd_one (c := r.num ^ 2) ⟨m, Eq.symm ?_⟩ <|
    isCoprime_iff_gcd_eq_one.1 r.isCoprime_num_den.symm.pow_right.pow_left
  qify
  rw [mul_comm, ← eq_div_iff (by simp), mul_div_assoc, ← div_pow, Rat.num_div_den, hm]

lemma two_b_int (hz : IsIntegral ℤ z) : ∃ (B₂ : ℤ), B₂ = 2 * b := by
  obtain ⟨y, hy⟩ := trace_int hz
  exact squarefree_mul sf.out ⟨y ^ 2 - (4 * n hz), by grind [four_n hz]⟩

lemma b_int_of_a_int (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) : ∃ (B : ℤ), B = b := by
  obtain ⟨A, hA⟩ := ha
  exact squarefree_mul sf.out ⟨A ^ 2 - (n hz), by grind [four_n hz]⟩

lemma a_not_int (hz : IsIntegral ℤ z) (ha : ¬∃ (A : ℤ), A = a) : d ≡ 1 [ZMOD 4] := by
  obtain ⟨t, Ht⟩ := trace_int hz
  have ht : ¬ Even t := fun ⟨t', ht'⟩ ↦ by
    qify at ht'
    exact ha ⟨t', by grind⟩
  obtain ⟨B, hB⟩ := two_b_int hz
  have h1 := Ht ▸ hB ▸ four_n hz
  norm_cast at h1
  obtain ⟨B', rfl⟩ : Odd B := by
    by_contra h
    obtain ⟨B', rfl⟩ := not_odd_iff_even.1 h
    exact ht ((even_pow (n := 2)).1 ⟨2 * (n hz + d * B' ^ 2), by grind⟩).1
  obtain ⟨t', ht'⟩ := not_even_iff_odd.1 ht
  exact modEq_iff_dvd.2 ⟨-t' ^ 2 - t' + d * B' ^ 2 + d * B' + n hz, by grind⟩

end integrality

end trace_and_norm

section d_2_3

theorem d_2_or_3 (hd : d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4]) : IsIntegralClosure R ℤ K := by
  refine ⟨fun z₁ z₂ h ↦ ?_, @fun ⟨a, b⟩ ↦ ⟨fun hz ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩⟩
  · injection h
    ext <;> simp_all
  · simp only [mk_eq_add_smul_omega, eq_ratCast] at hz
    obtain ⟨A, hA⟩ : ∃ (A : ℤ), A = a := by
      by_contra ha
      have := a_not_int hz ha
      rcases hd with hd | hd <;>
      grw [hd] at this <;> contradiction
    obtain ⟨B, hB⟩ := b_int_of_a_int hz ⟨A, hA⟩
    exact ⟨A + B • (ω : R), by ext <;> simp [← hA, ← hB, ← C_mul_eq_smul]⟩
  · exact hx ▸ (IsIntegral.isIntegral x).algebraMap

end d_2_3

section d_1

variable [h : Fact (d ≡ 1 [ZMOD 4])]

local notation3 "e" => (d - 1) / 4

omit sf hd1 in
lemma e_spec : 4 * e = d - 1 :=
  mul_ediv_cancel_of_emod_eq_zero <| emod_eq_emod_iff_emod_sub_eq_zero.mp h.1

local notation3 "S" => QuadraticAlgebra ℤ e 1

lemma algebra_S_K : ((1 + (ω : K)) / 2) * ((1 + ω) / 2) = e • 1 + 1 • ((1 + ω) / 2) :=
  calc (1 + (ω : K)) / 2 * ((1 + ω) / 2) = (1 + 2 * ω + ω * ω) / 4 := by ring
      _ = (1 + 2 * ω + (↑(4 * e + 1) : ℚ) • 1) / 4 := by simp [omega_mul_omega_eq_add, e_spec]
      _ = e • 1 + 1 • ((1 + ω) / 2) := by simp [Algebra.smul_def]; ring

instance : Algebra S K := (lift ⟨(1 + ω) / 2, algebra_S_K⟩).toRingHom.toAlgebra

lemma algebraMap_S_K_omega : algebraMap S K ω = 2⁻¹ * (ω + 1) := by
  change (lift ⟨(1 + ω) / 2, algebra_S_K⟩) ω = 2⁻¹ * (ω + 1)
  rw [lift_apply_apply]
  simp only [omega_re, omega_im, zero_smul, one_smul, zero_add]
  ring

lemma easy_incl_d_1 : IsIntegral ℤ (algebraMap S K ω) :=
  (IsIntegral.isIntegral ω).algebraMap

lemma d_1_int {a b : ℚ} (hz : IsIntegral ℤ (a + b • (ω : K))) (ha : ∃ (A : ℤ), A = a) :
    a + b • (ω : K) ∈ range (algebraMap S K) := by
  obtain ⟨B, rfl⟩ := b_int_of_a_int hz ha
  obtain ⟨A, rfl⟩ := ha
  rw [← RingHom.coe_range, cast_smul_eq_zsmul, zsmul_eq_mul]
  refine Subring.add_mem _ (by simp) (Subring.mul_mem _ (by simp) ⟨2 * ω - 1, ?_⟩)
  simp [map_ofNat, algebraMap_S_K_omega]

theorem d_1 : IsIntegralClosure S ℤ K := by
  refine ⟨fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h ↦ ?_, @fun ⟨a, b⟩ ↦ ⟨fun hz ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩⟩
  · simp only [mk_eq_add_smul_omega, algebraMap_int_eq, eq_intCast, zsmul_eq_mul, map_add,
    map_intCast, map_mul] at h
    rcases QuadraticAlgebra.ext_iff.1 h with ⟨hre, him⟩
    simp only [algebraMap_S_K_omega, re_add, re_intCast, re_mul, omega_re, re_one, zero_add,
      mul_one, im_add, omega_im, im_one, add_zero, im_intCast, mul_zero, im_mul, zero_mul,
      _root_.mul_eq_mul_right_iff, Int.cast_inj] at hre him
    have h2 : (2⁻¹ : K) = ⟨2⁻¹, 0⟩ := by
      apply inv_eq_of_mul_eq_one_left
      apply QuadraticAlgebra.ext <;> simp [re_mul, im_mul, re_ofNat, im_ofNat]
    rw [h2] at hre him
    simp_all
  · rw [mk_eq_add_smul_omega, eq_ratCast] at ⊢ hz
    by_cases ha : ∃ (A : ℤ), A = a
    · exact d_1_int hz ha
    · let z' := a + b • (ω : K) - algebraMap S K ω
      obtain ⟨A, hA⟩ := a_half_int hz ha
      obtain ⟨B, hB⟩ := two_b_int hz
      have hz' : IsIntegral ℤ z' := hz.sub easy_incl_d_1
      rsuffices ⟨y, hy⟩ : ∃ y, (algebraMap S K) y = z'
      · exact ⟨y + ω, by simp [hy, z']⟩
      have H : z' = ↑(a - 2⁻¹) + (b - 2⁻¹) • (ω : K) := by
        simp [z', algebraMap_S_K_omega, Algebra.smul_def]
        grind
      rw [H] at hz' ⊢
      exact d_1_int hz' (a_half_int hz ha)
  · exact hx ▸ (IsIntegral.isIntegral x).algebraMap


end d_1

section discriminant

lemma quadratic_trace (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im := by
  obtain ⟨x, y⟩ := x
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b), Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply]
  simp [QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple]
  ring

lemma quadratic_discr (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = b ^ 2 + 4 * a := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  rw [quadratic_trace, quadratic_trace, quadratic_trace, quadratic_trace]
  simp [QuadraticAlgebra.basis, QuadraticAlgebra.linearEquivTuple]
  ring

theorem discr_d_2_or_3 (hd : d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4]) : discr K = 4 * d := by
  letI : IsIntegralClosure R ℤ K := d_2_or_3 hd
  let e := IsIntegralClosure.equiv ℤ R K (𝓞 K)
  let b := (QuadraticAlgebra.basis d 0).map e.toLinearEquiv
  calc
    discr K = Algebra.discr ℤ b := (NumberField.discr_eq_discr K b).symm
    _ = Algebra.discr ℤ (QuadraticAlgebra.basis d 0) := by
      convert (Algebra.discr_eq_discr_of_algEquiv (QuadraticAlgebra.basis d 0) e).symm using 1
      change Algebra.discr ℤ (fun i => e ((QuadraticAlgebra.basis d 0) i)) = _
      rfl
    _ = 4 * d := by simpa using quadratic_discr d 0

theorem discr_d_1 [Fact (d ≡ 1 [ZMOD 4])] : discr K = d := by
  letI : IsIntegralClosure (QuadraticAlgebra ℤ ((d - 1) / 4) 1) ℤ K := d_1
  let f := IsIntegralClosure.equiv ℤ (QuadraticAlgebra ℤ ((d - 1) / 4) 1) K (𝓞 K)
  let b := (QuadraticAlgebra.basis ((d - 1) / 4) 1).map f.toLinearEquiv
  calc
    discr K = Algebra.discr ℤ b := (NumberField.discr_eq_discr K b).symm
    _ = Algebra.discr ℤ (QuadraticAlgebra.basis ((d - 1) / 4) 1) := by
      convert (Algebra.discr_eq_discr_of_algEquiv (QuadraticAlgebra.basis ((d - 1) / 4) 1) f).symm
        using 1
      change Algebra.discr ℤ (fun i => f ((QuadraticAlgebra.basis ((d - 1) / 4) 1) i)) = _
      rfl
    _ = 1 ^ 2 + 4 * ((d - 1) / 4) := quadratic_discr _ _
    _ = d := by
      rw [e_spec]
      ring

end discriminant

end QuadraticInteger
