import IsoProof.IntegralsBridge
import IsingBulk.HT22.Physical.ExteriorIdentity
import IsingBulk.HT.Final.OriginDecay

/-! Quantitative origin control. The old removable-singularity construction
only supplied boundedness. Here each resolvent factor is retained, so the
complete odd tail beginning with N=3 is O(|s|²) after the 1/s normalization.
-/
namespace IsoProof
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final
open scoped BigOperators

private theorem quarter_resolvent_product_power_decay (N : ℕ) {t : ℂ}
    (ht : 16 < ‖t‖) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖=(1/4 : ℝ)) (hy : ∀ i, ‖y i‖=(1/4 : ℝ)) :
    ‖∏ i, (dispersion (x i) (y i) t)⁻¹‖ ≤ (2/‖t‖)^N := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin N, 2/‖t‖ := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      have hd := farExterior_dispersion_half_norm ht
        (x := x i) (y := y i) (by rw [hx i]; norm_num) (by rw [hy i]; norm_num)
      rw [norm_inv]
      simpa only [inv_div] using inv_anti₀ (by linarith : 0 < ‖t‖/2) hd
    _ = _ := by simp [div_pow]

/-- Full Nth-order decay, stronger than the uniform O(1/t) bound previously
used only for existence of the removable extension. -/
theorem standardFormFactor_quarter_power_decay (N : ℕ) (hN : 0 < N)
    {t : ℂ} (ht : 16 < ‖t‖) :
    ‖standardFormFactor N (1/4) t‖ ≤ 16*(2/‖t‖)^N/(N.factorial : ℝ) := by
  have hb := multiCircleIntegral_norm_le N (r := 1/4) (by norm_num)
    (fun y => multiCircleIntegral (1/4) N (fun x => standardDensity t x y)) (by
      intro y hy
      apply multiCircleIntegral_norm_le N (by norm_num)
      intro x hx
      exact standardDensity_quarter_norm_bound_of_resolvent_product hN t x y hx hy
        (quarter_resolvent_product_power_decay N ht x y hx hy))
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg N.factorial))
  have he : (1/4 : ℝ)^N*((1/4 : ℝ)^N*((16*(16 : ℝ)^N)*(2/‖t‖)^N)) =
      16*(2/‖t‖)^N := by
    calc
      _ = 16*(((1/4 : ℝ)*(1/4)*16)^N)*(2/‖t‖)^N := by
        simp only [mul_pow]
        ring
      _ = _ := by norm_num
  rw [he] at hh
  simpa only [standardFormFactor, norm_mul, norm_inv, Complex.norm_natCast,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh

theorem oddCoefficient_power_decay (n : ℕ) {t : ℂ} (ht : 16 < ‖t‖) :
    ‖IsingBulk.HT22.Physical.coefficient (2*n+1) t‖ ≤
      16*(2/‖t‖)^(2*n+1)/((2*n+1).factorial : ℝ) := by
  rw [IsingBulk.HT22.Physical.coefficient_odd_eq_existing_exterior n (show 1 < ‖t‖ by linarith),
    exteriorOddTerm_eq_quarter_far n ht]
  exact standardFormFactor_quarter_power_decay _ (by omega) ht

def originTailMajorant (n : ℕ) : ℝ :=
  16*2^(2*n+3)/((2*n+3).factorial : ℝ)

theorem originTailMajorant_summable : Summable originTailMajorant := by
  have hi : Function.Injective (fun n : ℕ => 2*n+3) := by
    intro n m h
    change 2*n+3 = 2*m+3 at h
    omega
  have h := (Real.summable_pow_div_factorial 2).comp_injective hi
  apply (h.mul_left 16).congr
  intro n
  change 16*(2^(2*n+3)/((2*n+3).factorial : ℝ)) = _
  unfold originTailMajorant
  ring

/-- A summable bound retaining the exact vanishing order after cancellation
of the high-temperature prefactor's simple pole. -/
theorem scaled_odd_tail_term_bound (n : ℕ) {s : ℂ}
    (hs0 : s ≠ 0) (hs : ‖s‖ < 1/16) :
    ‖s⁻¹ * IsingBulk.HT22.Physical.coefficient (2*n+3) s⁻¹‖ ≤
      originTailMajorant n * ‖s‖^2 := by
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hi : 16 < ‖s⁻¹‖ := by
    rw [norm_inv, inv_eq_one_div]
    exact (lt_div_iff₀ hsn).mpr (by linarith)
  have hb := oddCoefficient_power_decay (n+1) hi
  rw [show 2*(n+1)+1 = 2*n+3 by omega, norm_inv, div_inv_eq_mul] at hb
  rw [norm_mul, norm_inv]
  have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg s))
  calc
    _ ≤ ‖s‖⁻¹*(16*(2*‖s‖)^(2*n+3)/((2*n+3).factorial : ℝ)) := hm
    _ = originTailMajorant n * (‖s‖^(2*n)*‖s‖^2) := by
      unfold originTailMajorant
      rw [mul_pow]
      have he : ‖s‖^(2*n+3) = ‖s‖^(2*n)*‖s‖^2*‖s‖ := by
        rw [show 2*n+3 = (2*n+2)+1 by omega, pow_succ, pow_add]
      rw [he]
      field_simp [hsn.ne']
    _ ≤ originTailMajorant n * ‖s‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (by unfold originTailMajorant; positivity)
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (by linarith))

/-- The full N>=3 odd tail, without truncation. -/
theorem scaled_odd_tail_bound {s : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1/16) :
    ‖∑' n : ℕ, s⁻¹ * IsingBulk.HT22.Physical.coefficient (2*n+3) s⁻¹‖ ≤
      (∑' n : ℕ, originTailMajorant n) * ‖s‖^2 := by
  have hmaj := originTailMajorant_summable.mul_right (‖s‖^2)
  have habs := hmaj.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => scaled_odd_tail_term_bound n hs0 hs)
  exact (norm_tsum_le_tsum_norm habs).trans
    ((Summable.tsum_le_tsum (fun n => scaled_odd_tail_term_bound n hs0 hs) habs hmaj).trans_eq
      (tsum_mul_right))

end
end IsoProof
