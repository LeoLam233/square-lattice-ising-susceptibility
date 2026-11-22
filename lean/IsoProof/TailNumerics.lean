import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! Numerical estimates used in equation (6). All constants are arbitrary;
no assertion about a site or particle integral is an assumption here. -/
namespace IsoProof
noncomputable section
open Filter
open scoped Topology

/-- The exact all-parity factorial envelope in the manuscript. -/
def siteOrderEnvelope (C : ℝ) (N : ℕ) : ℝ :=
  (C*(N : ℝ)^(3/4 : ℝ))^N/(N.factorial : ℝ)

/-- Elementary factorial lower bound, from one term of the exponential series. -/
theorem factorial_lower_exponential (N : ℕ) :
    ((N : ℝ)/Real.exp 1)^N ≤ (N.factorial : ℝ) := by
  have ht := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have he : Real.exp (N : ℝ) = (Real.exp 1)^N := by simp
  rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < N.factorial)] at ht
  rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (Real.exp 1)^N)]
  nlinarith

/-- The factor N^(3N/4) is strictly subfactorial for every fixed C. -/
theorem siteOrderEnvelope_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (siteOrderEnvelope C) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(1/4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      tendsto_natCast_atTop_atTop
  have he : ∀ᶠ N : ℕ in atTop, (2*C*Real.exp 1) ≤ (N : ℝ)^(1/4 : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N hroot hN
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ siteOrderEnvelope C N by
    unfold siteOrderEnvelope; positivity)]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ)^(3/4 : ℝ)*(N : ℝ)^(1/4 : ℝ) = N := by
    rw [← Real.rpow_add hN']
    norm_num
  have hm := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hN'.le (3/4 : ℝ))
  rw [hpow] at hm
  have hb : C*(N : ℝ)^(3/4 : ℝ) ≤ (1/2)*((N : ℝ)/Real.exp 1) := by
    have hh : C*(N : ℝ)^(3/4 : ℝ) ≤ ((1/2)*(N : ℝ))/Real.exp 1 :=
      (le_div_iff₀ (Real.exp_pos 1)).mpr (by nlinarith)
    convert hh using 1; ring
  unfold siteOrderEnvelope
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < N.factorial)).mpr
  calc
    _ ≤ ((1/2)*((N : ℝ)/Real.exp 1))^N :=
      pow_le_pow_left₀ (by positivity : 0 ≤ C*(N : ℝ)^(3/4 : ℝ)) hb N
    _ = (1/2 : ℝ)^N*((N : ℝ)/Real.exp 1)^N := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_lower_exponential N) (by positivity)

/-- The strict cutoff in the paper gives a summable spatial exponent,
uniformly for all lower derivative orders. -/
theorem site_tail_exponent {N j k : ℕ} (hj : j ≤ k) (hN : 2*k+4 < N) :
    (j : ℝ)-(N : ℝ)/2 ≤ -(5/2 : ℝ) := by
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hN' : 2*(k : ℝ)+5 ≤ N := by exact_mod_cast (show 2*k+5 ≤ N by omega)
  linarith

/-- Including the exact linear shell growth, the spatial majorant is a
p-series of exponent at most -3/2. -/
theorem shell_majorant_summable :
    Summable (fun A : ℕ => (8 : ℝ)*(A+1)*(1+(A+1 : ℝ))^(-(5/2 : ℝ))) := by
  have hp : Summable (fun A : ℕ => (A : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hp' : Summable (fun A : ℕ => ((A+2 : ℕ) : ℝ)^(-(3/2 : ℝ))) :=
    (summable_nat_add_iff 2).mpr hp
  apply (hp'.mul_left 8).of_nonneg_of_le
  · intro A
    positivity
  · intro A
    have hbase : (0 : ℝ) < 1+(A+1 : ℝ) := by positivity
    have hpow : (1+(A+1 : ℝ))*(1+(A+1 : ℝ))^(-(5/2 : ℝ)) =
        (1+(A+1 : ℝ))^(-(3/2 : ℝ)) := by
      calc
        _ = (1+(A+1 : ℝ))^(1 : ℝ)*(1+(A+1 : ℝ))^(-(5/2 : ℝ)) := by
          rw [Real.rpow_one]
        _ = (1+(A+1 : ℝ))^((1 : ℝ)+(-(5/2 : ℝ))) :=
          (Real.rpow_add hbase _ _).symm
        _ = _ := by norm_num
    have hle := mul_le_mul_of_nonneg_right
      (show (A+1 : ℝ) ≤ 1+(A+1 : ℝ) by linarith)
      (Real.rpow_nonneg hbase.le (-(5/2 : ℝ)))
    rw [hpow] at hle
    have heq : (1+(A+1 : ℝ)) = ((A+2 : ℕ) : ℝ) := by push_cast; ring
    rw [heq] at hle ⊢
    nlinarith

end
end IsoProof
