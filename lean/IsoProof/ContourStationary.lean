import IsoProof.ContourGlobal
import Mathlib.Topology.Order.IntermediateValue

/-! Stationary centers and the exact conversion from the phase inequality
to the modulus of the actual exponential site factors. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set

def stationaryHalfWidth (x : ℝ) : ℝ := Real.arccos (x/2)

theorem stationaryHalfWidth_range {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    0 < stationaryHalfWidth x ∧ stationaryHalfWidth x < cutHalfWidth x := by
  constructor
  · exact Real.arccos_pos.mpr (by linarith)
  · exact Real.arccos_lt_arccos (by linarith) (by linarith) (by linarith)

theorem cutPhase_at_negative_stationary {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    cutPhase x (-stationaryHalfWidth x)=stationaryHalfWidth x := by
  unfold cutPhase stationaryHalfWidth
  rw [Real.cos_neg,Real.cos_arccos (by linarith) (by linarith)]
  congr 1
  ring

theorem cutPhase_slope_at_stationary {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    deriv (cutPhase x) (-stationaryHalfWidth x)=1 ∧ deriv (cutPhase x) 0=0 := by
  obtain ⟨hd,hdb⟩ := stationaryHalfWidth_range hx hx2
  have hdpi : stationaryHalfWidth x < Real.pi := hdb.trans (cutHalfWidth_range hx hx2).2
  have hsin : Real.sin (stationaryHalfWidth x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hd hdpi).ne'
  have harg := cutPhase_argument_range hx hx2
    (show |-stationaryHalfWidth x| < cutHalfWidth x by simpa only [abs_neg,abs_of_pos hd] using hdb)
  have harg0 := cutPhase_argument_range hx hx2
    (show |(0 : ℝ)| < cutHalfWidth x by simpa using (cutHalfWidth_range hx hx2).1)
  constructor
  · rw [(cutPhase_hasDerivAt harg.1 harg.2).deriv,
      cutPhase_at_negative_stationary hx hx2,Real.sin_neg,neg_neg,div_self hsin]
  · simp [(cutPhase_hasDerivAt harg0.1 harg0.2).deriv]

theorem stationary_center_exists {x ρ : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ∃ c ∈ Icc (-stationaryHalfWidth x) 0, deriv (cutPhase x) c=ρ := by
  obtain ⟨hd,hdb⟩ := stationaryHalfWidth_range hx hx2
  have hc := (center_slope_continuousOn hx hx2 hdb).mono
    (show Icc (-stationaryHalfWidth x) 0 ⊆ Icc (-stationaryHalfWidth x) (stationaryHalfWidth x) by
      intro c hc
      exact ⟨hc.1,hc.2.trans hd.le⟩)
  have himage := intermediate_value_Icc' (show -stationaryHalfWidth x ≤ 0 by linarith) hc
  obtain ⟨hleft,hright⟩ := cutPhase_slope_at_stationary hx hx2
  rw [hleft,hright] at himage
  exact himage hρ

theorem site_exponential_norm (A B : ℕ) (W q : ℂ) :
    ‖(continuedTransferRoot W)^A*(Complex.exp (Complex.I*q))^B‖ =
      Real.exp ((A : ℝ)*(continuedPhase W).im-(B : ℝ)*q.im) := by
  have he : (continuedTransferRoot W)^A*(Complex.exp (Complex.I*q))^B =
      Complex.exp (-Complex.I*((A : ℂ)*continuedPhase W-(B : ℂ)*q)) := by
    rw [← continuedPhase_exp W,← Complex.exp_nat_mul,← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    ring
  rw [he,Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

/-- At the stationary slope, (5) gives the Gaussian in each actual site
factor. This retains the complete exponent A and the true angular power. -/
theorem common_graph_site_exponential_bound {x d a ε : ℝ} (ha : 0 ≤ a)
    (hphase : ∀ v, 0 < v → v ≤ ε → ∀ y ∈ Icc (0 : ℝ) ε,
      ∀ r ∈ Icc (-Real.pi) Real.pi, ∀ c ∈ Icc (-d) d,
      a*(y+v*(r-c)^2) ≤ commonPhaseGain x v y r c)
    {A B : ℕ} (hBA : B ≤ A) {c : ℝ} (hc : c ∈ Icc (-d) d)
    (hslope : deriv (cutPhase x) c=(B : ℝ)/(A : ℝ))
    {v y r : ℝ} (hv : 0 < v) (hvε : v ≤ ε) (hy : y ∈ Icc (0 : ℝ) ε)
    (hr : r ∈ Icc (-Real.pi) Real.pi) :
    ‖(continuedTransferRoot (graphDispersion x (cutHalfWidth x) v y r c))^A*
      (Complex.exp (Complex.I*scalarGraph (cutHalfWidth x) v r c))^B‖ ≤
      Real.exp (-(a*v)*(A : ℝ)*(r-c)^2) := by
  rw [site_exponential_norm]
  apply Real.exp_le_exp.mpr
  have hAn : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  have h := mul_le_mul_of_nonneg_left (hphase v hv hvε y hy r hr c hc) hAn
  have hgain : commonPhaseGain x v y r c =
      ((B : ℝ)/(A : ℝ))*(scalarGraph (cutHalfWidth x) v r c).im-
        (continuedPhase (graphDispersion x (cutHalfWidth x) v y r c)).im := by
    simp only [commonPhaseGain,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,hslope]
  rw [hgain] at h
  have hAB : (A : ℝ)*((B : ℝ)/(A : ℝ))=(B : ℝ) := by
    by_cases hA : A=0
    · have hB : B=0 := by omega
      simp [hA,hB]
    · have hAn0 : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      field_simp
  have hay : 0 ≤ a*y := mul_nonneg ha hy.1
  simp only [mul_sub,← mul_assoc,hAB] at h
  nlinarith [mul_nonneg hAn hay]

end
end IsoProof
