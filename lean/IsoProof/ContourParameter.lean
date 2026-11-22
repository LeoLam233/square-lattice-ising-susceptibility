import IsoProof.ContourInterior
import IsoProof.ContourGlobal

/-! Joint parameter formulas used to stabilize a fixed common graph under
a small real change of the cut point. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def phaseAngleSecond (E q : ℂ) : ℂ :=
  -Complex.cos q/Complex.sin (continuedPhase (E-Complex.cos q))-
    (Complex.sin q)^2*Complex.cos (continuedPhase (E-Complex.cos q))/
      (Complex.sin (continuedPhase (E-Complex.cos q)))^3

theorem phaseAngleFirst_hasDerivAt {E q : ℂ}
    (hD : E-Complex.cos q ∈ contourRootDomain) :
    HasDerivAt (fun q => -Complex.sin q/Complex.sin (continuedPhase (E-Complex.cos q)))
      (phaseAngleSecond E q) q := by
  have hφ := continuedPhase_angle_hasDerivAt hD
  have hsin := (Complex.hasDerivAt_sin (continuedPhase (E-Complex.cos q))).comp q hφ
  have h := (Complex.hasDerivAt_sin q).neg.div hsin (continuedPhase_sin_ne_zero hD)
  convert h using 1
  · rfl
  · unfold phaseAngleSecond
    simp only [Function.comp_def,Pi.neg_apply]
    field_simp [continuedPhase_sin_ne_zero hD]

theorem anglePhase_second_eq {x : ℝ} {q : ℂ}
    (hD : (x : ℂ)-Complex.cos q ∈ contourRootDomain) :
    deriv (deriv (anglePhase x)) q = phaseAngleSecond (x : ℂ) q := by
  have hneigh : ∀ᶠ z : ℂ in 𝓝 q, (x : ℂ)-Complex.cos z ∈ contourRootDomain :=
    ((contourRootDomain_isOpen.preimage (by fun_prop)).mem_nhds hD)
  have he : deriv (anglePhase x) =ᶠ[𝓝 q]
      fun z => -Complex.sin z/Complex.sin (continuedPhase ((x : ℂ)-Complex.cos z)) := by
    filter_upwards [hneigh] with z hz
    exact (continuedPhase_angle_hasDerivAt hz).deriv
  rw [he.deriv_eq]
  exact (phaseAngleFirst_hasDerivAt hD).deriv

theorem phaseAngleSecond_continuousAt {p : ℂ × ℂ}
    (hD : p.1-Complex.cos p.2 ∈ contourRootDomain) :
    ContinuousAt (fun z : ℂ × ℂ => phaseAngleSecond z.1 z.2) p := by
  have hW : Continuous (fun z : ℂ × ℂ => z.1-Complex.cos z.2) := by fun_prop
  have hφ := (continuedPhase_analyticAt hD).continuousAt.comp (f := fun z : ℂ × ℂ =>
    z.1-Complex.cos z.2) hW.continuousAt
  have hs := Complex.continuous_sin.continuousAt.comp hφ
  have hc := Complex.continuous_cos.continuousAt.comp hφ
  have hsq : ContinuousAt (fun z : ℂ × ℂ => Complex.sin z.2) p := by fun_prop
  have hcq : ContinuousAt (fun z : ℂ × ℂ => Complex.cos z.2) p := by fun_prop
  exact (hcq.neg.div hs (continuedPhase_sin_ne_zero hD)).sub
    (((hsq.pow 2).mul hc).div (hs.pow 3) (pow_ne_zero _ (continuedPhase_sin_ne_zero hD)))

theorem phaseAngleSecond_real {x c : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hc : |c| < cutHalfWidth x) :
    phaseAngleSecond (x : ℂ) (c : ℂ) = ((deriv (deriv (cutPhase x)) c : ℝ) : ℂ) := by
  rw [← anglePhase_second_eq (real_angle_domain hx hx2 hc),anglePhase_second_real hx hx2 hc]
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hc
  rw [(cutPhase_second_hasDerivAt h0 h1).deriv]

/-- The real-angle phase slope is jointly continuous in the cut point and
the real center, on the strict oscillatory region. -/
theorem cutPhase_slope_joint_continuousAt {x c : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hc : |c| < cutHalfWidth x) :
    ContinuousAt (fun p : ℝ × ℝ => deriv (cutPhase p.1) p.2) (x,c) := by
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hc
  have hW : Continuous (fun p : ℝ × ℝ => p.1-Real.cos p.2) := by fun_prop
  have hneigh : ∀ᶠ p : ℝ × ℝ in 𝓝 (x,c), -1 < p.1-Real.cos p.2 ∧ p.1-Real.cos p.2 < 1 :=
    (isOpen_Ioo.preimage hW).mem_nhds ⟨h0,h1⟩
  have he : (fun p : ℝ × ℝ => deriv (cutPhase p.1) p.2) =ᶠ[𝓝 (x,c)]
      (fun p => -Real.sin p.2/Real.sin (cutPhase p.1 p.2)) := by
    filter_upwards [hneigh] with p hp
    exact (cutPhase_hasDerivAt hp.1 hp.2).deriv
  apply ContinuousAt.congr_of_eventuallyEq _ he
  have hg : Continuous (fun p : ℝ × ℝ => cutPhase p.1 p.2) := by
    unfold cutPhase
    fun_prop
  exact ((Real.continuous_sin.comp continuous_snd).continuousAt.neg).div
    (Real.continuous_sin.comp hg).continuousAt (cutPhase_sin_pos h0 h1).ne'

end
end IsoProof
