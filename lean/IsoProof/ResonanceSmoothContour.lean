import IsoProof.ResonanceFiniteGeometry
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.Instances.AddCircle.Defs

/-! A genuine smooth periodic perturbation of the literal common contour.
For finite particle order its use is justified by open compact pole gaps;
no identity of the nonsmooth Jacobian is assumed.  Convolution preserves
periodicity exactly, so the coupled constrained cylinder faces still cancel. -/
namespace IsoProof
noncomputable section
open Complex Filter Set Metric MeasureTheory Function
open scoped Topology ContDiff Convolution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

local instance : Fact (0<(2*Real.pi:ℝ)) := ⟨by positivity⟩

def periodicContourDisplacement (b r : ℝ) : ℝ :=
  AddCircle.liftIco (2*Real.pi) (-Real.pi) (contourDisplacement b) (r : AddCircle (2*Real.pi))

theorem periodicContourDisplacement_periodic (b : ℝ) :
    Function.Periodic (periodicContourDisplacement b) (2*Real.pi) := by
  intro r
  simp only [periodicContourDisplacement,AddCircle.coe_add_period]

theorem periodicContourDisplacement_continuous {b : ℝ} (hb : 0≤b) (hbpi : b<Real.pi) :
    Continuous (periodicContourDisplacement b) := by
  have he : contourDisplacement b (-Real.pi)=contourDisplacement b (-Real.pi+2*Real.pi) := by
    rw [show -Real.pi+2*Real.pi=Real.pi by ring]
    exact (contourDisplacement_endpoints hbpi).2.trans (contourDisplacement_endpoints hbpi).1.symm
  have hc := AddCircle.liftIco_continuous he (contourDisplacement_continuous hb hbpi).continuousOn
  exact hc.comp (show Continuous (fun r : ℝ=>(r : AddCircle (2*Real.pi))) from by fun_prop)

theorem periodicContourDisplacement_agrees {b r : ℝ} (hbpi : b<Real.pi)
    (hr : r∈Icc (-Real.pi) Real.pi) : periodicContourDisplacement b r=contourDisplacement b r := by
  by_cases htop : r<Real.pi
  · exact AddCircle.liftIco_coe_apply (by
      constructor
      · exact hr.1
      · linarith)
  · have heq : r=Real.pi := le_antisymm hr.2 (le_of_not_gt htop)
    subst r
    have he : ((Real.pi:ℝ):AddCircle (2*Real.pi))=((-Real.pi:ℝ):AddCircle (2*Real.pi)) := by
      convert AddCircle.coe_add_period (2*Real.pi) (-Real.pi) using 1
      congr 1
      ring
    unfold periodicContourDisplacement
    rw [he,AddCircle.liftIco_coe_apply (by
      constructor
      · exact le_rfl
      · linarith [Real.pi_pos])]
    exact (contourDisplacement_endpoints hbpi).2.trans (contourDisplacement_endpoints hbpi).1.symm

/-- Uniform approximation on a specified compact real set, with smoothness
and exact periodicity produced simultaneously by one compact bump convolution. -/
theorem periodic_smooth_approx_on_compact {f : ℝ→ℝ} (hf : Continuous f)
    {T : ℝ} (hp : Function.Periodic f T) {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0<ε) :
    ∃g : ℝ→ℝ,ContDiff ℝ ∞ g ∧ Function.Periodic g T ∧
      ∀x∈K,dist (g x) (f x)<ε := by
  have hU : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ,hδ,hδprop⟩ := Metric.uniformContinuousOn_iff.mp hU (ε/2) (half_pos hε)
  let ρ := min 1 δ
  have hρ : 0<ρ := lt_min one_pos hδ
  let φ : ContDiffBump (0:ℝ) := ⟨ρ/2,ρ,half_pos hρ,half_lt_self hρ⟩
  let g : ℝ→ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f
  have hg : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf.locallyIntegrable
  refine ⟨g,hg,?_,?_⟩
  · intro x
    simp only [g,convolution_def]
    congr 1
    funext t
    rw [show x+T-t=x-t+T by ring,hp (x-t)]
  · intro x hx
    have hbound : dist (g x) (f x)≤ε/2 := by
      apply φ.dist_normed_convolution_le hf.aestronglyMeasurable
      intro y hy
      have hyd : dist y x<min 1 δ := hy
      exact (hδprop y (mem_cthickening_of_dist_le _ x _ _ hx (lt_min_iff.mp hyd).1.le)
        x (self_subset_cthickening _ hx) (lt_min_iff.mp hyd).2).le
    exact hbound.trans_lt (half_lt_self hε)

/-- The actual piecewise linear displacement has arbitrarily accurate
smooth periodic representatives on each compact set. -/
theorem contourDisplacement_smooth_periodic_approx {b : ℝ} (hb : 0≤b) (hbpi : b<Real.pi)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0<ε) :
    ∃g : ℝ→ℝ,ContDiff ℝ ∞ g ∧ Function.Periodic g (2*Real.pi) ∧
      ∀x∈K,dist (g x) (periodicContourDisplacement b x)<ε :=
  periodic_smooth_approx_on_compact (periodicContourDisplacement_continuous hb hbpi)
    (periodicContourDisplacement_periodic b) hK hε

end
end IsoProof
