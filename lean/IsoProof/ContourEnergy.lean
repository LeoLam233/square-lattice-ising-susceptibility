import IsoProof.ContourBounds
import IsoProof.ContourPhase
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform phase control on the actual complex energy disk of the fixed
common graph. This is the quantitative shrinking-disk step before Cauchy. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set
set_option backward.isDefEq.respectTransparency false

theorem common_graph_phase_energy_lipschitz {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε → ∃ ρ > 0, ∃ D > 0,
      ∀ y ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (-Real.pi) Real.pi, ∀ c ∈ Icc (-d) d,
      ∀ e : ℂ, ‖e‖ ≤ ρ →
      ‖continuedPhase (graphDispersion x (cutHalfWidth x) v y r c+e)-
        continuedPhase (graphDispersion x (cutHalfWidth x) v y r c)‖ ≤ D*‖e‖ := by
  obtain ⟨ε,hε,hbounds⟩ := common_graph_scalar_bounds hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε
  obtain ⟨ρ,hρ,M,hM,δ,hδ,hDom,_⟩ := hbounds v hv hvε
  let T := Metric.closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d
  let W := fun t : ℂ × (ℝ × (ℝ × ℝ)) =>
    commonGraphEnergy x t.1 t.2-Complex.cos (commonGraphAngle x v t.2)
  have hT : IsCompact T := (isCompact_closedBall (0 : ℂ) ρ).prod
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hf := contourDisplacement_continuous (cutHalfWidth_range hx hx2).1.le
    (cutHalfWidth_range hx hx2).2
  have hW : Continuous W := by
    unfold W commonGraphEnergy commonGraphAngle scalarGraph
    fun_prop
  have hphase : ContinuousOn (fun t => continuedPhase (W t)) T := by
    intro t ht
    exact (continuedPhase_analyticAt (hDom t ht)).continuousAt.comp_continuousWithinAt
      (f := W) hW.continuousWithinAt
  have hsin : ContinuousOn (fun t => Complex.sin (continuedPhase (W t))) T :=
    Complex.continuous_sin.comp_continuousOn hphase
  have hinv := hsin.inv₀ (fun t ht => continuedPhase_sin_ne_zero (hDom t ht))
  obtain ⟨D0,hD0⟩ := hT.bddAbove_image hinv.norm
  let D := max 1 D0
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨ρ,hρ,D,hD,?_⟩
  intro y hy r hr c hc e he
  let W0 := graphDispersion x (cutHalfWidth x) v y r c
  have hdom (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) ρ) : W0+z ∈ contourRootDomain := by
    have h := hDom (z,(y,(r,c))) ⟨hz,hy,hr,hc⟩
    convert h using 1
    dsimp [W0,graphDispersion,commonGraphEnergy,commonGraphAngle]
    ring
  have hdF (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) ρ) :
      HasDerivAt (fun z => continuedPhase (W0+z))
        (-1/Complex.sin (continuedPhase (W0+z))) z := by
    simpa only [Function.comp_def,mul_one] using!
      (continuedPhase_hasDerivAt (hdom z hz)).comp z ((hasDerivAt_id z).const_add W0)
  have hbound (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) ρ) :
      ‖deriv (fun z => continuedPhase (W0+z)) z‖ ≤ D := by
    rw [(hdF z hz).deriv]
    have h := (hD0 (mem_image_of_mem _ (show (z,(y,(r,c))) ∈ T from ⟨hz,hy,hr,hc⟩))).trans
      (le_max_right 1 D0)
    have heq : W (z,(y,(r,c))) = W0+z := by
      dsimp [W,W0,commonGraphEnergy,commonGraphAngle,graphDispersion]
      ring
    simpa only [Pi.inv_apply,heq,norm_div,norm_neg,norm_one,one_div,norm_inv,D] using h
  have h := (convex_closedBall (0 : ℂ) ρ).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hdF z hz).differentiableAt) hbound
    (by simpa using hρ.le : (0 : ℂ) ∈ Metric.closedBall 0 ρ)
    (by simpa using he : e ∈ Metric.closedBall 0 ρ)
  simpa only [add_zero,sub_zero] using h

/-- The energy change of each actual exponential site factor is bounded
independently of A on the shrinking Cauchy disk. -/
theorem phase_shrinking_disk_bound {A : ℕ} {D δ : ℝ} (hD : 0 ≤ D)
    (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {e : ℂ}
    (he : ‖e‖ ≤ δ/(1+(A : ℝ))) {W : ℂ}
    (hphase : ‖continuedPhase (W+e)-continuedPhase W‖ ≤ D*‖e‖) :
    (A : ℝ)*((continuedPhase (W+e)).im-(continuedPhase W).im) ≤ D := by
  have hA : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  have hA1 : 0 < 1+(A : ℝ) := by positivity
  have hAi : (A : ℝ)*‖e‖ ≤ 1 := by
    have h := (le_div_iff₀ hA1).mp he
    have h' := norm_nonneg e
    nlinarith
  have him : (continuedPhase (W+e)).im-(continuedPhase W).im ≤ D*‖e‖ := by
    calc
      _ ≤ ‖continuedPhase (W+e)-continuedPhase W‖ := by
        simpa only [Complex.sub_im] using Complex.im_le_norm (continuedPhase (W+e)-continuedPhase W)
      _ ≤ _ := hphase
  have h := mul_le_mul_of_nonneg_left him hA
  have h' := mul_le_mul_of_nonneg_left hAi hD
  nlinarith

end
end IsoProof
