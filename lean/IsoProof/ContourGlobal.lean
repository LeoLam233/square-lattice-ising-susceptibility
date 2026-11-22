import IsoProof.ContourInterior
import IsoProof.ContourEndpoint

/-! Gluing the quantitative compact-interior, square-root endpoint and
strict exterior estimates into the full literal common-contour inequality. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set Filter
set_option maxHeartbeats 1000000

theorem exterior_argument_gt_one {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : r ∈ Icc (-Real.pi) Real.pi) (hb : cutHalfWidth x < |r|) :
    1 < x-Real.cos r := by
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (cutHalfWidth_range hx hx2).1.le (abs_le.mpr hr) hb
  rw [Real.cos_abs,cutHalfWidth,Real.cos_arccos (by linarith) (by linarith)] at hcos
  linarith

theorem exterior_common_phase_gain {x d η : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hdb : d < cutHalfWidth x) (hη : 0 < η) :
    ∃ ε > 0, ∀ v ∈ Icc (0 : ℝ) ε, ∀ y ∈ Icc (0 : ℝ) ε,
      ∀ r ∈ Icc (-Real.pi) Real.pi, cutHalfWidth x+η ≤ |r| →
      ∀ c ∈ Icc (-d) d, y+v*(r-c)^2 ≤ commonPhaseGain x v y r c := by
  let R := Icc (-Real.pi) Real.pi ∩ {r : ℝ | cutHalfWidth x+η ≤ |r|}
  have hR : IsCompact R := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  let S := R ×ˢ Icc (-d) d
  have hS : IsCompact S := hR.prod isCompact_Icc
  have hf := contourDisplacement_continuous (cutHalfWidth_range hx hx2).1.le
    (cutHalfWidth_range hx hx2).2
  have he : ∀ᶠ vy : ℝ × ℝ in 𝓝 (0,0), ∀ p ∈ S,
      0 < commonPhaseGain x vy.1 vy.2 p.1 p.2-vy.2-vy.1*(p.1-p.2)^2 := by
    apply hS.eventually_forall_of_forall_eventually
    intro p hp
    have hW : 1 < x-Real.cos p.1 := exterior_argument_gt_one hx hx2 hp.1.1
      (by have hh : cutHalfWidth x+η ≤ |p.1| := hp.1.2; linarith)
    have hdom : graphDispersion x (cutHalfWidth x) 0 0 p.1 p.2 ∈ contourRootDomain := by
      simpa [graphDispersion,scalarGraph,← Complex.ofReal_cos,← Complex.ofReal_sub] using
        real_mem_contourRootDomain (by linarith : -1 < x-Real.cos p.1) (ne_of_gt hW)
    have hph : ContinuousAt
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          continuedPhase (graphDispersion x (cutHalfWidth x) z.1.1 z.1.2 z.2.1 z.2.2)) ((0,0),p) := by
      have hc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          graphDispersion x (cutHalfWidth x) z.1.1 z.1.2 z.2.1 z.2.2) := by
        unfold graphDispersion scalarGraph
        fun_prop
      exact (continuedPhase_analyticAt hdom).continuousAt.comp (x := ((0,0),p))
        (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          graphDispersion x (cutHalfWidth x) z.1.1 z.1.2 z.2.1 z.2.2) hc.continuousAt
    have hcb : |p.2| < cutHalfWidth x := (abs_le.mpr hp.2).trans_lt hdb
    obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hcb
    have hsl := (cutPhase_second_hasDerivAt h0 h1).continuousAt
    have hslc : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) => deriv (cutPhase x) z.2.2)
        ((0,0),p) := hsl.comp (x := ((0,0),p)) (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.2)
          (continuous_snd.comp continuous_snd).continuousAt
    have hc : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        commonPhaseGain x z.1.1 z.1.2 z.2.1 z.2.2-z.1.2-z.1.1*(z.2.1-z.2.2)^2) ((0,0),p) := by
      simp_rw [commonPhaseGain_eq]
      have hi := Complex.continuous_im.continuousAt.comp hph
      fun_prop
    have hbase : 0 < commonPhaseGain x 0 0 p.1 p.2 := by
      have hpneg := continuedPhase_exterior_im_neg hW
      simpa [commonPhaseGain,scalarGraph,graphDispersion,← Complex.ofReal_cos,
        ← Complex.ofReal_sub] using neg_pos.mpr hpneg
    exact continuousAt_const.eventually_lt hc (by simpa using hbase)
  obtain ⟨ε,hε,hprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε/2,by positivity,?_⟩
  intro v hv y hy r hr hout c hc
  have hdist : dist (v,y) ((0 : ℝ),0) < ε := by
    simp only [Prod.dist_eq,Real.dist_eq,sub_zero,abs_of_nonneg hv.1,abs_of_nonneg hy.1]
    exact max_lt (by linarith [hv.2]) (by linarith [hy.2])
  have h := hprop (y := (v,y)) hdist (r,c) ⟨⟨hr,hout⟩,hc⟩
  linarith

/-- Equation (5) for the actual full piecewise-linear common graph.
The constants are constructed, and no phase-bound or contour-bound
hypothesis occurs in the statement. -/
theorem common_phase_gain {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ a > 0, ∃ ε > 0, ∀ v, 0 < v → v ≤ ε → ∀ y ∈ Icc (0 : ℝ) ε,
      ∀ r ∈ Icc (-Real.pi) Real.pi, ∀ c ∈ Icc (-d) d,
        a*(y+v*(r-c)^2) ≤ commonPhaseGain x v y r c := by
  obtain ⟨η,hη,εp,hεp,hp⟩ := endpoint_common_phase_gain hx hx2 hd hdb
  let s := max d (cutHalfWidth x-η/2)
  have hs : 0 ≤ s := hd.trans (le_max_left _ _)
  have hsb : s < cutHalfWidth x := max_lt hdb (by linarith)
  obtain ⟨εi,hεi,hi⟩ := interior_phase_gain hx hx2 hs hsb
  obtain ⟨εo,hεo,ho⟩ := exterior_common_phase_gain hx hx2 hdb (by positivity : 0 < η/2)
  let a := min (x*(1-x^2/4)/2) (1/2 : ℝ)
  have hapos : 0 < a := by
    apply lt_min
    · have : 0 < 1-x^2/4 := by nlinarith
      positivity
    · norm_num
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨a,hapos,min εp (min εi εo),lt_min hεp (lt_min hεi hεo),?_⟩
  intro v hv hvε y hy r hr c hc
  have hvp : v ≤ εp := hvε.trans (min_le_left _ _)
  have hyp : y ≤ εp := hy.2.trans (min_le_left _ _)
  have hvi : v ≤ εi := hvε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hyi : y ≤ εi := hy.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hvo : v ≤ εo := hvε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hyo : y ≤ εo := hy.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnonneg : 0 ≤ y+v*(r-c)^2 := add_nonneg hy.1 (mul_nonneg hv.le (sq_nonneg _))
  by_cases hrs : |r| ≤ s
  · have hcs : |c| ≤ s := (abs_le.mpr hc).trans (le_max_left _ _)
    have h := hi v ⟨hv.le,hvi⟩ y ⟨hy.1,hyi⟩ r (abs_le.mp hrs) c (abs_le.mp hcs)
    have hf : contourDisplacement (cutHalfWidth x) r=r :=
      contourDisplacement_interior (hrs.trans hsb.le)
    change _ ≤ _ at h
    unfold commonPhaseGain graphDispersion scalarGraph
    rw [hf]
    have haI := mul_le_mul_of_nonneg_right (min_le_left (x*(1-x^2/4)/2) (1/2 : ℝ))
      (mul_nonneg hv.le (sq_nonneg (r-c)))
    have haY := mul_le_mul_of_nonneg_right (min_le_right (x*(1-x^2/4)/2) (1/2 : ℝ)) hy.1
    nlinarith
  · by_cases hnear : |r-cutHalfWidth x| < η ∨ |r+cutHalfWidth x| < η
    · exact (mul_le_of_le_one_left hnonneg ha1).trans (hp r hr hnear c hc v hv hvp y ⟨hy.1,hyp⟩)
    · have hout : cutHalfWidth x+η/2 ≤ |r| := by
        by_contra hout
        have hUpper : |r| < cutHalfWidth x+η/2 := lt_of_not_ge hout
        have hLower : cutHalfWidth x-η/2 < |r| :=
          (le_max_right d _).trans_lt (lt_of_not_ge hrs)
        apply hnear
        by_cases hr0 : 0 ≤ r
        · left
          rw [abs_of_nonneg hr0] at hUpper hLower
          exact abs_lt.mpr ⟨by linarith,by linarith⟩
        · right
          rw [abs_of_neg (lt_of_not_ge hr0)] at hUpper hLower
          exact abs_lt.mpr ⟨by linarith,by linarith⟩
      exact (mul_le_of_le_one_left hnonneg ha1).trans
        (ho v ⟨hv.le,hvo⟩ y ⟨hy.1,hyo⟩ r hr hout c hc)

end
end IsoProof
