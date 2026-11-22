import IsoProof.ContourLocal
import IsoProof.ContourBounds

/-! Local real-energy uniformity of (5) on one fixed geometric graph.
The stationary diagonal is treated by its exact second derivative; its
complement has a compact strict margin. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def fixedPhaseGain (x₀ x v y r c : ℝ) : ℝ :=
  ((((deriv (cutPhase x) c : ℝ) : ℂ)*scalarGraph (cutHalfWidth x₀) v r c)-
    continuedPhase (graphDispersion x (cutHalfWidth x₀) v y r c)).im

theorem fixed_graph_near_diagonal_gain {x₀ d v : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (hdb : d < cutHalfWidth x₀) (hv : 0 < v) :
    ∃ η > 0, ∀ x r c y : ℝ, |x-x₀| < η → |r-c| < η → c∈Icc (-d) d →
      0 ≤ y → y < η →
      (x₀*(1-x₀^2/4)/2)*v*(r-c)^2+y/2 ≤ fixedPhaseGain x₀ x v y r c := by
  obtain ⟨η₀,hη₀,hcontrol⟩ := fixed_graph_diagonal_controls hx hx2 hdb hv
  let η := min η₀ ((cutHalfWidth x₀-d)/2)
  have hη : 0 < η := lt_min hη₀ (by linarith)
  refine ⟨η,hη,?_⟩
  intro x r c y hxx hrc hc hy hyη
  have hxη : |x-x₀| < η₀ := hxx.trans_le (min_le_left _ _)
  have hhη : |r-c| < η₀ := hrc.trans_le (min_le_left _ _)
  have hyη₀ : y < η₀ := hyη.trans_le (min_le_left _ _)
  obtain ⟨hx',hx2',hcb,_hD0,_hcurv0,_hheight0⟩ :=
    hcontrol x 0 0 hxη (by simpa using hη₀) (by simpa using hη₀) c hc
  have hrb : |r| < cutHalfWidth x₀ := by
    have hab : |r| ≤ |r-c|+|c| := by simpa using abs_sub_le r c 0
    have hcabs : |c| ≤ d := abs_le.mpr hc
    have hle := min_le_right η₀ ((cutHalfWidth x₀-d)/2)
    change η ≤ _ at hle
    linarith
  have hq : scalarGraph (cutHalfWidth x₀) v r c =
      (c : ℂ)+(1+Complex.I*(v : ℂ))*((r-c : ℝ) : ℂ) := by
    rw [scalarGraph,contourDisplacement_interior hrb.le]
    push_cast
    ring
  have hzero := stationary_phase_quadratic hx' hx2' hcb
    (κ := v*(x₀*(1-x₀^2/4))) (h := r-c) (v := v) (by
      intro t ht
      have hth : |t*(r-c)| < η₀ := by
        rw [abs_mul,abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hhη
      have h := hcontrol x (t*(r-c)) 0 hxη hth (by simpa using hη₀) c hc
      constructor
      · simpa only [Complex.ofReal_zero,mul_zero,add_zero] using h.2.2.2.1
      · simpa only [Complex.ofReal_zero,mul_zero,add_zero] using h.2.2.2.2.1.le)
  rw [← hq] at hzero
  have hheight := phase_height_gain (x := x) (lam := deriv (cutPhase x) c) (q := scalarGraph (cutHalfWidth x₀) v r c)
    hy (by
      intro t ht
      have htt : |t| < η₀ := by rw [abs_of_nonneg ht.1]; exact ht.2.trans_lt hyη₀
      have h := hcontrol x (r-c) t hxη hhη htt c hc
      dsimp only at h
      rw [← hq] at h
      exact ⟨h.2.2.2.1,h.2.2.2.2.2.le⟩)
  change _ ≤ _ at hzero hheight
  unfold fixedPhaseGain graphDispersion
  nlinarith

theorem fixed_graph_far_diagonal_gain {x₀ d v a η : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (hdb : d < cutHalfWidth x₀)
    (hv : 0 < v) (ha : 0 < a) (hη : 0 < η)
    (hDom : ∀ r∈Icc (-Real.pi) Real.pi, ∀ c∈Icc (-d) d,
      graphDispersion x₀ (cutHalfWidth x₀) v 0 r c ∈ contourRootDomain)
    (hbase : ∀ r∈Icc (-Real.pi) Real.pi, ∀ c∈Icc (-d) d,
      a*v*(r-c)^2 ≤ commonPhaseGain x₀ v 0 r c) :
    ∃ ρ > 0, ∀ x y r c : ℝ, |x-x₀| < ρ → |y| < ρ →
      r∈Icc (-Real.pi) Real.pi → c∈Icc (-d) d → η ≤ |r-c| →
      (a/2)*(y+v*(r-c)^2) ≤ fixedPhaseGain x₀ x v y r c := by
  let K : Set (ℝ × ℝ) := (Icc (-Real.pi) Real.pi ×ˢ Icc (-d) d) ∩
    {p | η ≤ |p.1-p.2|}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (by fun_prop))
  have hf := contourDisplacement_continuous (cutHalfWidth_range hx hx2).1.le
    (cutHalfWidth_range hx hx2).2
  have he : ∀ᶠ xy : ℝ × ℝ in 𝓝 (x₀,0), ∀ p∈K,
      0 < fixedPhaseGain x₀ xy.1 v xy.2 p.1 p.2-(a/2)*(xy.2+v*(p.1-p.2)^2) := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hcb : |p.2| < cutHalfWidth x₀ := (abs_le.mpr hp.1.2).trans_lt hdb
    let W := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      graphDispersion z.1.1 (cutHalfWidth x₀) v z.1.2 z.2.1 z.2.2
    have hW : Continuous W := by unfold W graphDispersion scalarGraph; fun_prop
    have hD : W ((x₀,0),p) ∈ contourRootDomain := hDom p.1 hp.1.1 p.2 hp.1.2
    have hφ := (continuedPhase_analyticAt hD).continuousAt.comp (f := W) hW.continuousAt
    have hsl := (cutPhase_slope_joint_continuousAt hx hx2 hcb).comp
      (x := ((x₀,0),p)) (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1.1,z.2.2)) (by fun_prop)
    have hcont : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        fixedPhaseGain x₀ z.1.1 v z.1.2 z.2.1 z.2.2-(a/2)*(z.1.2+v*(z.2.1-z.2.2)^2))
        ((x₀,0),p) := by
      unfold fixedPhaseGain
      have hph : ContinuousAt (fun z => continuedPhase (graphDispersion z.1.1 (cutHalfWidth x₀) v
          z.1.2 z.2.1 z.2.2)) ((x₀,0),p) := hφ
      have hq : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => scalarGraph (cutHalfWidth x₀) v z.2.1 z.2.2) := by
        unfold scalarGraph
        fun_prop
      have hslc : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          ((deriv (cutPhase z.1.1) z.2.2 : ℝ) : ℂ)) ((x₀,0),p) := by
        simpa only [Function.comp_def] using Complex.continuous_ofReal.continuousAt.comp hsl
      have hm := Complex.continuous_im.continuousAt.comp ((hslc.mul hq.continuousAt).sub hph)
      exact hm.sub (by fun_prop)
    have hpositive : 0 < a*v*(p.1-p.2)^2 := by
      apply mul_pos (mul_pos ha hv)
      exact sq_pos_of_ne_zero (abs_pos.mp (hη.trans_le hp.2))
    have h := hbase p.1 hp.1.1 p.2 hp.1.2
    have heq : fixedPhaseGain x₀ x₀ v 0 p.1 p.2=commonPhaseGain x₀ v 0 p.1 p.2 := rfl
    exact continuousAt_const.eventually_lt hcont (by rw [heq]; nlinarith)
  obtain ⟨ρ,hρ,hρprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ρ,hρ,?_⟩
  intro x y r c hxx hy hr hc hfar
  have hd : dist (x,y) (x₀,(0 : ℝ)) < ρ := by
    simp only [Prod.dist_eq,Real.dist_eq,sub_zero]
    exact max_lt hxx hy
  have h := hρprop (y := (x,y)) hd (r,c) ⟨⟨hr,hc⟩,hfar⟩
  linarith

/-- A fixed protected graph has a uniform quadratic phase estimate on an
open neighborhood of the real cut point. -/
theorem common_phase_gain_locally_uniform {x₀ d : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (hd : 0 ≤ d) (hdb : d < cutHalfWidth x₀) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε → ∃ ρ > 0, ∃ a > 0,
      ∀ x y r c : ℝ, |x-x₀| < ρ → 0 ≤ y → y < ρ →
      r∈Icc (-Real.pi) Real.pi → c∈Icc (-d) d →
      a*(y+v*(r-c)^2) ≤ fixedPhaseGain x₀ x v y r c := by
  obtain ⟨a₀,ha₀,εp,hεp,hbase⟩ := common_phase_gain hx hx2 hd hdb
  obtain ⟨εD,hεD,hD⟩ := common_graph_domain hx hx2 hd hdb
  refine ⟨min εp εD,lt_min hεp hεD,?_⟩
  intro v hv hvε
  have hvp : v ≤ εp := (hvε.trans_le (min_le_left _ _)).le
  have hvD : v < εD := hvε.trans_le (min_le_right _ _)
  obtain ⟨η,hη,hnear⟩ := fixed_graph_near_diagonal_gain hx hx2 hdb hv
  obtain ⟨ρ,hρ,hfar⟩ := fixed_graph_far_diagonal_gain hx hx2 hdb hv ha₀ hη
    (fun r hr c hc => hD v hv hvD r hr c hc 0 le_rfl)
    (fun r hr c hc => by
      have h := hbase v hv hvp 0 ⟨le_rfl,hεp.le⟩ r hr c hc
      simpa only [zero_add,mul_assoc] using h)
  let a := min (a₀/2) (min (x₀*(1-x₀^2/4)/2) (1/2 : ℝ))
  have ha : 0 < a := by
    apply lt_min (by positivity)
    apply lt_min
    · have : 0 < 1-x₀^2/4 := by nlinarith
      positivity
    · norm_num
  refine ⟨min ρ η,lt_min hρ hη,a,ha,?_⟩
  intro x y r c hxx hy hyr hr hc
  have hnonneg : 0 ≤ y+v*(r-c)^2 := by positivity
  by_cases hrc : |r-c| < η
  · have h := hnear x r c y (hxx.trans_le (min_le_right _ _)) hrc hc hy
      (hyr.trans_le (min_le_right _ _))
    have haQ : a ≤ x₀*(1-x₀^2/4)/2 := (min_le_right _ _).trans (min_le_left _ _)
    have haY : a ≤ 1/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hq := mul_le_mul_of_nonneg_right haQ (mul_nonneg hv.le (sq_nonneg (r-c)))
    have hy' := mul_le_mul_of_nonneg_right haY hy
    nlinarith
  · apply (mul_le_mul_of_nonneg_right (min_le_left _ _) hnonneg).trans
    exact hfar x y r c (hxx.trans_le (min_le_left _ _))
      (by rw [abs_of_nonneg hy]; exact hyr.trans_le (min_le_left _ _)) hr hc (le_of_not_gt hrc)

end
end IsoProof
