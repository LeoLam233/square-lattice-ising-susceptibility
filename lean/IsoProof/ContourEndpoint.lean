import IsoProof.ContourPhysical
import IsoProof.ContourProtected
import IsoProof.ContourCompact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual endpoint and exterior phase estimates. In particular the
square-root endpoint gives arbitrarily strong control of Im W by the
positive damping -Im phi; no asymptotic O-symbol is used as a premise. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set Filter
set_option maxHeartbeats 1000000

theorem continuedTransferRoot_one : continuedTransferRoot 1=1 := by
  simp [continuedTransferRoot,downwardSquareRoot]

theorem continuedPhase_one : continuedPhase 1=0 := by
  simp [continuedPhase,continuedTransferRoot_one]

theorem continuedPhase_continuousAt_one : ContinuousAt continuedPhase 1 := by
  have hrot : Continuous (fun W : ℂ => -Complex.I*(W-1)) := by fun_prop
  have hplus : Continuous (fun W : ℂ => W+1) := by fun_prop
  have hs0 : ContinuousAt Complex.sqrt (-Complex.I*((1 : ℂ)-1)) :=
    Complex.continuousAt_sqrt (Or.inl (by norm_num))
  have hs2 : ContinuousAt Complex.sqrt ((1 : ℂ)+1) :=
    Complex.continuousAt_sqrt (Or.inl (by norm_num))
  have hu : ContinuousAt continuedTransferRoot 1 :=
    continuousAt_id.sub ((continuousAt_const.mul
      (hs0.comp (f := fun W : ℂ => -Complex.I*(W-1)) hrot.continuousAt)).mul
        (hs2.comp (f := fun W : ℂ => W+1) hplus.continuousAt))
  have hl : ContinuousAt Complex.log (continuedTransferRoot 1) := by
    rw [continuedTransferRoot_one]
    exact (Complex.differentiableAt_log (Or.inl (by norm_num))).continuousAt
  exact continuousAt_const.mul (hl.comp (f := continuedTransferRoot) hu)

theorem continuedPhase_im_dispersion (W : ℂ) :
    W.im = Real.sin (continuedPhase W).re*Real.sinh (-(continuedPhase W).im) := by
  have h := congrArg Complex.im (continuedPhase_cos W)
  rw [Complex.cos_eq] at h
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,
    ← Complex.ofReal_cosh,← Complex.ofReal_sinh,Complex.sub_im,Complex.mul_im,
    Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_mul,zero_add,Complex.I_re,
    Complex.I_im,Complex.mul_re,mul_one,sub_zero] at h
  rw [Real.sinh_neg]
  linarith

theorem real_sinh_le_mul_cosh {G : ℝ} (hG : 0 ≤ G) :
    Real.sinh G ≤ Real.cosh G*G := by
  have hbound (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) G)) :
      deriv Real.sinh t ≤ Real.cosh G := by
    rw [Real.deriv_sinh]
    apply Real.cosh_le_cosh.mpr
    have ht' := interior_subset ht
    simpa only [abs_of_nonneg ht'.1,abs_of_nonneg hG] using ht'.2
  have h := (convex_Icc (0 : ℝ) G).image_sub_le_mul_sub_of_deriv_le
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
    hbound 0 ⟨le_rfl,hG⟩ G ⟨hG,le_rfl⟩ hG
  simpa using h

/-- The endpoint gain dominates every fixed multiple of Im W near W=1
on the actual upper physical sheet. -/
theorem endpoint_phase_dominates_im (K : ℝ) (hK : 0 ≤ K) :
    ∃ δ > 0, ∀ W : ℂ, ‖W-1‖ < δ → 0 < W.im →
      K*W.im ≤ -(continuedPhase W).im := by
  have hc : ContinuousAt (fun W : ℂ =>
      K*(Real.sin (continuedPhase W).re*Real.cosh (continuedPhase W).im)) 1 := by
    have hr := Complex.continuous_re.continuousAt.comp continuedPhase_continuousAt_one
    have hi := Complex.continuous_im.continuousAt.comp continuedPhase_continuousAt_one
    exact continuousAt_const.mul
      ((Real.continuous_sin.continuousAt.comp hr).mul (Real.continuous_cosh.continuousAt.comp hi))
  have he : ∀ᶠ W : ℂ in 𝓝 1,
      K*(Real.sin (continuedPhase W).re*Real.cosh (continuedPhase W).im) < 1 :=
    hc.eventually_lt continuousAt_const (by simp [continuedPhase_one])
  obtain ⟨δ,hδ,hprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro W hdist hW
  have hsmall := hprop (y := W) (by simpa [dist_eq_norm] using hdist)
  obtain ⟨hα,hαpi,hG⟩ := continuedPhase_upper_sheet hW
  have hsin : 0 ≤ Real.sin (continuedPhase W).re :=
    (Real.sin_pos_of_pos_of_lt_pi hα hαpi).le
  have hg : 0 ≤ -(continuedPhase W).im := by linarith
  have hb := mul_le_mul_of_nonneg_left (real_sinh_le_mul_cosh hg) hsin
  rw [← continuedPhase_im_dispersion,Real.cosh_neg] at hb
  have hb' := mul_le_mul_of_nonneg_left hb hK
  have hc' := mul_le_mul_of_nonneg_right hsmall.le hg
  nlinarith

/-- Exterior boundary damping is strictly positive at every real W>1. -/
theorem continuedPhase_exterior_im_neg {W : ℝ} (hW : 1 < W) :
    (continuedPhase (W : ℂ)).im < 0 := by
  have hsq : (Real.sqrt (W^2-1))^2=W^2-1 := Real.sq_sqrt (by nlinarith)
  have hs := Real.sqrt_nonneg (W^2-1)
  have hu0 : 0 < W-Real.sqrt (W^2-1) := by nlinarith
  have hu1 : W-Real.sqrt (W^2-1) < 1 := by nlinarith
  rw [continuedPhase_im,continuedTransferRoot_real_exterior hW,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0]
  exact Real.log_neg hu0 hu1

/-- Literal left side of the manuscript's phase inequality. -/
def commonPhaseGain (x v y r c : ℝ) : ℝ :=
  ((((deriv (cutPhase x) c : ℝ) : ℂ)*scalarGraph (cutHalfWidth x) v r c)-
    continuedPhase (graphDispersion x (cutHalfWidth x) v y r c)).im

theorem commonPhaseGain_eq (x v y r c : ℝ) :
    commonPhaseGain x v y r c =
      v*(deriv (cutPhase x) c*(contourDisplacement (cutHalfWidth x) r-c))-
        (continuedPhase (graphDispersion x (cutHalfWidth x) v y r c)).im := by
  simp [commonPhaseGain,scalarGraph,Complex.mul_im]
  ring

theorem graph_im_lower {x b v y r c a : ℝ} (hv : 0 ≤ v)
    (hdir : a ≤ graphDirection b r c) (ha : 0 < a) :
    y+a*v ≤ (graphDispersion x b v y r c).im := by
  rw [graphDispersion_im]
  have hpos : 0 < Real.sin r*(contourDisplacement b r-c) := ha.trans_le hdir
  have hp : v*(Real.sin r*(contourDisplacement b r-c)) ≤
      Real.sin r*Real.sinh (v*(contourDisplacement b r-c)) := by
    rcases mul_pos_iff.mp hpos with h | h
    · have hh := mul_le_mul_of_nonneg_left
        (Real.self_le_sinh_iff.mpr (mul_nonneg hv h.2.le)) h.1.le
      nlinarith
    · have hh := mul_le_mul_of_nonpos_left
        (Real.sinh_le_self_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hv h.2.le)) h.1.le
      nlinarith
  have hh := mul_le_mul_of_nonneg_right hdir hv
  change a*v ≤ (Real.sin r*(contourDisplacement b r-c))*v at hh
  nlinarith

theorem center_slope_continuousOn {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hdb : d < cutHalfWidth x) : ContinuousOn (deriv (cutPhase x)) (Icc (-d) d) := by
  intro c hc
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 ((abs_le.mpr hc).trans_lt hdb)
  exact (cutPhase_second_hasDerivAt h0 h1).continuousAt.continuousWithinAt

theorem common_slope_displacement_bound {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hdb : d < cutHalfWidth x) :
    ∃ L > 0, ∀ r ∈ Icc (-Real.pi) Real.pi, ∀ c ∈ Icc (-d) d,
      |deriv (cutPhase x) c*(contourDisplacement (cutHalfWidth x) r-c)| ≤ L := by
  have hf := contourDisplacement_continuous (cutHalfWidth_range hx hx2).1.le
    (cutHalfWidth_range hx hx2).2
  have hc := center_slope_continuousOn hx hx2 hdb
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      |deriv (cutPhase x) p.2*(contourDisplacement (cutHalfWidth x) p.1-p.2)|)
      (Icc (-Real.pi) Real.pi ×ˢ Icc (-d) d) := by
    apply ContinuousOn.abs
    apply ContinuousOn.mul
    · exact hc.comp continuous_snd.continuousOn (fun _ hp => hp.2)
    · exact ((hf.comp continuous_fst).sub continuous_snd).continuousOn
  obtain ⟨L,hL⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hcont
  refine ⟨max 1 L,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro r hr c hc
  exact (hL (mem_image_of_mem _ (show (r,c) ∈ Icc (-Real.pi) Real.pi ×ˢ Icc (-d) d from ⟨hr,hc⟩))).trans (le_max_right _ _)

/-- On neighborhoods of both branch endpoints, the actual common graph
satisfies (5) with coefficient 1 after shrinking its height. -/
theorem endpoint_common_phase_gain {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ η > 0, ∃ ε > 0, ∀ r ∈ Icc (-Real.pi) Real.pi,
      (|r-cutHalfWidth x| < η ∨ |r+cutHalfWidth x| < η) →
      ∀ c ∈ Icc (-d) d, ∀ v, 0 < v → v ≤ ε → ∀ y ∈ Icc (0 : ℝ) ε,
        y+v*(r-c)^2 ≤ commonPhaseGain x v y r c := by
  let b := cutHalfWidth x
  have hb := (cutHalfWidth_range hx hx2).1
  have hbpi := (cutHalfWidth_range hx hx2).2
  have hsin : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbpi
  let a := Real.sin b*(b-d)/2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨L,hL,hLbound⟩ := common_slope_displacement_bound hx hx2 hdb
  let R := Real.pi+d
  have hR : 0 < R := by dsimp [R]; linarith [Real.pi_pos]
  let K : ℝ := 1+(L+R^2+1)/a
  have hK1 : 1 ≤ K := by
    dsimp [K]
    exact le_add_of_nonneg_right (by positivity)
  have hK : 0 ≤ K := zero_le_one.trans hK1
  have hKa : a*K = a+L+R^2+1 := by dsimp [K]; field_simp; ring
  obtain ⟨δ,hδ,hendpoint⟩ := endpoint_phase_dominates_im K hK
  let S : Set (ℝ × ℝ) := ({b,-b} : Set ℝ) ×ˢ Icc (-d) d
  have hS : IsCompact S := (Set.toFinite ({b,-b} : Set ℝ)).isCompact.prod isCompact_Icc
  have hf := contourDisplacement_continuous hb.le hbpi
  have he : ∀ᶠ z : ℝ × (ℝ × ℝ) in 𝓝 (0,(0,0)), ∀ p ∈ S,
      a < graphDirection b (p.1+z.2.2) p.2 ∧
      ‖graphDispersion x b z.1 z.2.1 (p.1+z.2.2) p.2-1‖ < δ := by
    apply hS.eventually_forall_of_forall_eventually
    intro p hp
    have hpEnd : p.1=b ∨ p.1= -b := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hp.1
    have hdir : a < graphDirection b p.1 p.2 := by
      rcases hpEnd with hp0 | hp0
      · rw [hp0,graphDirection,contourDisplacement_interior (le_of_eq (abs_of_pos hb))]
        dsimp [a]
        nlinarith [mul_nonneg hsin.le (sub_nonneg.mpr hp.2.2)]
      · rw [hp0,graphDirection,contourDisplacement_interior (by simpa only [abs_neg] using le_of_eq (abs_of_pos hb)),Real.sin_neg]
        dsimp [a]
        nlinarith [mul_nonneg hsin.le (show 0 ≤ p.2+d by linarith [hp.2.1])]
    have hbase : graphDispersion x b 0 0 p.1 p.2=1 := by
      have hcos : Real.cos p.1=x-1 := by
        rcases hpEnd with he | he
        · rw [he]
          exact Real.cos_arccos (by linarith) (by linarith)
        · rw [he,Real.cos_neg]
          exact Real.cos_arccos (by linarith) (by linarith)
      simp [graphDispersion,scalarGraph,← Complex.ofReal_cos,hcos]
    have hdc : Continuous (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        graphDirection b (z.2.1+z.1.2.2) z.2.2) := by
      unfold graphDirection
      fun_prop
    have hwc : Continuous (fun z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
        ‖graphDispersion x b z.1.1 z.1.2.1 (z.2.1+z.1.2.2) z.2.2-1‖) := by
      unfold graphDispersion scalarGraph
      fun_prop
    have ho : IsOpen {z : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) |
        a < graphDirection b (z.2.1+z.1.2.2) z.2.2 ∧
        ‖graphDispersion x b z.1.1 z.1.2.1 (z.2.1+z.1.2.2) z.2.2-1‖ < δ} :=
      (isOpen_lt continuous_const hdc).inter (isOpen_lt hwc continuous_const)
    apply ho.mem_nhds
    constructor
    · simpa only [add_zero] using hdir
    · simpa only [add_zero,hbase,sub_self,norm_zero] using hδ
  obtain ⟨τ,hτ,hprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨τ/2,by positivity,τ/2,by positivity,?_⟩
  intro r hr hnear c hc v hv hvτ y hy
  obtain ⟨r0,hr0,hrr⟩ : ∃ r0 ∈ ({b,-b} : Set ℝ), |r-r0| < τ/2 := by
    rcases hnear with h | h
    · exact ⟨b,Or.inl rfl,h⟩
    · exact ⟨-b,Or.inr rfl,by simpa only [sub_neg_eq_add] using h⟩
  have hdist : dist (v,(y,r-r0)) ((0 : ℝ),(0,0)) < τ := by
    simp only [Prod.dist_eq,Real.dist_eq,sub_zero,abs_of_pos hv,abs_of_nonneg hy.1]
    exact max_lt (by linarith) (max_lt (by linarith [hy.2]) (by linarith))
  have hpair := hprop (y := (v,(y,r-r0))) hdist (r0,c) ⟨hr0,hc⟩
  simp only [add_sub_cancel] at hpair
  have him := graph_im_lower (x := x) (y := y) hv.le hpair.1.le ha
  have himpos : 0 < (graphDispersion x b v y r c).im := by
    nlinarith [mul_pos ha hv,hy.1]
  have hG := hendpoint (graphDispersion x b v y r c) hpair.2 himpos
  have hmult := mul_le_mul_of_nonneg_left him hK
  have hcoef := (abs_le.mp (hLbound r hr c hc)).1
  have hcoefv := mul_le_mul_of_nonneg_left hcoef hv.le
  have habs : |r-c| ≤ R := by
    calc
      _ ≤ |r|+|c| := by simpa using abs_sub_le r 0 c
      _ ≤ Real.pi+d := add_le_add (abs_le.mpr hr) (abs_le.mpr hc)
  have hsquare : (r-c)^2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR.le).mpr habs
  rw [commonPhaseGain_eq]
  change y+v*(r-c)^2 ≤ v*(deriv (cutPhase x) c*(contourDisplacement b r-c))-
    (continuedPhase (graphDispersion x b v y r c)).im
  have hvSq := mul_le_mul_of_nonneg_left hsquare hv.le
  have hyK := mul_le_mul_of_nonneg_right hK1 hy.1
  nlinarith

end
end IsoProof
