import IsoProof.ContourPhase
import IsoProof.ContourGeometry
import IsoProof.ContourCompact
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Quantitative interior part of (5), obtained from the actual holomorphic
phase and its uniformly negative real second derivative. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set Filter

def anglePhase (x : ℝ) (q : ℂ) : ℂ :=
  continuedPhase ((x : ℂ)-Complex.cos q)

theorem anglePhase_analyticAt {x : ℝ} {q : ℂ}
    (h : (x : ℂ)-Complex.cos q ∈ contourRootDomain) : AnalyticAt ℂ (anglePhase x) q := by
  have hi : AnalyticAt ℂ (fun q : ℂ => (x : ℂ)-Complex.cos q) q := by fun_prop
  exact (continuedPhase_analyticAt h).comp (f := fun q : ℂ => (x : ℂ)-Complex.cos q) hi

theorem real_angle_domain {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : |r| < cutHalfWidth x) :
    (x : ℂ)-Complex.cos (r : ℂ) ∈ contourRootDomain := by
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hr
  simpa only [← Complex.ofReal_cos,← Complex.ofReal_sub] using
    real_mem_contourRootDomain h0 h1.ne

theorem anglePhase_real {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : |r| < cutHalfWidth x) : anglePhase x (r : ℂ) = (cutPhase x r : ℂ) := by
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hr
  simpa only [anglePhase,cutPhase,← Complex.ofReal_cos,← Complex.ofReal_sub]
    using continuedPhase_real_interior h0 h1

theorem anglePhase_deriv_real {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : |r| < cutHalfWidth x) :
    deriv (anglePhase x) (r : ℂ) = ((deriv (cutPhase x) r : ℝ) : ℂ) := by
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hr
  have hd := (continuedPhase_angle_hasDerivAt (real_angle_domain hx hx2 hr)).deriv
  change deriv (anglePhase x) (r : ℂ) = _ at hd
  rw [hd, show continuedPhase ((x : ℂ)-Complex.cos (r : ℂ)) =
      (cutPhase x r : ℂ) from anglePhase_real hx hx2 hr,
    ← Complex.ofReal_sin,← Complex.ofReal_sin,(cutPhase_hasDerivAt h0 h1).deriv]
  push_cast
  rfl

theorem anglePhase_second_real {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : |r| < cutHalfWidth x) :
    deriv (deriv (anglePhase x)) (r : ℂ) =
      ((-x*(1-x*Real.cos r+(Real.cos r)^2)/(Real.sin (cutPhase x r))^3 : ℝ) : ℂ) := by
  obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hr
  have hF := ((anglePhase_analyticAt (real_angle_domain hx hx2 hr)).deriv).differentiableAt.hasDerivAt.comp_ofReal
  have hneigh : ∀ᶠ t in 𝓝 r, |t| < cutHalfWidth x :=
    (continuous_abs.continuousAt.eventually_lt continuousAt_const hr)
  have he : (fun t : ℝ => deriv (anglePhase x) (t : ℂ)) =ᶠ[𝓝 r]
      (fun t : ℝ => ((deriv (cutPhase x) t : ℝ) : ℂ)) := by
    filter_upwards [hneigh] with t ht
    exact anglePhase_deriv_real hx hx2 ht
  have hF' := hF.congr_of_eventuallyEq he.symm
  exact hF'.unique (cutPhase_second_hasDerivAt h0 h1).ofReal_comp

/-- Complex second derivatives inherit a uniform strict real sign in a
small common imaginary deformation, uniformly along every interior
segment joining c to r. -/
theorem interior_second_uniform {x s : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (_hs : 0 ≤ s) (hsb : s < cutHalfWidth x) :
    ∃ ε > 0, ∀ v : ℝ, |v| < ε →
      ∀ r ∈ Icc (-s) s, ∀ c ∈ Icc (-s) s, ∀ t ∈ Icc (0 : ℝ) 1,
      let q := (c : ℂ)+(1+Complex.I*(v : ℂ))*((t*(r-c) : ℝ) : ℂ)
      ((x : ℂ)-Complex.cos q ∈ contourRootDomain) ∧
      (((1+Complex.I*(v : ℂ))*deriv (deriv (anglePhase x)) q).re <
        -x*(1-x^2/4)/2) := by
  let K : Set (ℝ × (ℝ × ℝ)) := Icc (-s) s ×ˢ (Icc (-s) s ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have he : ∀ᶠ v : ℝ in 𝓝 0, ∀ p ∈ K,
      let q := (p.2.1 : ℂ)+(1+Complex.I*(v : ℂ))*((p.2.2*(p.1-p.2.1) : ℝ) : ℂ)
      ((x : ℂ)-Complex.cos q ∈ contourRootDomain) ∧
      (((1+Complex.I*(v : ℂ))*deriv (deriv (anglePhase x)) q).re <
        -x*(1-x^2/4)/2) := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    let R : ℝ := p.2.1+p.2.2*(p.1-p.2.1)
    have hR : R ∈ Icc (-s) s := by
      have ht0 := hp.2.2.1
      have ht1 := hp.2.2.2
      have hleft := (convex_Icc (-s) s) hp.2.1 hp.1
        (by linarith : 0 ≤ 1-p.2.2) ht0 (by ring : 1-p.2.2+p.2.2=1)
      convert hleft using 1
      dsimp [R]
      ring
    have hRb : |R| < cutHalfWidth x := (abs_le.mpr hR).trans_lt hsb
    let Q := fun z : ℝ × (ℝ × (ℝ × ℝ)) =>
      (z.2.2.1 : ℂ)+(1+Complex.I*(z.1 : ℂ))*((z.2.2.2*(z.2.1-z.2.2.1) : ℝ) : ℂ)
    have hQ : Continuous Q := by fun_prop
    have hQ0 : Q (0,p) = (R : ℂ) := by simp [Q,R]
    have hD : (x : ℂ)-Complex.cos (Q (0,p)) ∈ contourRootDomain := by
      rw [hQ0]
      exact real_angle_domain hx hx2 hRb
    have hP : ∀ᶠ z in 𝓝 (0,p), (x : ℂ)-Complex.cos (Q z) ∈ contourRootDomain :=
      ((contourRootDomain_isOpen.preimage (continuous_const.sub
        (Complex.continuous_cos.comp hQ))).mem_nhds hD)
    have hcont : ContinuousAt (fun z : ℝ × (ℝ × (ℝ × ℝ)) =>
        ((1+Complex.I*(z.1 : ℂ))*deriv (deriv (anglePhase x)) (Q z)).re) (0,p) := by
      have hder := ((anglePhase_analyticAt (real_angle_domain hx hx2 hRb)).deriv.deriv).continuousAt
      rw [← hQ0] at hder
      have hp : ContinuousAt (fun z : ℝ × (ℝ × (ℝ × ℝ)) =>
          (1+Complex.I*(z.1 : ℂ))*deriv (deriv (anglePhase x)) (Q z)) (0,p) :=
        ((continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_fst))).continuousAt.mul
            (hder.comp (f := Q) hQ.continuousAt))
      exact Complex.continuous_re.continuousAt.comp hp
    have hbase :
        ((1+Complex.I*((0 : ℝ) : ℂ))*deriv (deriv (anglePhase x)) (Q (0,p))).re <
          -x*(1-x^2/4)/2 := by
      rw [hQ0,anglePhase_second_real hx hx2 hRb]
      simp only [Complex.ofReal_zero,mul_zero,add_zero,one_mul,Complex.ofReal_re]
      obtain ⟨hpos,hbound⟩ := cutPhase_curvature_lower hx hx2 hRb
      obtain ⟨hW0,hW1⟩ := cutPhase_argument_range hx hx2 hRb
      rw [(cutPhase_second_hasDerivAt hW0 hW1).deriv] at hbound
      linarith
    have hLt : ∀ᶠ z in 𝓝 (0,p),
        ((1+Complex.I*(z.1 : ℂ))*deriv (deriv (anglePhase x)) (Q z)).re <
          -x*(1-x^2/4)/2 := hcont.eventually_lt continuousAt_const hbase
    exact hP.and hLt
  obtain ⟨ε,hε,hprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε,hε,?_⟩
  intro v hv r hr c hc t ht
  exact hprop (y := v) (by simpa [Real.dist_eq] using hv) (r,(c,t)) ⟨hr,hc,ht⟩

/-- The two mean-value integrations in the compact interior are made
explicit: negative complex curvature first controls the deformation
velocity, including the stationary case r=c. -/
theorem interior_direction_gain {x r c v a : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hc : |c| < cutHalfWidth x)
    (hstep : ∀ t ∈ Icc (0 : ℝ) 1,
      let q := (c : ℂ)+(1+Complex.I*(v : ℂ))*((t*(r-c) : ℝ) : ℂ)
      ((x : ℂ)-Complex.cos q ∈ contourRootDomain) ∧
      (((1+Complex.I*(v : ℂ))*deriv (deriv (anglePhase x)) q).re ≤ -a)) :
    a*(r-c)^2 ≤ (r-c)*
      (deriv (cutPhase x) c-(deriv (anglePhase x)
        ((r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ))).re) := by
  let Q := fun t : ℝ =>
    (c : ℂ)+(1+Complex.I*(v : ℂ))*((t*(r-c) : ℝ) : ℂ)
  let H := fun t : ℝ => (r-c)*(deriv (anglePhase x) (Q t)).re
  have hQ (t : ℝ) : HasDerivAt Q ((1+Complex.I*(v : ℂ))*((r-c : ℝ) : ℂ)) t := by
    simpa [Q] using (((hasDerivAt_id t).mul_const (r-c)).ofReal_comp.const_mul (1+Complex.I*(v : ℂ))).const_add (c : ℂ)
  have hH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt H
      ((r-c)^2*((1+Complex.I*(v : ℂ))*deriv (deriv (anglePhase x)) (Q t)).re) t := by
    have hcpl := ((anglePhase_analyticAt (hstep t ht).1).deriv).differentiableAt.hasDerivAt
    have hp := hcpl.comp t (hQ t)
    have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
    convert hreal.const_mul (r-c) using 1
    · rfl
    · simp only [Complex.reCLM_apply,Q,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
        Complex.mul_im,zero_add]
      ring
  have hbound (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      deriv H t ≤ -a*(r-c)^2 := by
    rw [(hH t (interior_subset ht)).deriv]
    have h := mul_le_mul_of_nonneg_left (hstep t (interior_subset ht)).2 (sq_nonneg (r-c))
    nlinarith
  have hm := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hH t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hH t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) 1 (by simp) (by norm_num)
  have hQ0 : Q 0 = (c : ℂ) := by simp [Q]
  have hQ1 : Q 1 = (r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ) := by
    dsimp [Q]
    push_cast
    ring
  dsimp [H] at hm
  rw [hQ0,hQ1,anglePhase_deriv_real hx hx2 hc,Complex.ofReal_re] at hm
  linarith

/-- The v-part of equation (5), on a compact interval wholly inside the
oscillatory interval, with the exact quadratic exponent in r-c. -/
theorem interior_zero_height_phase_gain {x s : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hs : 0 ≤ s) (hsb : s < cutHalfWidth x) :
    ∃ ε > 0, ∀ r ∈ Icc (-s) s, ∀ c ∈ Icc (-s) s,
      ∀ v, 0 ≤ v → v ≤ ε →
      (x*(1-x^2/4)/2)*v*(r-c)^2 ≤
        ((((deriv (cutPhase x) c : ℝ) : ℂ)*
          ((r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ))-
          anglePhase x ((r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ))).im) := by
  obtain ⟨ε,hε,hsecond⟩ := interior_second_uniform hx hx2 hs hsb
  refine ⟨ε/2,by positivity,?_⟩
  intro r hr c hc v hv hvε
  have hrb : |r| < cutHalfWidth x := (abs_le.mpr hr).trans_lt hsb
  have hcb : |c| < cutHalfWidth x := (abs_le.mpr hc).trans_lt hsb
  let lam : ℝ := deriv (cutPhase x) c
  let Q := fun τ : ℝ => (r : ℂ)+Complex.I*((τ*(r-c) : ℝ) : ℂ)
  let G := fun τ : ℝ => ((lam : ℂ)*Q τ-anglePhase x (Q τ)).im
  have hτbound (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) v) : |τ| < ε := by
    rw [abs_of_nonneg hτ.1]
    linarith [hτ.2]
  have hDom (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) v) :
      (x : ℂ)-Complex.cos (Q τ) ∈ contourRootDomain := by
    have h := (hsecond τ (hτbound τ hτ) r hr c hc 1 (by simp)).1
    convert h using 1
    dsimp [Q]
    push_cast
    ring
  have hQ (τ : ℝ) : HasDerivAt Q (Complex.I*((r-c : ℝ) : ℂ)) τ := by
    simpa [Q] using (((hasDerivAt_id τ).mul_const (r-c)).ofReal_comp.const_mul Complex.I).const_add (r : ℂ)
  have hG (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) v) : HasDerivAt G
      ((r-c)*(lam-(deriv (anglePhase x) (Q τ)).re)) τ := by
    have hF := (anglePhase_analyticAt (hDom τ hτ)).differentiableAt.hasDerivAt
    have hp := ((hQ τ).const_mul (lam : ℂ)).sub (hF.comp τ (hQ τ))
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ hp
    convert hi using 1
    · rfl
    · simp only [Complex.imCLM_apply,Q,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,zero_add,one_mul,
        Complex.mul_re,sub_zero]
      ring
  have hbound (τ : ℝ) (hτ : τ ∈ interior (Icc (0 : ℝ) v)) :
      (x*(1-x^2/4)/2)*(r-c)^2 ≤ deriv G τ := by
    rw [(hG τ (interior_subset hτ)).deriv]
    exact interior_direction_gain hx hx2 hcb (fun t ht =>
      ⟨(hsecond τ (hτbound τ (interior_subset hτ)) r hr c hc t ht).1,
        by simpa [neg_div] using
          (hsecond τ (hτbound τ (interior_subset hτ)) r hr c hc t ht).2.le⟩)
  have hm := (convex_Icc (0 : ℝ) v).mul_sub_le_image_sub_of_le_deriv
    (fun τ hτ => (hG τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hG τ (interior_subset hτ)).differentiableAt.differentiableWithinAt)
    hbound 0 ⟨le_rfl,hv⟩ v ⟨hv,le_rfl⟩ hv
  have hG0 : G 0=0 := by
    simp [G,Q,anglePhase_real hx hx2 hrb]
  rw [hG0,sub_zero,sub_zero] at hm
  simpa only [G,Q,mul_assoc,mul_left_comm,mul_comm] using hm

/-- Uniform positive E-height derivative on the same compact interior. -/
theorem interior_height_uniform {x s : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (_hs : 0 ≤ s) (hsb : s < cutHalfWidth x) :
    ∃ ε > 0, ∀ v ∈ Icc (0 : ℝ) ε, ∀ y ∈ Icc (0 : ℝ) ε,
      ∀ r ∈ Icc (-s) s, ∀ c ∈ Icc (-s) s,
      let W := (x : ℂ)+Complex.I*(y : ℂ)-
        Complex.cos ((r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ))
      W ∈ contourRootDomain ∧ (1/2 : ℝ) < ((Complex.sin (continuedPhase W))⁻¹).re := by
  let K : Set (ℝ × ℝ) := Icc (-s) s ×ˢ Icc (-s) s
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have he : ∀ᶠ vy : ℝ × ℝ in 𝓝 (0,0), ∀ p ∈ K,
      let W := (x : ℂ)+Complex.I*(vy.2 : ℂ)-
        Complex.cos ((p.1 : ℂ)+Complex.I*((vy.1*(p.1-p.2) : ℝ) : ℂ))
      W ∈ contourRootDomain ∧ (1/2 : ℝ) < ((Complex.sin (continuedPhase W))⁻¹).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hrb : |p.1| < cutHalfWidth x := (abs_le.mpr hp.1).trans_lt hsb
    let W := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      (x : ℂ)+Complex.I*(z.1.2 : ℂ)-
        Complex.cos ((z.2.1 : ℂ)+Complex.I*((z.1.1*(z.2.1-z.2.2) : ℝ) : ℂ))
    have hW : Continuous W := by fun_prop
    have hW0 : W ((0,0),p) = (x : ℂ)-Complex.cos (p.1 : ℂ) := by simp [W]
    have hD : W ((0,0),p) ∈ contourRootDomain := by
      rw [hW0]
      exact real_angle_domain hx hx2 hrb
    have hDom : ∀ᶠ z in 𝓝 ((0,0),p), W z ∈ contourRootDomain :=
      (contourRootDomain_isOpen.preimage hW).mem_nhds hD
    have hphi := (continuedPhase_analyticAt hD).continuousAt.comp (f := W) hW.continuousAt
    have hsin := Complex.continuous_sin.continuousAt.comp hphi
    have hinv := hsin.inv₀ (continuedPhase_sin_ne_zero hD)
    have hcont : ContinuousAt
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ((Complex.sin (continuedPhase (W z)))⁻¹).re)
        ((0,0),p) := Complex.continuous_re.continuousAt.comp hinv
    have hbase : (1/2 : ℝ) < ((Complex.sin (continuedPhase (W ((0,0),p))))⁻¹).re := by
      rw [hW0,show continuedPhase ((x : ℂ)-Complex.cos (p.1 : ℂ)) =
        (cutPhase x p.1 : ℂ) from anglePhase_real hx hx2 hrb,
        ← Complex.ofReal_sin,← Complex.ofReal_inv,Complex.ofReal_re]
      obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hrb
      have hsin := cutPhase_sin_pos h0 h1
      have hone : 1 ≤ (Real.sin (cutPhase x p.1))⁻¹ :=
        (one_le_inv₀ hsin).mpr (Real.sin_le_one _)
      linarith
    have hgt : ∀ᶠ z in 𝓝 ((0,0),p),
        (1/2 : ℝ) < ((Complex.sin (continuedPhase (W z)))⁻¹).re :=
      continuousAt_const.eventually_lt hcont hbase
    exact hDom.and hgt
  obtain ⟨ε,hε,hprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε/2,by positivity,?_⟩
  intro v hv y hy r hr c hc
  have hdist : dist (v,y) ((0 : ℝ),0) < ε := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq,sub_zero,abs_of_nonneg hv.1,abs_of_nonneg hy.1]
    exact max_lt (by linarith [hv.2]) (by linarith [hy.2])
  exact hprop (y := (v,y)) hdist (r,c) ⟨hr,hc⟩

/-- Full compact-interior inequality in (5), with explicit positive
coefficients and the exact prescribed linear piece of the common graph. -/
theorem interior_phase_gain {x s : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hs : 0 ≤ s) (hsb : s < cutHalfWidth x) :
    ∃ ε > 0, ∀ v ∈ Icc (0 : ℝ) ε, ∀ y ∈ Icc (0 : ℝ) ε,
      ∀ r ∈ Icc (-s) s, ∀ c ∈ Icc (-s) s,
      let q := (r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ)
      (x*(1-x^2/4)/2)*v*(r-c)^2+y/2 ≤
        ((((deriv (cutPhase x) c : ℝ) : ℂ)*q-
          continuedPhase ((x : ℂ)+Complex.I*(y : ℂ)-Complex.cos q)).im) := by
  obtain ⟨εv,hεv,hvbound⟩ := interior_zero_height_phase_gain hx hx2 hs hsb
  obtain ⟨εy,hεy,hybound⟩ := interior_height_uniform hx hx2 hs hsb
  refine ⟨min εv εy,lt_min hεv hεy,?_⟩
  intro v hv y hy r hr c hc
  let q := (r : ℂ)+Complex.I*((v*(r-c) : ℝ) : ℂ)
  let lam : ℝ := deriv (cutPhase x) c
  let W := fun t : ℝ => (x : ℂ)+Complex.I*(t : ℂ)-Complex.cos q
  let G := fun t : ℝ => ((lam : ℂ)*q-continuedPhase (W t)).im
  have hvy : v ∈ Icc (0 : ℝ) εy := ⟨hv.1,hv.2.trans (min_le_right _ _)⟩
  have hW (t : ℝ) : HasDerivAt W Complex.I t := by
    simpa [W] using ((Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).const_add (x : ℂ)).sub_const (Complex.cos q)
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) y) :
      HasDerivAt G ((Complex.sin (continuedPhase (W t)))⁻¹).re t := by
    have hty : t ∈ Icc (0 : ℝ) εy := ⟨ht.1,ht.2.trans (hy.2.trans (min_le_right _ _))⟩
    have hdom := (hybound v hvy t hty r hr c hc).1
    have hphi := (continuedPhase_hasDerivAt hdom).comp t (hW t)
    have hp := hphi.const_sub ((lam : ℂ)*q)
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hp
    convert hi using 1
    · rfl
    · simp [Complex.imCLM_apply,neg_div,one_div,W,q]
  have hder (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) y)) : (1/2 : ℝ) ≤ deriv G t := by
    rw [(hG t (interior_subset ht)).deriv]
    have ht' := interior_subset ht
    exact (hybound v hvy t ⟨ht'.1,ht'.2.trans (hy.2.trans (min_le_right _ _))⟩ r hr c hc).2.le
  have hm := (convex_Icc (0 : ℝ) y).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hG t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    hder 0 ⟨le_rfl,hy.1⟩ y ⟨hy.1,le_rfl⟩ hy.1
  have hzero : (x*(1-x^2/4)/2)*v*(r-c)^2 ≤ G 0 := by
    simpa [G,W,q,lam,anglePhase] using
      hvbound r hr c hc v hv.1 (hv.2.trans (min_le_left _ _))
  dsimp [G,W] at hm hzero ⊢
  linarith

end
end IsoProof
