import IsoProof.ContourParameter

/-! Stability near the stationary diagonal for a fixed graph height.
This is the local real-energy uniformity step; unlike a plain continuity
argument it preserves the quadratic zero at r=c. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem quadratic_gain_of_second {F F' : ℝ → ℝ} {a : ℝ}
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc (0 : ℝ) 1, ∃ d, HasDerivAt F' d t ∧ a ≤ d)
    (h0 : F 0=0) (h0' : F' 0=0) : a/2 ≤ F 1 := by
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : a*t ≤ F' t := by
    have hsub : Icc 0 t ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    have hm := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv
      (fun s hs => (hF' s (hsub hs)).choose_spec.1.continuousAt.continuousWithinAt)
      (fun s hs => (hF' s (hsub (interior_subset hs))).choose_spec.1.differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(hF' s (hsub (interior_subset hs))).choose_spec.1.deriv]
        exact (hF' s (hsub (interior_subset hs))).choose_spec.2)
      0 ⟨le_rfl,ht.1⟩ t ⟨ht.1,le_rfl⟩ ht.1
    simpa only [sub_zero,h0'] using hm
  let G := fun t : ℝ => F t-a*t^2/2
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt G (F' t-a*t) t := by
    convert (hF t ht).sub ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hG t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (C := 0) (fun t ht => by
      rw [(hG t (interior_subset ht)).deriv]
      linarith [hfirst t (interior_subset ht)])
    0 (by simp) 1 (by simp) (by norm_num)
  dsimp [G] at hm
  simp only [h0,zero_pow (by omega : 2 ≠ 0),mul_zero,zero_div,sub_zero,one_pow,mul_one] at hm
  linarith

/-- At the stationary diagonal the graph curvature is exactly -2v g''.
Compactness preserves a positive margin jointly in real energy, horizontal
displacement and height, while the E-height derivative stays positive. -/
theorem fixed_graph_diagonal_controls {x₀ d v : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (hdb : d < cutHalfWidth x₀) (hv : 0 < v) :
    ∃ η > 0, ∀ x h y : ℝ, |x-x₀| < η → |h| < η → |y| < η →
      ∀ c ∈ Icc (-d) d,
      let L := (1 : ℂ)+Complex.I*(v : ℂ)
      let q := (c : ℂ)+L*(h : ℂ)
      let E := (x : ℂ)+Complex.I*(y : ℂ)
      0 < x ∧ x < 2 ∧ |c| < cutHalfWidth x ∧
      (E-Complex.cos q ∈ contourRootDomain) ∧
      v*(x₀*(1-x₀^2/4)) < -(L^2*phaseAngleSecond E q).im ∧
      (1/2 : ℝ) < ((Complex.sin (continuedPhase (E-Complex.cos q)))⁻¹).re := by
  let L : ℂ := 1+Complex.I*(v : ℂ)
  let κ : ℝ := x₀*(1-x₀^2/4)
  have hκ : 0 < κ := by
    dsimp [κ]
    have : 0 < 1-x₀^2/4 := by nlinarith
    positivity
  let K := Icc (-d) d
  have hK : IsCompact K := isCompact_Icc
  let E := fun z : (ℝ × (ℝ × ℝ)) × ℝ => (z.1.1 : ℂ)+Complex.I*(z.1.2.2 : ℂ)
  let Q := fun z : (ℝ × (ℝ × ℝ)) × ℝ => (z.2 : ℂ)+L*(z.1.2.1 : ℂ)
  have hE : Continuous E := by fun_prop
  have hQ : Continuous Q := by fun_prop
  have hW : Continuous (fun z => E z-Complex.cos (Q z)) := hE.sub (Complex.continuous_cos.comp hQ)
  have he : ∀ᶠ p : ℝ × (ℝ × ℝ) in 𝓝 (x₀,(0,0)), ∀ c∈K,
      0 < p.1 ∧ p.1 < 2 ∧ |c| < cutHalfWidth p.1 ∧
      (E (p,c)-Complex.cos (Q (p,c)) ∈ contourRootDomain) ∧
      v*κ < -(L^2*phaseAngleSecond (E (p,c)) (Q (p,c))).im ∧
      (1/2 : ℝ) < ((Complex.sin (continuedPhase (E (p,c)-Complex.cos (Q (p,c)))))⁻¹).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro c hc
    have hcb : |c| < cutHalfWidth x₀ := (abs_le.mpr hc).trans_lt hdb
    have hD : E ((x₀,(0,0)),c)-Complex.cos (Q ((x₀,(0,0)),c)) ∈ contourRootDomain := by
      simpa only [E,Q,Complex.ofReal_zero,mul_zero,add_zero] using real_angle_domain hx hx2 hcb
    have hd : ∀ᶠ z in 𝓝 ((x₀,(0,0)),c), E z-Complex.cos (Q z) ∈ contourRootDomain :=
      (contourRootDomain_isOpen.preimage hW).mem_nhds hD
    have hsecond : ContinuousAt (fun z => -(L^2*phaseAngleSecond (E z) (Q z)).im)
        ((x₀,(0,0)),c) := by
      have hc := (phaseAngleSecond_continuousAt hD).comp
        (f := fun z => (E z,Q z)) (hE.prodMk hQ).continuousAt
      exact (Complex.continuous_im.continuousAt.comp (continuousAt_const.mul hc)).neg
    have hbase : v*κ < -(L^2*phaseAngleSecond (E ((x₀,(0,0)),c)) (Q ((x₀,(0,0)),c))).im := by
      simp only [E,Q,Complex.ofReal_zero,mul_zero,add_zero]
      rw [phaseAngleSecond_real hx hx2 hcb]
      have hcurv := (cutPhase_curvature_lower hx hx2 hcb).2
      have heq : -(L^2*((deriv (deriv (cutPhase x₀)) c : ℝ) : ℂ)).im =
          -2*v*deriv (deriv (cutPhase x₀)) c := by
        dsimp [L]
        simp only [pow_two,Complex.mul_im,Complex.mul_re,Complex.add_im,Complex.add_re,
          Complex.one_im,Complex.one_re,Complex.I_im,Complex.I_re,Complex.ofReal_re,Complex.ofReal_im]
        ring
      rw [heq]
      have h := mul_le_mul_of_nonneg_left hcurv hv.le
      change κ ≤ _ at hcurv
      have hvκ := mul_pos hv hκ
      dsimp [κ] at hvκ ⊢
      nlinarith
    have hp := (continuedPhase_analyticAt hD).continuousAt.comp (f := fun z => E z-Complex.cos (Q z))
      hW.continuousAt
    have hinv := (Complex.continuous_sin.continuousAt.comp hp).inv₀ (continuedPhase_sin_ne_zero hD)
    have hheight := Complex.continuous_re.continuousAt.comp hinv
    have hbaseheight : (1/2 : ℝ) <
        ((Complex.sin (continuedPhase (E ((x₀,(0,0)),c)-Complex.cos (Q ((x₀,(0,0)),c)))))⁻¹).re := by
      simp only [E,Q,Complex.ofReal_zero,mul_zero,add_zero]
      rw [show continuedPhase ((x₀ : ℂ)-Complex.cos (c : ℂ)) = (cutPhase x₀ c : ℂ) from
        anglePhase_real hx hx2 hcb,← Complex.ofReal_sin,← Complex.ofReal_inv,Complex.ofReal_re]
      obtain ⟨h0,h1⟩ := cutPhase_argument_range hx hx2 hcb
      have hh := (one_le_inv₀ (cutPhase_sin_pos h0 h1)).mpr (Real.sin_le_one _)
      linarith
    have hgeo : ∀ᶠ z : (ℝ × (ℝ × ℝ)) × ℝ in 𝓝 ((x₀,(0,0)),c),
        0 < z.1.1 ∧ z.1.1 < 2 ∧ |z.2| < cutHalfWidth z.1.1 := by
      have hopen : IsOpen {z : (ℝ × (ℝ × ℝ)) × ℝ |
          0 < z.1.1 ∧ z.1.1 < 2 ∧ |z.2| < cutHalfWidth z.1.1} := by
        have h1 : IsOpen {z : (ℝ × (ℝ × ℝ)) × ℝ | 0 < z.1.1} :=
          isOpen_lt continuous_const (by fun_prop)
        have h2 : IsOpen {z : (ℝ × (ℝ × ℝ)) × ℝ | z.1.1 < 2} :=
          isOpen_lt (by fun_prop) continuous_const
        have h3 : IsOpen {z : (ℝ × (ℝ × ℝ)) × ℝ | |z.2| < cutHalfWidth z.1.1} :=
          isOpen_lt (by fun_prop) (by unfold cutHalfWidth; fun_prop)
        exact h1.inter (h2.inter h3)
      exact hopen.mem_nhds ⟨hx,hx2,hcb⟩
    filter_upwards [hgeo,hd,continuousAt_const.eventually_lt hsecond hbase,
      continuousAt_const.eventually_lt hheight hbaseheight] with z hz hDz hs hy
    exact ⟨hz.1,hz.2.1,hz.2.2,hDz,hs,hy⟩
  obtain ⟨η,hη,hηprop⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η,hη,?_⟩
  intro x h y hx' hh hy c hc
  have hd : dist (x,(h,y)) (x₀,((0 : ℝ),0)) < η := by
    simp only [Prod.dist_eq,Real.dist_eq,sub_zero]
    exact max_lt hx' (max_lt hh hy)
  exact hηprop (y := (x,(h,y))) hd c hc

theorem phase_height_gain {x y lam : ℝ} {q : ℂ} (hy : 0 ≤ y)
    (hcontrol : ∀ t∈Icc (0 : ℝ) y,
      (x : ℂ)+Complex.I*(t : ℂ)-Complex.cos q ∈ contourRootDomain ∧
      (1/2 : ℝ) ≤ ((Complex.sin (continuedPhase
        ((x : ℂ)+Complex.I*(t : ℂ)-Complex.cos q)))⁻¹).re) :
    (((lam : ℂ)*q-continuedPhase ((x : ℂ)-Complex.cos q)).im)+y/2 ≤
      (((lam : ℂ)*q-continuedPhase ((x : ℂ)+Complex.I*(y : ℂ)-Complex.cos q)).im) := by
  let W := fun t : ℝ => (x : ℂ)+Complex.I*(t : ℂ)-Complex.cos q
  let G := fun t : ℝ => ((lam : ℂ)*q-continuedPhase (W t)).im
  have hW (t : ℝ) : HasDerivAt W Complex.I t := by
    simpa [W] using ((Complex.ofRealCLM.hasDerivAt.const_mul Complex.I).const_add
      (x : ℂ)).sub_const (Complex.cos q)
  have hG (t : ℝ) (ht : t∈Icc (0 : ℝ) y) :
      HasDerivAt G ((Complex.sin (continuedPhase (W t)))⁻¹).re t := by
    have h := ((continuedPhase_hasDerivAt (hcontrol t ht).1).comp t (hW t)).const_sub ((lam : ℂ)*q)
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
    convert hi using 1
    · rfl
    · simp [Complex.imCLM_apply,neg_div,one_div,W]
  have hm := (convex_Icc (0 : ℝ) y).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hG t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hG t (interior_subset ht)).deriv]
      exact (hcontrol t (interior_subset ht)).2)
    0 ⟨le_rfl,hy⟩ y ⟨hy,le_rfl⟩ hy
  dsimp [G,W] at hm
  simp only [mul_zero,add_zero,sub_zero] at hm
  simp only [Complex.sub_im]
  linarith

theorem stationary_phase_quadratic {x c v h κ : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hc : |c| < cutHalfWidth x)
    (hcontrol : ∀ t∈Icc (0 : ℝ) 1,
      let L := (1 : ℂ)+Complex.I*(v : ℂ)
      let q := (c : ℂ)+L*((t*h : ℝ) : ℂ)
      ((x : ℂ)-Complex.cos q ∈ contourRootDomain) ∧
      κ ≤ -(L^2*phaseAngleSecond (x : ℂ) q).im) :
    κ*h^2/2 ≤
      ((((deriv (cutPhase x) c : ℝ) : ℂ)*((c : ℂ)+(1+Complex.I*(v : ℂ))*(h : ℂ))-
        continuedPhase ((x : ℂ)-Complex.cos ((c : ℂ)+(1+Complex.I*(v : ℂ))*(h : ℂ)))).im) := by
  let L : ℂ := 1+Complex.I*(v : ℂ)
  let lam : ℂ := ((deriv (cutPhase x) c : ℝ) : ℂ)
  let Q := fun t : ℝ => (c : ℂ)+L*((t*h : ℝ) : ℂ)
  let P := fun q : ℂ => -Complex.sin q/Complex.sin (continuedPhase ((x : ℂ)-Complex.cos q))
  let F := fun t : ℝ => (lam*Q t-continuedPhase ((x : ℂ)-Complex.cos (Q t))).im
  let F' := fun t : ℝ => (lam*(L*(h : ℂ))-P (Q t)*(L*(h : ℂ))).im
  have hQ (t : ℝ) : HasDerivAt Q (L*(h : ℂ)) t := by
    simpa [Q] using (((hasDerivAt_id t).mul_const h).ofReal_comp.const_mul L).const_add (c : ℂ)
  have hF (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : HasDerivAt F (F' t) t := by
    have hd := (continuedPhase_angle_hasDerivAt (hcontrol t ht).1).comp t (hQ t)
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (((hQ t).const_mul lam).sub hd)
  have hF' (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      ∃ d, HasDerivAt F' d t ∧ κ*h^2 ≤ d := by
    have hd := (phaseAngleFirst_hasDerivAt (hcontrol t ht).1).comp t (hQ t)
    have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hd.mul_const (L*(h : ℂ))).const_sub (lam*(L*(h : ℂ))))
    refine ⟨h^2*(-(L^2*phaseAngleSecond (x : ℂ) (Q t)).im),?_,?_⟩
    · convert hi using 1
      · rfl
      · simp only [Complex.imCLM_apply,Complex.neg_im,Complex.mul_im,Complex.mul_re,
          Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,pow_two]
        ring
    · exact (mul_le_mul_of_nonneg_right (hcontrol t ht).2 (sq_nonneg h)).trans_eq (mul_comm _ _)
  have hQ0 : Q 0=(c : ℂ) := by simp [Q]
  have hP0 : P (c : ℂ)=lam := by
    have hd := (continuedPhase_angle_hasDerivAt (real_angle_domain hx hx2 hc)).deriv
    change deriv (anglePhase x) (c : ℂ)=P (c : ℂ) at hd
    rw [← hd,anglePhase_deriv_real hx hx2 hc]
  have h0 : F 0=0 := by
    simp only [F,hQ0,show continuedPhase ((x : ℂ)-Complex.cos (c : ℂ))=(cutPhase x c : ℂ) from
      anglePhase_real hx hx2 hc,lam,Complex.sub_im,Complex.mul_im,Complex.ofReal_im,mul_zero,zero_mul,
      zero_add,sub_zero]
  have h0' : F' 0=0 := by simp only [F',hQ0,hP0,sub_self,Complex.zero_im]
  have hb := quadratic_gain_of_second hF hF' h0 h0'
  simpa only [F,Q,L,lam,one_mul] using hb

end
end IsoProof
