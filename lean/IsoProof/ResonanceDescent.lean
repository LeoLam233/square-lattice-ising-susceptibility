import IsingBulk.HT.First.RadialJetDescent
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Sharp descent from an actual simple-pole asymptotic.  The key result is
new: a nonzero limit of t times the derivative forces the primitive to have
unbounded norm.  This removes the one-derivative discrepancy between the
older HT calculation and the five-page manuscript's sharp order. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Integrating the real differential inequality G(t) ≥ c/t gives a
logarithmic lower divergence toward the endpoint. -/
theorem tendsto_atBot_of_derivative_inv_lower {F G : ℝ → ℝ} {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hder : ∀ x ∈ Ioc 0 a, HasDerivAt F (G x) x)
    (hbound : ∀ x ∈ Ioc 0 a, c/x ≤ G x) :
    Tendsto F (𝓝[>] 0) atBot := by
  let H : ℝ → ℝ := fun x => F x-c*Real.log x
  have hd (x : ℝ) (hx : x ∈ Ioc 0 a) :
      HasDerivAt H (G x-c/x) x := by
    convert! (hder x hx).sub ((Real.hasDerivAt_log hx.1.ne').const_mul c) using 1
  have hm : MonotoneOn H (Ioc 0 a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 a)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact sub_nonneg.mpr (hbound x (interior_subset hx))
  have hupper : ∀ x ∈ Ioc 0 a, F x ≤ H a+c*Real.log x := by
    intro x hx
    have h := hm hx ⟨ha, le_rfl⟩ hx.2
    dsimp [H] at h ⊢
    linarith
  have ht : Tendsto (fun x : ℝ => H a+c*Real.log x) (𝓝[>] 0) atBot := by
    have h := Real.tendsto_log_nhdsGT_zero.const_mul_atBot hc
    exact tendsto_atBot_add_const_left _ (H a) h
  apply tendsto_atBot_mono' _ ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with x hx hxa
  exact hupper x ⟨hx,hxa.le⟩

/-- A genuine one-sided simple-pole derivative asymptotic produces
unbounded norm of the primitive; no divergence premise is inserted. -/
theorem norm_tendsto_atTop_of_simple_pole_derivative {F G : ℝ → ℂ} {L : ℂ}
    (hL : L ≠ 0)
    (hder : ∀ᶠ x : ℝ in 𝓝[>] 0, HasDerivAt F (G x) x)
    (hlim : Tendsto (fun x : ℝ => (x:ℂ)*G x) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun x : ℝ => ‖F x‖) (𝓝[>] 0) atTop := by
  let u : ℂ := L⁻¹
  let f : ℝ → ℝ := fun x => (u*F x).re
  let g : ℝ → ℝ := fun x => (u*G x).re
  have hscalar : Tendsto (fun x : ℝ => x*g x) (𝓝[>] 0) (𝓝 1) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (hlim.const_mul u)
    have hu : u*L=1 := inv_mul_cancel₀ hL
    rw [hu] at h
    convert h using 1
    funext x
    simp [g, Complex.mul_re, Complex.mul_im]
    ring
  have hge : ∀ᶠ x : ℝ in 𝓝[>] 0, (1/2:ℝ) ≤ x*g x :=
    (hscalar.eventually (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))).mono
      (fun _ hx => hx.le)
  have hrealder : ∀ᶠ x : ℝ in 𝓝[>] 0, HasDerivAt f (g x) x := by
    filter_upwards [hder] with x hx
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hx.const_mul u)
  obtain ⟨a,ha,hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hrealder.and hge)
  change 0<a at ha
  let b : ℝ := a/2
  have hb : 0<b := by dsimp [b]; positivity
  have hfb : Tendsto f (𝓝[>] 0) atBot := by
    apply tendsto_atBot_of_derivative_inv_lower hb (by norm_num : (0:ℝ)<1/2)
    · intro x hx
      exact (hall ⟨hx.1, hx.2.trans_lt (by dsimp [b]; linarith)⟩).1
    · intro x hx
      have h := (hall ⟨hx.1, hx.2.trans_lt (by dsimp [b]; linarith)⟩).2
      exact (div_le_iff₀ hx.1).mpr (by simpa [mul_comm] using h)
  have hneg : Tendsto (fun x => -f x) (𝓝[>] 0) atTop := tendsto_neg_atBot_atTop.comp hfb
  have hu0 : 0<‖u‖ := norm_pos_iff.mpr (inv_ne_zero hL)
  have hquot : Tendsto (fun x => (-f x)/‖u‖) (𝓝[>] 0) atTop :=
    hneg.atTop_div_const hu0
  apply tendsto_atTop_mono (fun x => ?_) hquot
  apply (div_le_iff₀ hu0).mpr
  have h := (neg_le_abs (f x)).trans (Complex.abs_re_le_norm (u*F x))
  simpa only [norm_mul,mul_comm] using h

end
end IsoProof
