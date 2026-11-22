import IsoProof.SiteSummation
import IsingBulk.First.DominatedAnalyticIntegral

/-! Repeated differentiation of actual normally convergent series, with
an arbitrary index type (in particular particle number times lattice site).
Only the order-zero local majorant is assumed; Cauchy constructs all local
derivative majorants before any differentiation of the sum is performed. -/
namespace IsoProof
noncomputable section
open Set Filter Metric
open scoped Topology
set_option maxHeartbeats 800000

def LocalSummableBound {ι : Type*} (f : ι → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∃ r > 0, ∃ M : ι → ℝ, Summable M ∧ closedBall z r ⊆ U ∧
    ∀ i w, w ∈ closedBall z r → ‖f i w‖ ≤ M i

theorem localSummableBound_of_uniform {ι : Type*} {f : ι → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) {M : ι → ℝ} (hM : Summable M)
    (hb : ∀ i z, z ∈ U → ‖f i z‖ ≤ M i) : LocalSummableBound f U := by
  intro z hz
  obtain ⟨r,hr,hs⟩ := Metric.isOpen_iff.mp hU z hz
  have hsub : closedBall z (r/2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hs
  exact ⟨r/2,half_pos hr,M,hM,hsub,fun i w hw => hb i w (hsub hw)⟩

theorem local_normal_jet_majorant {ι : Type*} {f : ι → ℂ → ℂ} {U : Set ℂ}
    (ha : ∀ i, AnalyticOnNhd ℂ (f i) U) (hb : LocalSummableBound f U)
    (j : ℕ) {z : ℂ} (hz : z ∈ U) :
    ∃ r > 0, ∃ M : ι → ℝ, Summable M ∧ ball z r ⊆ U ∧
      ∀ i w, w ∈ ball z r → ‖iteratedDeriv j (f i) w‖ ≤ M i := by
  obtain ⟨r,hr,M,hM,hs,hbound⟩ := hb z hz
  let B : ι → ℝ := fun i => (j.factorial : ℝ)*M i/(r/2)^j
  have hB : Summable B := by
    apply (hM.mul_left ((j.factorial : ℝ)/(r/2)^j)).congr
    intro i
    dsimp [B]
    ring
  refine ⟨r/2,half_pos hr,B,hB,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))).trans hs,?_⟩
  intro i w hw
  apply IsingBulk.First.cauchy_bound_on_subdisk
    (U := closedBall z r) (fun y hy => ha i y (hs hy)) (hbound i) (half_pos hr) ?_ j
  apply closedBall_subset_closedBall'
  have hdist := mem_ball.mp hw
  linarith

theorem norm_iteratedDeriv_summable_of_local_bound {ι : Type*}
    {f : ι → ℂ → ℂ} {U : Set ℂ} (ha : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hb : LocalSummableBound f U) (j : ℕ) {z : ℂ} (hz : z ∈ U) :
    Summable (fun i => ‖iteratedDeriv j (f i) z‖) := by
  obtain ⟨r,hr,M,hM,_hs,hbound⟩ := local_normal_jet_majorant ha hb j hz
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => hbound i z (mem_ball_self hr))

theorem analyticOnNhd_tsum_of_local_bound {ι : Type*}
    {f : ι → ℂ → ℂ} {U : Set ℂ} (ha : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hb : LocalSummableBound f U) : AnalyticOnNhd ℂ (fun z => ∑' i, f i z) U := by
  intro z hz
  obtain ⟨r,hr,M,hM,hs,hbound⟩ := hb z hz
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (fun i w hw => (ha i w (hs (ball_subset_closedBall hw))).differentiableAt.differentiableWithinAt)
    isOpen_ball (fun i w hw => hbound i w (ball_subset_closedBall hw))
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ball_mem_nhds z hr] with w hw
  exact hd.differentiableAt (isOpen_ball.mem_nhds hw)

theorem iteratedDeriv_tsum_of_local_bound {ι : Type*}
    {f : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : ∀ i, AnalyticOnNhd ℂ (f i) U) (hb : LocalSummableBound f U)
    (j : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv j (fun w => ∑' i, f i w) z = ∑' i, iteratedDeriv j (f i) z := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
    have heq : iteratedDeriv j (fun w => ∑' i, f i w) =ᶠ[𝓝 z]
        fun w => ∑' i, iteratedDeriv j (f i) w := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih hw
    obtain ⟨r,hr,M,hM,hs,hbound⟩ := local_normal_jet_majorant ha hb j hz
    have hh := Complex.hasSum_deriv_of_summable_norm hM
      (fun i w hw => (IsingBulk.First.analyticAt_iteratedDeriv (ha i w (hs hw)) j).differentiableAt.differentiableWithinAt)
      isOpen_ball hbound (mem_ball_self hr)
    rw [iteratedDeriv_succ,heq.deriv_eq]
    simpa only [iteratedDeriv_succ] using hh.tsum_eq.symm

theorem site_lattice_local_bound (N : ℕ) (hN : 0 < N) :
    LocalSummableBound (fun p : ℤ × ℤ => siteCoefficient N p.1.natAbs p.2) energyDomain := by
  intro E hE
  obtain ⟨r,hr,hs⟩ := energyDomain_closedBall hE
  obtain ⟨M,hM,hbound⟩ := compact_site_summable_majorant N hN (isCompact_closedBall E r) hs
  exact ⟨r,hr,M,hM,hs,hbound⟩

/-- Every derivative of the concrete positive-sign particle integral is the
absolutely convergent sum of the actual site derivatives in the whole slit. -/
theorem particleCoefficient_jet_eq_site_tsum (N : ℕ) (hN : 0 < N) (j : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    iteratedDeriv j (particleCoefficient .positive N) E =
      ∑' p : ℤ × ℤ, iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E := by
  have he : particleCoefficient .positive N =ᶠ[𝓝 E]
      fun z => ∑' p : ℤ × ℤ, siteCoefficient N p.1.natAbs p.2 z := by
    filter_upwards [isOpen_energyDomain.mem_nhds hE] with z hz
    exact particleCoefficient_eq_site_tsum_complex N hN hz
  rw [he.iteratedDeriv_eq j]
  exact iteratedDeriv_tsum_of_local_bound isOpen_energyDomain
    (fun p _ h => siteCoefficient_analyticAt N p.1.natAbs p.2 h)
    (site_lattice_local_bound N hN) j hE

end
end IsoProof
