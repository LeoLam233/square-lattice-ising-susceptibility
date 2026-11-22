import IsoProof.IntegralsSignedVertical
import IsoProof.SiteSummation

/-! Formula (3), both signs and all positive particle numbers, on the full
complex energy slit.  The same compact spatial majorant proves absolute
summability and holomorphy before the real Fourier identity is continued. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped BigOperators Topology

/-- Multiplication by the actual lattice character preserves the proved
absolute spatial convergence. -/
theorem signed_site_lattice_norm_summable (σ : Sign) (N : ℕ) (hN : 0 < N)
    {E : ℂ} (hE : E ∈ energyDomain) :
    Summable (fun p : ℤ × ℤ =>
      ‖latticeSign σ p * siteCoefficient N p.1.natAbs p.2 E‖) := by
  simpa only [norm_mul,latticeSign_norm,one_mul] using
    site_lattice_norm_summable N hN hE

theorem signed_site_lattice_sum_analyticAt (σ : Sign) (N : ℕ) (hN : 0 < N)
    {E : ℂ} (hE : E ∈ energyDomain) :
    AnalyticAt ℂ (fun z => ∑' p : ℤ × ℤ,
      latticeSign σ p * siteCoefficient N p.1.natAbs p.2 z) E := by
  obtain ⟨r,hr,hD⟩ := energyDomain_closedBall hE
  obtain ⟨M,hM,hbound⟩ := compact_site_summable_majorant N hN
    (isCompact_closedBall E r) hD
  have hbound' (p : ℤ × ℤ) (z : ℂ) (hz : z ∈ Metric.ball E r) :
      ‖latticeSign σ p * siteCoefficient N p.1.natAbs p.2 z‖ ≤ M p := by
    simpa only [norm_mul,latticeSign_norm,one_mul] using
      hbound p z (Metric.ball_subset_closedBall hz)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (fun p z hz => (analyticAt_const.mul (siteCoefficient_analyticAt N p.1.natAbs p.2
      (hD (Metric.ball_subset_closedBall hz)))).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball hbound'
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Metric.ball_mem_nhds E hr] with z hz
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)

/-- Literal formula (3) for both signed constrained integrals and the entire
integer lattice.  In particular the even-particle negative channel is covered
by Fourier inversion at pi, rather than inferred from an odd reflection law. -/
theorem particleCoefficient_eq_signed_site_tsum_complex (σ : Sign)
    (N : ℕ) (hN : 0 < N) {E : ℂ} (hE : E ∈ energyDomain) :
    particleCoefficient σ N E =
      ∑' p : ℤ × ℤ, latticeSign σ p * siteCoefficient N p.1.natAbs p.2 E :=
  energy_eq_of_real_temperature
    (fun _ h => particleCoefficient_analyticAt σ N h)
    (fun _ h => signed_site_lattice_sum_analyticAt σ N hN h)
    (fun _ ht => particleCoefficient_eq_signed_site_tsum_real σ hN ht) hE

/-- The same theorem printed using the manuscript's integer exponent. -/
theorem particleCoefficient_eq_character_site_tsum_complex (σ : Sign)
    (N : ℕ) (hN : 0 < N) {E : ℂ} (hE : E ∈ energyDomain) :
    particleCoefficient σ N E =
      ∑' p : ℤ × ℤ, signValue σ ^ (p.1+p.2) * siteCoefficient N p.1.natAbs p.2 E := by
  rw [particleCoefficient_eq_signed_site_tsum_complex σ N hN hE]
  apply tsum_congr
  intro p
  rw [latticeSign_eq_zpow]

end
end IsoProof
