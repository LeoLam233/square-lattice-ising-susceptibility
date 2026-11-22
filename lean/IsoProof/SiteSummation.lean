import IsoProof.SiteInteriorBounds
import IsoProof.ResonanceCoordinate

/-! Actual full-lattice summation at complex energy.  The spatial series is
normally convergent on compact subsets of the energy slit, so its identity
with the literal particle integral follows from the full real-temperature
identity. -/
namespace IsoProof
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.HT.Contour
set_option maxHeartbeats 800000

theorem compact_site_summable_majorant (N : ℕ) (hN : 0 < N)
    {K : Set ℂ} (hK : IsCompact K) (hD : K ⊆ energyDomain) :
    ∃ M : (ℤ × ℤ) → ℝ, Summable M ∧ ∀ p E, E ∈ K →
      ‖siteCoefficient N p.1.natAbs p.2 E‖ ≤ M p := by
  obtain ⟨C,q,_hC,hq,hq1,hbound⟩ := compact_site_geometric_bound N hN hK hD
  have hsum := physical_real_twoSided_geometric_summable hq.le hq1
  refine ⟨fun p => C*(q^p.1.natAbs*q^p.2.natAbs),
    (hsum.mul_of_nonneg hsum (fun _ => pow_nonneg hq.le _)
      (fun _ => pow_nonneg hq.le _)).mul_left C,?_⟩
  intro p E hE
  exact hbound E hE p

theorem site_lattice_norm_summable (N : ℕ) (hN : 0 < N)
    {E : ℂ} (hE : E ∈ energyDomain) :
    Summable (fun p : ℤ × ℤ => ‖siteCoefficient N p.1.natAbs p.2 E‖) := by
  obtain ⟨M,hM,hb⟩ := compact_site_summable_majorant N hN (isCompact_singleton (x := E))
    (by intro z hz; simpa only [mem_singleton_iff.mp hz] using hE)
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hb p E (mem_singleton E))

theorem energyDomain_closedBall {E : ℂ} (hE : E ∈ energyDomain) :
    ∃ r > 0, Metric.closedBall E r ⊆ energyDomain := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_energyDomain E hE
  exact ⟨r/2,half_pos hr,(Metric.closedBall_subset_ball (by linarith)).trans hball⟩

theorem site_lattice_sum_analyticAt (N : ℕ) (hN : 0 < N)
    {E : ℂ} (hE : E ∈ energyDomain) :
    AnalyticAt ℂ (fun z => ∑' p : ℤ × ℤ, siteCoefficient N p.1.natAbs p.2 z) E := by
  obtain ⟨r,hr,hD⟩ := energyDomain_closedBall hE
  obtain ⟨M,hM,hbound⟩ := compact_site_summable_majorant N hN
    (isCompact_closedBall E r) hD
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (fun p z hz => (siteCoefficient_analyticAt N p.1.natAbs p.2
      (hD (Metric.ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun p z hz => hbound p z (Metric.ball_subset_closedBall hz))
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Metric.ball_mem_nhds E hr] with z hz
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)

theorem particleCoefficient_analyticAt (σ : Sign) (N : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) : AnalyticAt ℂ (particleCoefficient σ N) E := by
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec hE
  have hs0 : exteriorEnergyInverse E ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hs))
  have hs1 : exteriorEnergyInverse E ≠ 1 := by intro h; simp [h] at hs
  have hsm1 : exteriorEnergyInverse E ≠ -1 := by intro h; simp [h] at hs
  rw [← he]
  apply analyticAt_energyFunction_of_composition hs0 hs1 hsm1
  cases σ with
  | positive =>
    apply (IsingBulk.HT22.Physical.signedCoefficient_analyticAt false N hs).congr
    exact Filter.Eventually.of_forall (fun u => (particleCoefficient_positive_energy N u).symm)
  | negative =>
    apply (IsingBulk.HT22.Physical.signedCoefficient_analyticAt true N hs).congr
    exact Filter.Eventually.of_forall (fun u => (particleCoefficient_negative_energy N u).symm)

/-- Formula (3), positive sign, throughout the full complex energy slit.
The convergent lattice sum is not a definition of the particle coefficient. -/
theorem particleCoefficient_eq_site_tsum_complex (N : ℕ) (hN : 0 < N)
    {E : ℂ} (hE : E ∈ energyDomain) :
    particleCoefficient .positive N E =
      ∑' p : ℤ × ℤ, siteCoefficient N p.1.natAbs p.2 E :=
  energy_eq_of_real_temperature
    (fun _ h => particleCoefficient_analyticAt .positive N h)
    (fun _ h => site_lattice_sum_analyticAt N hN h)
    (fun _ ht => particleCoefficient_eq_site_tsum hN ht) hE

end
end IsoProof
