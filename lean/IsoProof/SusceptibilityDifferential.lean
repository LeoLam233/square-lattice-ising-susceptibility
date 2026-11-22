import IsoProof.EnergyJetInterval
import IsoProof.BoundaryPrefactors
import IsoProof.JetTraceTransport
import IsoProof.ResonanceDense
import IsoProof.ResonanceNormalized

/-! Complete application of §5 to the literal reduced, physical and w-series
objects, consuming exactly the separately produced full-energy finite-jet
interval.  Final discharges this analytic input using EnergyJetRegularity, whose
construction combines the common-contour tail and finite-particle extensions. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem fullEnergySum_analyticOn_upperCollar (ν : Phase) (a b R : ℝ) :
    AnalyticOnNhd ℂ (fullEnergySum ν .positive) (upperCollar a b R) := by
  intro E hE
  exact fullEnergySum_positive_analyticOn ν E (Or.inl (show 0 < E.im from hE.2).ne')

theorem physicalEnergyChart_eq_temperatureChart (ν : Phase) (a b R : ℝ) :
    EqOn (physicalEnergyChart ν) (temperatureChart ν) (upperCollar a b R) := by
  intro E hE
  cases ν with
  | high => exact (temperatureChart_high_eq_exterior_inv hE.2).symm
  | low => exact (temperatureChart_low_eq_exterior hE.2).symm

theorem RegularEnergyJetInterval.reduced_boundary_chart {ν : Phase} {n : ℕ}
    (B : RegularEnergyJetInterval ν n) :
    Nonempty (SmoothSingularBoundaryChart (reducedSusceptibility ν)
      (positiveTemperatureDomain ν) n) := by
  obtain ⟨T⟩ := jetTraceOn_of_pullback_product n B.jet B.continuous B.agrees
    (temperatureChart_analyticOn_closedCollar ν B.left_pos B.right_lt_two).continuousOn
    (energy_analyticOn_chart_closedCollar ν)
    (normalization_analyticOn_chart_closedCollar ν B.left_pos B.right_lt_two)
    (fullEnergySum_analyticOn_upperCollar ν _ _ _)
    (fun E _ => energy_temperatureChart ν E)
    (fun _ _ => reduced_energy_product_germ ν)
  refine ⟨{
    left := B.left
    right := B.right
    height := B.height
    left_lt_right := B.left_lt_right
    height_pos := B.height_pos
    chart := temperatureChart ν
    chart_analytic := (temperatureChart_analyticOn_closedCollar ν B.left_pos B.right_lt_two).mono
      (upperCollar_subset_closed _ _ _)
    chart_injective := (temperatureChart_injective ν).injOn
    chart_mapsTo := temperatureChart_mapsTo_collar ν B.left_pos
    trace := T
    singularSet := primeSingularLevels n B.left B.right
    singular_subset := primeSingularLevels_subset n B.left B.right
    singular_dense := primeSingularLevels_dense n B.left_pos B.right_lt_two
    sharp := ?_ }⟩
  intro x hx
  obtain ⟨k,hnk,hsharp⟩ := reduced_sharp_on_primeSingularLevels ν n B.height_pos hx
  exact ⟨k,hnk,hsharp.congr_chart (physicalEnergyChart_eq_temperatureChart ν _ _ _)⟩

theorem RegularEnergyJetInterval.physical_boundary_chart {ν : Phase} {n : ℕ}
    (B : RegularEnergyJetInterval ν n) {J : ℝ} (hJ : 0 < J) :
    Nonempty (SmoothSingularBoundaryChart (physicalSusceptibility ν J)
      (positiveTemperatureDomain ν) n) := by
  obtain ⟨T⟩ := jetTraceOn_of_pullback_product n B.jet B.continuous B.agrees
    (temperatureChart_analyticOn_closedCollar ν B.left_pos B.right_lt_two).continuousOn
    (energy_analyticOn_chart_closedCollar ν)
    (physicalPrefactor_analyticOn_chart_closedCollar ν hJ B.left_pos B.right_lt_two)
    (fullEnergySum_analyticOn_upperCollar ν _ _ _)
    (fun E _ => energy_temperatureChart ν E)
    (fun _ _ => physical_energy_product_germ ν J)
  refine ⟨{
    left := B.left
    right := B.right
    height := B.height
    left_lt_right := B.left_lt_right
    height_pos := B.height_pos
    chart := temperatureChart ν
    chart_analytic := (temperatureChart_analyticOn_closedCollar ν B.left_pos B.right_lt_two).mono
      (upperCollar_subset_closed _ _ _)
    chart_injective := (temperatureChart_injective ν).injOn
    chart_mapsTo := temperatureChart_mapsTo_collar ν B.left_pos
    trace := T
    singularSet := primeSingularLevels n B.left B.right
    singular_subset := primeSingularLevels_subset n B.left B.right
    singular_dense := primeSingularLevels_dense n B.left_pos B.right_lt_two
    sharp := ?_ }⟩
  intro x hx
  obtain ⟨k,hnk,hsharp⟩ := physical_sharp_on_primeSingularLevels ν hJ n B.height_pos hx
  exact ⟨k,hnk,hsharp.congr_chart (physicalEnergyChart_eq_temperatureChart ν _ _ _)⟩

theorem nonzero_of_closedUpperCollar {a b R : ℝ} (ha : 0 < a) {E : ℂ}
    (hE : E ∈ closedUpperCollar a b R) : E ≠ 0 := by
  have hr : 0 < E.re := ha.trans hE.1.1.1
  intro hz
  simp only [hz,Complex.zero_re,lt_self_iff_false] at hr

theorem seriesCoordinate_analyticOn_closedUpperCollar {a b R : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℂ seriesCoordinate (closedUpperCollar a b R) :=
  fun _ hE => seriesCoordinate_analyticAt (nonzero_of_closedUpperCollar ha hE)

theorem seriesCoordinate_analyticOn_image_closedUpperCollar {a b R : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℂ seriesCoordinate (seriesCoordinate '' closedUpperCollar a b R) := by
  rintro w ⟨E,hE,rfl⟩
  exact seriesCoordinate_analyticAt (seriesCoordinate_ne_zero (nonzero_of_closedUpperCollar ha hE))

theorem seriesCoordinate_im_ne_zero {E : ℂ} (hE : E.im ≠ 0) :
    (seriesCoordinate E).im ≠ 0 := by
  have hE0 : E ≠ 0 := by intro hz; exact hE (by simp [hz])
  rw [seriesCoordinate,Complex.inv_im]
  apply div_ne_zero
  · simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hE
  · exact (Complex.normSq_pos.mpr (mul_ne_zero (by norm_num) hE0)).ne'

theorem normalizedSeries_energy_germ (ν : Phase) {E : ℂ} (hE : E ≠ 0) :
    normalizedSeries ν =ᶠ[𝓝 (seriesCoordinate E)]
      (fullEnergySum ν .positive ∘ seriesCoordinate)*(fun _ => 1) := by
  filter_upwards [eventually_ne_nhds (seriesCoordinate_ne_zero hE)] with w hw
  simpa only [Pi.mul_apply,Function.comp_apply,mul_one] using normalizedSeries_eq (ν := ν) hw

theorem RegularEnergyJetInterval.normalized_boundary_chart {ν : Phase} {n : ℕ}
    (B : RegularEnergyJetInterval ν n) :
    Nonempty (SmoothSingularBoundaryChart (normalizedSeries ν) normalizedSeriesDomain n) := by
  obtain ⟨T⟩ := jetTraceOn_of_pullback_product n B.jet B.continuous B.agrees
    (seriesCoordinate_analyticOn_closedUpperCollar B.left_pos).continuousOn
    (seriesCoordinate_analyticOn_image_closedUpperCollar B.left_pos)
    (show AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _ from fun _ _ => analyticAt_const)
    (fullEnergySum_analyticOn_upperCollar ν _ _ _)
    (fun E _ => seriesCoordinate_involutive E)
    (fun E hE => normalizedSeries_energy_germ ν
      (nonzero_of_closedUpperCollar B.left_pos (upperCollar_subset_closed _ _ _ hE)))
  refine ⟨{
    left := B.left
    right := B.right
    height := B.height
    left_lt_right := B.left_lt_right
    height_pos := B.height_pos
    chart := seriesCoordinate
    chart_analytic := (seriesCoordinate_analyticOn_closedUpperCollar B.left_pos).mono
      (upperCollar_subset_closed _ _ _)
    chart_injective := seriesCoordinate_involutive.injective.injOn
    chart_mapsTo := ?_
    trace := T
    singularSet := primeSingularLevels n B.left B.right
    singular_subset := primeSingularLevels_subset n B.left B.right
    singular_dense := primeSingularLevels_dense n B.left_pos B.right_lt_two
    sharp := ?_ }⟩
  · intro E hE
    exact Or.inl (seriesCoordinate_im_ne_zero (show 0 < E.im from hE.2).ne')
  · intro x hx
    exact normalized_sharp_on_primeSingularLevels ν n B.height_pos hx

theorem reduced_differentiallyTranscendental_of_energyJetIntervals (ν : Phase)
    (hjets : ∀ n : ℕ, 1 ≤ n → Nonempty (RegularEnergyJetInterval ν n))
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    DifferentiallyTranscendentalAt (reducedSusceptibility ν) (s : ℂ) := by
  apply differential_transcendentalAt_of_boundary_charts
    (positiveTemperatureDomain_isOpen ν) (positiveTemperatureDomain_isPreconnected ν)
    (reduced_positiveDomain_analyticOn ν) ?_ (realTemperature_mem_positiveDomain ν hs)
  intro n hn
  obtain ⟨B⟩ := hjets n hn
  exact B.reduced_boundary_chart

theorem physical_differentiallyTranscendental_of_energyJetIntervals (ν : Phase)
    (hjets : ∀ n : ℕ, 1 ≤ n → Nonempty (RegularEnergyJetInterval ν n))
    {J s : ℝ} (hJ : 0 < J) (hs : s ∈ realTemperatureDomain ν) :
    DifferentiallyTranscendentalAt (physicalSusceptibility ν J) (s : ℂ) := by
  apply differential_transcendentalAt_of_boundary_charts
    (positiveTemperatureDomain_isOpen ν) (positiveTemperatureDomain_isPreconnected ν)
    (physical_positiveDomain_analyticOn ν hJ) ?_ (realTemperature_mem_positiveDomain ν hs)
  intro n hn
  obtain ⟨B⟩ := hjets n hn
  exact B.physical_boundary_chart hJ

theorem normalized_differentiallyTranscendental_of_energyJetIntervals (ν : Phase)
    (hjets : ∀ n : ℕ, 1 ≤ n → Nonempty (RegularEnergyJetInterval ν n)) :
    DifferentiallyTranscendentalAt (normalizedSeries ν) 0 := by
  apply differential_transcendentalAt_of_boundary_charts normalizedSeriesDomain_isOpen
    normalizedSeriesDomain_isPreconnected (normalizedSeries_analyticOn ν)
    ?_ zero_mem_normalizedSeriesDomain
  intro n hn
  obtain ⟨B⟩ := hjets n hn
  exact B.normalized_boundary_chart

end
end IsoProof
