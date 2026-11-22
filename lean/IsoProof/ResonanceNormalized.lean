import IsoProof.ResonanceDense
import IsoProof.NormalizedSeries
import IsoProof.BoundaryCoordinates

/-! Sharp derivatives of the actual normalized w-series.  The proof uses
the analytic continued inverse of E=s+s⁻¹ followed by w↦1/(2w), applies the
proved finite Faà di Bruno transport, and identifies the resulting germ
with the normalized series including its fixed removable definition. -/
namespace IsoProof
noncomputable section
open Complex Filter Set Asymptotics
open IsingBulk.PrimeFamily
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The continued exterior temperature as a function of the w-coordinate. -/
def normalizedTemperatureInverse (w : ℂ) : ℂ :=
  temperatureChart .low (seriesCoordinate w)

def normalizedRadialPath (ζ : ℂ) (t : ℝ) : ℂ :=
  seriesCoordinate (radialEnergy ζ t)

theorem normalizedTemperatureInverse_analyticAt {w : ℂ} (hw : w≠0)
    (hE0 : 0<(seriesCoordinate w).re) (hE2 : (seriesCoordinate w).re<2) :
    AnalyticAt ℂ normalizedTemperatureInverse w :=
  (temperatureChart_analyticAt .low hE0 hE2).comp (seriesCoordinate_analyticAt hw)

theorem normalizedTemperatureInverse_deriv_ne_zero {w : ℂ} (hw : w≠0)
    (hE0 : 0<(seriesCoordinate w).re) (hE2 : (seriesCoordinate w).re<2) :
    deriv normalizedTemperatureInverse w≠0 := by
  have ht := temperatureChart_analyticAt .low hE0 hE2
  have hc := seriesCoordinate_analyticAt hw
  rw [show normalizedTemperatureInverse=temperatureChart .low∘seriesCoordinate from rfl,
    deriv_comp]
  · exact mul_ne_zero (temperatureChart_deriv_ne_zero .low hE0 hE2)
      (seriesCoordinate_deriv_ne_zero hw)
  · exact ht.differentiableAt
  · exact hc.differentiableAt

/-- The fixed normalized series is the same actual function germ as the
full temperature sum in the analytic inverse coordinate. -/
theorem normalizedSeries_local_eq_source (ν : Phase) {w : ℂ} (hw : w≠0) :
    normalizedSeries ν=ᶠ[𝓝 w](exteriorTemperatureSum ν∘normalizedTemperatureInverse) := by
  filter_upwards [eventually_ne_nhds hw] with u hu
  rw [normalizedSeries_eq hu]
  simp only [Function.comp_apply,exteriorTemperatureSum,normalizedTemperatureInverse,
    energy_temperatureChart]

theorem normalizedTemperatureInverse_radial {ζ : ℂ} (hζ : ‖ζ‖=1) (him : 0<ζ.im)
    {t : ℝ} (ht : 0<t) :
    normalizedTemperatureInverse (normalizedRadialPath ζ t)=radialTemperature ζ t := by
  simp only [normalizedTemperatureInverse,normalizedRadialPath]
  rw [seriesCoordinate_involutive]
  rw [temperatureChart_low_eq_exterior (radialEnergy_upper hζ him ht),
    exteriorEnergyInverse_radialEnergy hζ ht]

theorem admissible_normalizedRadialPath_tendsto {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    Tendsto (normalizedRadialPath (IsingBulk.PrimeFamily.angleRoot p a)) (𝓝[>] (0:ℝ))
      (𝓝 (seriesCoordinate ((2*Real.cos (angle p a):ℝ):ℂ))) := by
  have hgeo := admissible_root_geometry hp hp5 ha
  have hx0 : ((2*Real.cos (angle p a):ℝ):ℂ)≠0 := by
    exact_mod_cast hgeo.2.2.2.2.1.ne'
  exact (seriesCoordinate_analyticAt hx0).continuousAt.tendsto.comp
    ((admissible_radialEnergy_tendsto_upper hp hp5 ha).mono_right nhdsWithin_le_nhds)

/-- Both normalized series have genuinely divergent w-derivatives at the
same sharp order, with every lower w-derivative bounded. -/
theorem normalized_prime_sharp (ν : Phase) {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    SharpJetsAlong (normalizedSeries ν)
      (normalizedRadialPath (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) := by
  have hgeo := admissible_root_geometry hp hp5 ha
  have hx0 : ((2*Real.cos (angle p a):ℝ):ℂ)≠0 := by
    exact_mod_cast hgeo.2.2.2.2.1.ne'
  have hw0 := seriesCoordinate_ne_zero hx0
  have hE0 : 0<(seriesCoordinate (seriesCoordinate ((2*Real.cos (angle p a):ℝ):ℂ))).re := by
    rw [seriesCoordinate_involutive]
    exact hgeo.2.2.2.2.1
  have hE2 : (seriesCoordinate (seriesCoordinate ((2*Real.cos (angle p a):ℝ):ℂ))).re<2 := by
    rw [seriesCoordinate_involutive]
    exact hgeo.2.2.2.2.2
  have he : ∀ᶠ t in 𝓝[>] (0:ℝ),
      normalizedTemperatureInverse (normalizedRadialPath (IsingBulk.PrimeFamily.angleRoot p a) t)
        =radialTemperature (IsingBulk.PrimeFamily.angleRoot p a) t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact normalizedTemperatureInverse_radial hgeo.1 hgeo.2.2.1 ht
  have hj (j : ℕ) :
      (fun t=>iteratedDeriv j (exteriorTemperatureSum ν)
        (normalizedTemperatureInverse (normalizedRadialPath (IsingBulk.PrimeFamily.angleRoot p a) t)))
      =ᶠ[𝓝[>] 0] (fun t=>iteratedDeriv j (exteriorTemperatureSum ν)
        (radialTemperature (IsingBulk.PrimeFamily.angleRoot p a) t)) :=
    he.mono (fun _ h=>congrArg _ h)
  have hh := exterior_prime_sharp ν hp hp5 ha
  have han : ∀ᶠ t in 𝓝[>] (0:ℝ),AnalyticAt ℂ (exteriorTemperatureSum ν)
      (normalizedTemperatureInverse (normalizedRadialPath (IsingBulk.PrimeFamily.angleRoot p a) t)) := by
    filter_upwards [self_mem_nhdsWithin,he] with t ht heq
    rw [heq]
    exact exteriorTemperatureSum_analyticAt ν (radialTemperature_exterior hgeo.1 ht)
  have hcomp : SharpJetsAlong (exteriorTemperatureSum ν∘normalizedTemperatureInverse)
      (normalizedRadialPath (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) :=
    sharp_jets_comp (admissible_normalizedRadialPath_tendsto hp hp5 ha)
      (normalizedTemperatureInverse_analyticAt hw0 hE0 hE2)
      (normalizedTemperatureInverse_deriv_ne_zero hw0 hE0 hE2) (phaseCriticalOrder ν p) han
      (hh.1.congr' ((hj _).symm.fun_comp norm))
      (fun j hlt=>(hh.2 j hlt).congr' (hj j).symm Filter.EventuallyEq.rfl)
  apply hcomp.congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply (normalizedSeries_local_eq_source ν ?_).symm
  apply seriesCoordinate_ne_zero
  intro hz
  have hi := radialEnergy_upper hgeo.1 hgeo.2.2.1 ht
  norm_num [hz] at hi

/-- The normalized sharp derivatives packaged with the same true upper
energy path used for the two physical susceptibilities. -/
theorem normalized_prime_sharp_boundary (ν : Phase) {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) {L U R : ℝ} (hR : 0<R)
    (hx : 2*Real.cos (angle p a)∈Ioo L U) :
    SharpBoundaryApproach (normalizedSeries ν) seriesCoordinate L U R
      (2*Real.cos (angle p a)) (phaseCriticalOrder ν p) := by
  have hs := normalized_prime_sharp ν hp hp5 ha
  refine ⟨radialEnergy (IsingBulk.PrimeFamily.angleRoot p a),
    admissible_radialEnergy_tendsto_collar hp hp5 ha hR hx,hs.1,?_⟩
  intro j hj
  have hb := hs.2 j hj
  simpa only [NormBoundedAlong,Asymptotics.isBigO_iff,norm_one,mul_one,normalizedRadialPath] using hb

theorem normalized_sharp_on_primeSingularLevels (ν : Phase) (r : ℕ) {L U R : ℝ}
    (hR : 0<R) {x : ℝ} (hx : x∈primeSingularLevels r L U) :
    ∃ k : ℕ,r≤k ∧ SharpBoundaryApproach (normalizedSeries ν)
      seriesCoordinate L U R x k := by
  obtain ⟨p,j,hp,hp5,hj,hk,hxeq⟩ := phaseCriticalOrder_high_on_primeSingularLevels ν hx
  refine ⟨phaseCriticalOrder ν p,hk.le,?_⟩
  rw [hxeq]
  exact normalized_prime_sharp_boundary ν hp hp5 hj hR (hxeq ▸ hx.1)

end
end IsoProof
