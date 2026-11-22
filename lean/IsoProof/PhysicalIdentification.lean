import IsoProof.IntegralsCosine
import IsingBulk.HT22.Physical.JointLatticeSummability

/-!
The only statistical-mechanical premises in this file are the real-temperature
sitewise form-factor identity, spin-square normalization, spin reversal, and
energy-field fluctuation response. They contain no complex continuation,
boundary estimate, or differential-transcendence conclusion.

Sources: Orrick--Nickel--Guttmann--Perk (2001), (1.7)--(1.10), (3.13),
(3.17)--(3.20), (4.1)--(4.2); Palmer--Tracy (1981), Theorem 5.0.
All site/particle summation exchanges used for identification are proved.
-/
namespace IsoProof
noncomputable section
open scoped BigOperators Topology
open IsingBulk.HT.Contour IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors

abbrev LatticeSite := ℤ × ℤ

def exteriorTemperature : Phase → ℝ → ℝ
  | .high, s => s⁻¹
  | .low, s => s

theorem exteriorTemperature_gt_one (ν : Phase) {s : ℝ}
    (hs : s ∈ realTemperatureDomain ν) : 1 < exteriorTemperature ν s := by
  cases ν with
  | high => exact (one_lt_inv₀ hs.1).mpr hs.2
  | low => exact hs

theorem energy_exteriorTemperature (ν : Phase) (s : ℝ) :
    energy (exteriorTemperature ν s : ℂ) = energy (s : ℂ) := by
  cases ν with
  | high => simpa only [exteriorTemperature, Complex.ofReal_inv] using energy_inv (s : ℂ)
  | low => rfl

theorem particleOrder_positive (ν : Phase) (n : ℕ) : 0 < particleOrder ν n := by
  cases ν <;> simp only [particleOrder] <;> omega

/-- Both particle parities are absolutely summable jointly with the whole
integer lattice. This is an interior real-temperature estimate only. -/
theorem all_particle_lattice_norm_summable (ν : Phase) {t : ℝ} (ht : 1 < t) :
    Summable (fun p : ℕ × LatticeSite =>
      ‖physicalFullLatticeCoefficient (particleOrder ν p.1) t p.2‖) := by
  cases ν with
  | high => exact IsingBulk.HT22.Physical.full_odd_lattice_norm_summable ht
  | low =>
    have hx : 0 < Real.arsinh t := Real.arsinh_pos_iff.mpr (by linarith)
    have hp : realProduct 1 (Real.arsinh t) ≠ 1 := by
      rw [realProduct_one, Real.sinh_arsinh]
      nlinarith
    have hs := selected_particle_lattice_norm_summable (by norm_num : (0 : ℝ) < 1)
      hx hp (fun n => 2*(n+1)) (fun _ => by omega)
      (fun C hC => (hadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective)
    simpa only [particleOrder, realB_one hx, realC_one hx, Real.sinh_arsinh,
      latticeCoefficient_isotropic] using hs

/-- Same joint absolute convergence for the new literal E-coordinate site
integrals, over the full real interval of either phase. -/
theorem actual_site_particle_norm_summable (ν : Phase) {s : ℝ}
    (hs : s ∈ realTemperatureDomain ν) :
    Summable (fun p : ℕ × LatticeSite =>
      ‖siteCoefficient (particleOrder ν p.1) p.2.1.natAbs p.2.2 (energy (s : ℂ))‖) := by
  have ht := exteriorTemperature_gt_one ν hs
  have h := all_particle_lattice_norm_summable ν ht
  apply h.congr
  intro p
  rw [← energy_exteriorTemperature ν s, siteCoefficient_energy_real _ _ _ ht]
  rfl

/-- The exact particle/site exchange, now with the paper's E coordinate. -/
theorem fullEnergySum_eq_siteFirst (ν : Phase) {s : ℝ}
    (hs : s ∈ realTemperatureDomain ν) :
    fullEnergySum ν .positive (energy (s : ℂ)) =
      ∑' v : LatticeSite, ∑' n : ℕ,
        siteCoefficient (particleOrder ν n) v.1.natAbs v.2 (energy (s : ℂ)) := by
  have habs := actual_site_particle_norm_summable ν hs
  have ht := exteriorTemperature_gt_one ν hs
  have hc (n : ℕ) : particleCoefficient .positive (particleOrder ν n) (energy (s : ℂ)) =
      ∑' v : LatticeSite,
        siteCoefficient (particleOrder ν n) v.1.natAbs v.2 (energy (s : ℂ)) := by
    rw [← energy_exteriorTemperature ν s]
    exact particleCoefficient_eq_site_tsum (particleOrder_positive ν n) ht
  unfold fullEnergySum
  calc
    _ = ∑' n : ℕ, ∑' v : LatticeSite,
        siteCoefficient (particleOrder ν n) v.1.natAbs v.2 (energy (s : ℂ)) := tsum_congr hc
    _ = _ := (Summable.tsum_comm (f := fun (n : ℕ) (v : LatticeSite) =>
      siteCoefficient (particleOrder ν n) v.1.natAbs v.2 (energy (s : ℂ))) habs.of_norm).symm

/-- M² is zero in the disordered phase; in the plus/minus ordered pure phases
it is the positive real fourth root prescribed by the paper. -/
def spontaneousSquare (ν : Phase) (s : ℝ) : ℂ :=
  match ν with
  | .high => 0
  | .low => normalization .low (s : ℂ)

def connectedCorrelation (ν : Phase) (corr : ℝ → LatticeSite → ℂ)
    (s : ℝ) (v : LatticeSite) : ℂ := corr s v - spontaneousSquare ν s

/-- Only published REAL TEMPERATURE sitewise data. No infinite lattice sum
or analyticity/continuation/convergence statement is an input field. -/
structure PublishedSiteInput (ν : Phase) (corr : ℝ → LatticeSite → ℂ) : Prop where
  spin_square : ∀ s : ℝ, s ∈ realTemperatureDomain ν → corr s (0,0) = 1
  sitewise : ∀ s : ℝ, s ∈ realTemperatureDomain ν → ∀ v : LatticeSite,
    connectedCorrelation ν corr s v = normalization ν (s : ℂ) *
      ∑' n : ℕ, publishedCosineSiteCoefficient (particleOrder ν n) v.1.natAbs v.2
        (exteriorTemperature ν s)

/-- The published cosine multiplier is converted by a proved reflection
identity, not silently absorbed into a stronger source premise. -/
theorem PublishedSiteInput.sitewise_fourier {ν : Phase} {corr : ℝ → LatticeSite → ℂ}
    (hphys : PublishedSiteInput ν corr) (s : ℝ) (hs : s ∈ realTemperatureDomain ν)
    (v : LatticeSite) :
    connectedCorrelation ν corr s v = normalization ν (s : ℂ) *
      ∑' n : ℕ, siteCoefficient (particleOrder ν n) v.1.natAbs v.2 (energy (s : ℂ)) := by
  rw [hphys.sitewise s hs v]
  congr 1
  apply tsum_congr
  intro n
  rw [← siteCoefficient_energy_real_eq_cosine _ _ _ (exteriorTemperature_gt_one ν hs),
    energy_exteriorTemperature]

def realReducedSum (ν : Phase) (corr : ℝ → LatticeSite → ℂ) (s : ℝ) : ℂ :=
  ∑' v : LatticeSite, connectedCorrelation ν corr s v

/-- Absolute full-lattice convergence is proved from the literal joint bound
and the real sitewise published identity. -/
theorem connectedCorrelation_norm_summable (ν : Phase)
    {corr : ℝ → LatticeSite → ℂ} (hphys : PublishedSiteInput ν corr)
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    Summable (fun v : LatticeSite => ‖connectedCorrelation ν corr s v‖) := by
  have habs := actual_site_particle_norm_summable ν hs
  have hmajor : Summable (fun v : LatticeSite => ‖normalization ν (s : ℂ)‖ *
      ∑' n : ℕ, ‖siteCoefficient (particleOrder ν n) v.1.natAbs v.2 (energy (s : ℂ))‖) := by
    simpa only [Prod.swap] using habs.prod_symm.prod.mul_left ‖normalization ν (s : ℂ)‖
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro v
  rw [hphys.sitewise_fourier s hs v, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_tsum_le_tsum_norm (habs.prod_symm.prod_factor v)

/-- Complete real-temperature identification. No range such as s>2 or
0<s<1/16 occurs: the quantifier is the paper's full physical interval. -/
theorem realReducedSum_eq_reducedSusceptibility (ν : Phase)
    {corr : ℝ → LatticeSite → ℂ} (hphys : PublishedSiteInput ν corr)
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    realReducedSum ν corr s = reducedSusceptibility ν (s : ℂ) := by
  have hs0 : (s : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    cases ν with
    | high => exact hs.1.ne'
    | low => exact (lt_trans zero_lt_one hs).ne'
  simp only [realReducedSum, reducedSusceptibility, hs0, and_false, ite_false]
  simp_rw [hphys.sitewise_fourier s hs]
  rw [tsum_mul_left, fullEnergySum_eq_siteFirst ν hs]

/-- The origin contributes 1 at high temperature and 1-M² in a pure ordered
phase; no individual particle coefficient is normalized to 1. -/
theorem realReducedSum_origin_add_offOrigin (ν : Phase)
    {corr : ℝ → LatticeSite → ℂ} (hphys : PublishedSiteInput ν corr)
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    realReducedSum ν corr s = (1-spontaneousSquare ν s) +
      ∑' v : LatticeSite, if v = (0,0) then 0 else connectedCorrelation ν corr s v := by
  have h := (connectedCorrelation_norm_summable ν hphys hs).of_norm.tsum_eq_add_tsum_ite (0,0)
  simpa only [realReducedSum, connectedCorrelation, hphys.spin_square s hs] using h

/-- Spin reversal is a real-temperature statement about the two pure states.
It immediately gives equality of their connected bulk sums after convergence
has already been established separately above. -/
theorem spin_reversal_sum_eq {corrPlus corrMinus : ℝ → LatticeSite → ℂ}
    (hspin : ∀ s : ℝ, 1 < s → ∀ v : LatticeSite, corrMinus s v = corrPlus s v)
    {s : ℝ} (hs : 1 < s) :
    realReducedSum .low corrMinus s = realReducedSum .low corrPlus s := by
  apply tsum_congr
  intro v
  simp only [connectedCorrelation, hspin s hs v]

def realInverseTemperature (J s : ℝ) : ℝ := Real.arsinh s/(2*J)

def realPhysicalSum (ν : Phase) (J : ℝ) (corr : ℝ → LatticeSite → ℂ)
    (s : ℝ) : ℂ := (realInverseTemperature J s : ℂ) * realReducedSum ν corr s

theorem realPhysicalSum_identification (ν : Phase) (J : ℝ)
    {corr : ℝ → LatticeSite → ℂ} (hphys : PublishedSiteInput ν corr)
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    realPhysicalSum ν J corr s =
      (realInverseTemperature J s : ℂ) * reducedSusceptibility ν (s : ℂ) := by
  rw [realPhysicalSum, realReducedSum_eq_reducedSusceptibility ν hphys hs]

theorem real_temperature_coordinate {J s : ℝ} (hJ : 0 < J) (hs : 0 < s) :
    0 < realInverseTemperature J s ∧
      Real.sinh (2*realInverseTemperature J s*J) = s := by
  refine ⟨div_pos (Real.arsinh_pos_iff.mpr hs) (by positivity), ?_⟩
  have hJ0 : J ≠ 0 := hJ.ne'
  have he : 2*realInverseTemperature J s*J = Real.arsinh s := by
    unfold realInverseTemperature
    field_simp
  rw [he, Real.sinh_arsinh]

/-- The differentiation convention for an energy-valued magnetic field.
The low-temperature response is from positive field in the plus state. -/
def HasEnergyFieldResponse (ν : Phase) (m : ℝ → ℂ) (χ : ℂ) : Prop :=
  match ν with
  | .high => HasDerivAt m χ 0
  | .low => HasDerivWithinAt m χ (Set.Ioi 0) 0

/-- The real fluctuation-response identification (ONGP (1.7)--(1.10)) is a
separate physical input from the zero-field sitewise expansion. -/
structure PublishedEnergyResponse (ν : Phase) (J : ℝ)
    (corr : ℝ → LatticeSite → ℂ) (magnetization : ℝ → ℝ → ℂ) : Prop where
  response : ∀ s : ℝ, s ∈ realTemperatureDomain ν →
    HasEnergyFieldResponse ν (magnetization s) (realPhysicalSum ν J corr s)

/-- The derivative of physical magnetization equals beta times the proved
literal analytic-series value on the entire real temperature interval. -/
theorem energyFieldResponse_identification (ν : Phase) (J : ℝ)
    {corr : ℝ → LatticeSite → ℂ} {magnetization : ℝ → ℝ → ℂ}
    (hsite : PublishedSiteInput ν corr)
    (hresponse : PublishedEnergyResponse ν J corr magnetization)
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    HasEnergyFieldResponse ν (magnetization s)
      ((realInverseTemperature J s : ℂ)*reducedSusceptibility ν (s : ℂ)) := by
  rw [← realPhysicalSum_identification ν J hsite hs]
  exact hresponse.response s hs

end
end IsoProof
