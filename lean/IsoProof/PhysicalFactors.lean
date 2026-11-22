import IsoProof.PhysicalHolomorphy
import IsingBulk.Preferred22.Prefactors
import IsingBulk.Final.InverseTemperatureLocalBranches
import IsingBulk.Final.InverseTemperatureSheets

/-! Analytic and nonzero physical multipliers at the nonaxis singularity
charts. The fourth-root normalization and inverse-sinh beta are distinct
functions with distinct branch laws throughout. -/
namespace IsoProof
noncomputable section
open Filter Set
open scoped Topology

theorem normalization_high_eq_exteriorPrefactor_inverse (s : ℂ) :
    normalization .high s = IsingBulk.HT.Final.exteriorPrefactor s⁻¹ := by
  rw [← IsingBulk.HT.Final.interiorPrefactor_inv s⁻¹, inv_inv]
  rfl

theorem normalization_regular_at_unit_nonaxis (ν : Phase) {z : ℂ}
    (hz : ‖z‖=1) (hfour : z^4 ≠ 1) :
    AnalyticAt ℂ (normalization ν) z ∧ normalization ν z ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  cases ν with
  | high =>
    have hzi : ‖z⁻¹‖=1 := by rw [norm_inv, hz, inv_one]
    have hfourI : (z⁻¹)^4 ≠ 1 := by
      intro h
      apply hfour
      simpa only [inv_pow, inv_inv, inv_one] using congrArg Inv.inv h
    obtain ⟨ha, hn⟩ := IsingBulk.HT.Final.exteriorPrefactor_regular_at_unit_nonaxis hzi hfourI
    have he : normalization .high = fun s => IsingBulk.HT.Final.exteriorPrefactor s⁻¹ :=
      funext normalization_high_eq_exteriorPrefactor_inverse
    rw [he]
    exact ⟨ha.comp (f := fun s : ℂ => s⁻¹) (analyticAt_id.inv hz0), hn⟩
  | low =>
    have he : normalization .low = IsingBulk.Preferred22.magnetizationSquared :=
      funext normalization_low_eq_magnetization
    rw [he]
    exact ⟨IsingBulk.Preferred22.magnetizationSquared_analyticAt_unit_nonaxis hz hfour,
      IsingBulk.Preferred22.magnetizationSquared_ne_zero_at_unit_nonaxis hz hfour⟩

/-- Actual canonical beta normalization, regular on the complete nonimaginary
part of the unit circle. It is not a fourth root. -/
theorem canonical_beta_regular {J : ℝ} (hJ : 0 < J) {z : ℂ}
    (hz : ‖z‖=1) (hre : z.re ≠ 0) :
    AnalyticAt ℂ (IsingBulk.Final.inverseTemperatureBranch J) z ∧
      IsingBulk.Final.inverseTemperatureBranch J z ≠ 0 :=
  IsingBulk.HT.Final.inverseTemperatureBranch_regular_unit_nonimaginary hJ hz hre

/-- The actual multiplier for susceptibility as opposed to the reduced sum. -/
def physicalPrefactor (ν : Phase) (J : ℝ) (s : ℂ) : ℂ :=
  IsingBulk.Final.inverseTemperatureBranch J s * normalization ν s

theorem physicalPrefactor_regular_at_unit_nonaxis (ν : Phase) {J : ℝ} (hJ : 0 < J)
    {z : ℂ} (hz : ‖z‖=1) (hfour : z^4 ≠ 1) (hre : z.re ≠ 0) :
    AnalyticAt ℂ (physicalPrefactor ν J) z ∧ physicalPrefactor ν J z ≠ 0 := by
  obtain ⟨ha, hn⟩ := normalization_regular_at_unit_nonaxis ν hz hfour
  obtain ⟨hb, hbn⟩ := canonical_beta_regular hJ hz hre
  exact ⟨hb.mul ha, mul_ne_zero hbn hn⟩

/-- Nonvanishing is proved for every genuine inverse-temperature sheet. -/
theorem beta_branch_ne_zero {J : ℝ} {z b : ℂ} (hz : z ≠ 0)
    (hrel : Complex.sinh (2*(J:ℂ)*b)=z) : b ≠ 0 :=
  IsingBulk.Final.inverseTemperature_nonzero_of_relation hz hrel

/-- Branch existence and regularity are constructed internally at all
nonbranch unit-circle points. -/
theorem beta_branch_exists_at_unit {J : ℝ} (hJ : 0 < J) {z : ℂ}
    (hz : ‖z‖=1) (hI : z ≠ Complex.I) (hnI : z ≠ -Complex.I) :
    ∃ beta : ℂ → ℂ, AnalyticAt ℂ beta z ∧ beta z ≠ 0 ∧
      ∀ᶠ s : ℂ in 𝓝 z, Complex.sinh (2*(J:ℂ)*beta s)=s :=
  IsingBulk.Final.unit_local_inverseTemperature_exists hz hI hnI hJ

/-- General local multiplication lemma for an already specified genuine
sheet; the terminal all-branch theorem assumes no such regularity premise. -/
theorem beta_normalization_regular (ν : Phase) {J : ℝ} {beta : ℂ → ℂ} {z : ℂ}
    (hz : ‖z‖=1) (hfour : z^4 ≠ 1) (hb : AnalyticAt ℂ beta z)
    (hrel : Complex.sinh (2*(J:ℂ)*beta z)=z) :
    AnalyticAt ℂ (fun s => beta s*normalization ν s) z ∧
      beta z*normalization ν z ≠ 0 := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  obtain ⟨ha, hn⟩ := normalization_regular_at_unit_nonaxis ν hz hfour
  exact ⟨hb.mul ha, mul_ne_zero (beta_branch_ne_zero hz0 hrel) hn⟩

/-- Every genuine sheet on an open connected region inside a canonical
branch chart extends to that chart, and its nonvanishing is a theorem. This
is the source-level sheet-rigidity result used by the all-branch endpoint. -/
theorem beta_sheet_extension {U V : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hne : U.Nonempty) (hUV : U ⊆ V)
    (hVconn : IsPreconnected V) {J : ℝ} (hJ : 0 < J) (beta beta0 : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ beta U) (hb0 : AnalyticOnNhd ℂ beta0 V)
    (hrel : ∀ s∈U, Complex.sinh (2*(J:ℂ)*beta s)=s)
    (hrel0 : ∀ s∈V, Complex.sinh (2*(J:ℂ)*beta0 s)=s) :
    ∃ betaExt : ℂ → ℂ, AnalyticOnNhd ℂ betaExt V ∧ Set.EqOn betaExt beta U ∧
      (∀ s∈V, Complex.sinh (2*(J:ℂ)*betaExt s)=s) ∧
      (∀ s∈V, s ≠ 0 → betaExt s ≠ 0) :=
  IsingBulk.Final.inverseTemperature_sheet_extension hU hconn hne hUV hVconn hJ beta beta0
    hb hb0 hrel hrel0

end
end IsoProof
