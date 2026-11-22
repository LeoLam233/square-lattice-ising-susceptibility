import IsoProof.PhysicalHolomorphy
import IsoProof.PhysicalIdentification
import IsingBulk.HT22.Final.NaturalBoundary
import IsingBulk.Preferred22.FullTheorem

/-!
Terminal boundary statements for the new literal susceptibility objects.
The old strong theorems enter only after coefficient, full-series, physical
normalization, and high-temperature origin identifications are proved.
The low-temperature physical statement quantifies over every genuine local
inverse-sinh sheet on arbitrary exterior approach domains, including approach
to both inverse-sinh branch points. It does not assert a global exterior beta.
-/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology

/-- Equality to the independently checked HT22 germ includes the origin. -/
theorem reduced_high_eq_ht22 {s : ℂ} (hs : s ∈ physicalDomain .high) :
    reducedSusceptibility .high s = IsingBulk.HT22.Physical.interiorBulk s :=
  (reduced_high_eq_existing hs).trans
    (IsingBulk.HT22.Physical.interiorBulk_eqOn_existing hs).symm

theorem reduced_high_naturalBoundary :
    NaturalBoundary (physicalDomain .high) (reducedSusceptibility .high) := by
  intro z hz he
  apply IsingBulk.HT22.Final.f001_natural_boundary.2.1 z hz
  obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq ⟨hs.1,hs.2.2⟩).symm.trans (reduced_high_eq_ht22 hs.2.2)

theorem reduced_low_naturalBoundary :
    NaturalBoundary (physicalDomain .low) (reducedSusceptibility .low) := by
  intro z hz he
  apply IsingBulk.Preferred22.preferred_bulk_natural_boundary z hz
  obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq hs).symm.trans (reduced_low_eq_existing hs.2)

theorem reduced_naturalBoundary (ν : Phase) :
    NaturalBoundary (physicalDomain ν) (reducedSusceptibility ν) := by
  cases ν
  · exact reduced_high_naturalBoundary
  · exact reduced_low_naturalBoundary

/-- Canonical physical germ. The principal formula is used on the disk and
on the positive-real low-temperature chart; arbitrary exterior sheets are
handled by the branch-family theorem below. -/
def physicalSusceptibility (ν : Phase) (J : ℝ) (s : ℂ) : ℂ :=
  IsingBulk.Final.inverseTemperatureBranch J s * reducedSusceptibility ν s

theorem physical_high_eq_ht22 (J : ℝ) {s : ℂ} (hs : s ∈ physicalDomain .high) :
    physicalSusceptibility .high J s = IsingBulk.HT22.Physical.physicalSusceptibility J s := by
  unfold physicalSusceptibility IsingBulk.HT22.Physical.physicalSusceptibility
  rw [reduced_high_eq_ht22 hs]

theorem physical_high_analyticOn {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (physicalSusceptibility .high J) (physicalDomain .high) := by
  intro s hs
  exact (IsingBulk.HT.Final.inverseTemperatureBranch_analyticAt_disk hJ hs).mul
    (reduced_high_analyticOn s hs)

theorem physical_high_naturalBoundary {J : ℝ} (hJ : 0 < J) :
    NaturalBoundary (physicalDomain .high) (physicalSusceptibility .high J) := by
  intro z hz he
  apply (IsingBulk.HT22.Final.f001_natural_boundary.2.2 J hJ).2 z hz
  obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
  refine ⟨U,hU,hzU,g,hg,?_⟩
  intro s hs
  exact (hEq ⟨hs.1,hs.2.2⟩).symm.trans (physical_high_eq_ht22 J hs.2.2)

/-- Literal branch-family continuation predicate: beta lives only on an open
exterior approach set and obeys the genuine inverse-sinh equation. -/
def PhysicalExteriorExtension (J : ℝ) (X : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ U : Set ℂ, IsOpen U ∧ z ∈ closure U ∧
    U ⊆ Metric.ball z R ∩ physicalDomain .low ∧ ∃ beta g : ℂ → ℂ,
      AnalyticOnNhd ℂ beta U ∧ AnalyticOnNhd ℂ g (Metric.ball z R) ∧
      (∀ s ∈ U, Complex.sinh (2*(J:ℂ)*beta s)=s) ∧
      Set.EqOn g (fun s => beta s*X s) U

/-- All local physical beta sheets, even at z=±i. No branch analyticity or
boundary obstruction is an extra premise of this terminal theorem. -/
theorem physical_low_all_branches_naturalBoundary {J : ℝ} (hJ : 0 < J) :
    ∀ z : ℂ, ‖z‖=1 →
      ¬PhysicalExteriorExtension J (reducedSusceptibility .low) z := by
  apply IsingBulk.Preferred22.physical_no_boundary_extension
    reduced_low_analyticOn
  · intro z hz he
    apply reduced_low_naturalBoundary z hz
    obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
    exact ⟨U,hU,hzU,g,hg,hEq.symm⟩
  · exact hJ

theorem physical_real_identification (ν : Phase) (J : ℝ)
    {corr : ℝ → LatticeSite → ℂ} (hphys : PublishedSiteInput ν corr)
    {s : ℝ} (hs : s ∈ realTemperatureDomain ν) :
    physicalSusceptibility ν J (s : ℂ) = realPhysicalSum ν J corr s := by
  have hs0 : 0 ≤ s := by
    cases ν with
    | high => exact hs.1.le
    | low => exact (lt_trans zero_lt_one hs).le
  rw [physicalSusceptibility, IsingBulk.Final.inverseTemperatureBranch_real hs0,
    realPhysicalSum_identification ν J hphys hs]
  simp [realInverseTemperature, Complex.ofReal_div, Complex.ofReal_mul]

/-- Complete physical real-interval germ analyticity in both phases. -/
theorem physical_real_analyticAt (ν : Phase) {J s : ℝ} (hJ : 0 < J)
    (hs : s ∈ realTemperatureDomain ν) :
    AnalyticAt ℂ (physicalSusceptibility ν J) (s : ℂ) := by
  have hspos : 0 < s := by cases ν with
    | high => exact hs.1
    | low => exact lt_trans zero_lt_one hs
  have hsD : (s : ℂ) ∈ physicalDomain ν := by
    cases ν <;> simp only [physicalDomain, Set.mem_ofPred_eq, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hspos]
    · exact hs.2
    · exact hs
  exact (IsingBulk.Final.inverseTemperatureBranch_regular
    (by simpa only [Complex.ofReal_re] using hspos) hJ).1.mul (reduced_analyticOn ν _ hsD)

end
end IsoProof
