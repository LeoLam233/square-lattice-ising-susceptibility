import IsoProof.IntegralsOneParticle
import IsingBulk.HT22.Physical.SignedConvergence
import IsoProof.IntegralsParity

/-! Energy reflection of the actual signed odd integral. Both the constraint
sign and the resolvent sign change; this is not an evenness assumption. -/
namespace IsoProof
noncomputable section
open scoped BigOperators

theorem fullEnergySum_high_positive_signed_energy (s : ℂ) :
    fullEnergySum .high .positive (energy s) =
      IsingBulk.HT22.Physical.signedOddSeries false s := by
  apply tsum_congr
  intro n
  exact particleCoefficient_positive_energy (2*n+1) s

theorem fullEnergySum_high_negative_signed_energy (s : ℂ) :
    fullEnergySum .high .negative (energy s) =
      IsingBulk.HT22.Physical.signedOddSeries true s := by
  apply tsum_congr
  intro n
  exact particleCoefficient_negative_energy (2*n+1) s

theorem energy_neg (s : ℂ) : energy (-s) = -energy s := by
  simp only [energy, inv_neg]
  ring

theorem particleCoefficient_odd_reflection (n : ℕ) {E : ℂ} (hE : E ∈ energyDomain) :
    particleCoefficient .positive (2*n+1) (-E) =
      -particleCoefficient .negative (2*n+1) E := by
  obtain ⟨hs, he⟩ := exteriorEnergyInverse_spec hE
  rw [← he, ← energy_neg, particleCoefficient_positive_energy,
    particleCoefficient_negative_energy]
  exact IsingBulk.HT22.Physical.coefficient_odd_neg n hs

theorem fullEnergySum_high_reflection {E : ℂ} (hE : E ∈ energyDomain) :
    fullEnergySum .high .positive (-E) = -fullEnergySum .high .negative E := by
  simp only [fullEnergySum, particleOrder, particleCoefficient_odd_reflection _ hE, tsum_neg]

theorem fullEnergySum_low_reflection {E : ℂ} (hE : E ∈ energyDomain) :
    fullEnergySum .low .positive (-E) = fullEnergySum .low .positive E := by
  obtain ⟨hs, he⟩ := exteriorEnergyInverse_spec hE
  rw [← he, ← energy_neg, fullEnergySum_low_energy (by simpa only [norm_neg] using hs),
    fullEnergySum_low_energy hs]
  exact IsingBulk.Preferred22.evenSeries_even hs

theorem energy_conj (s : ℂ) : energy (star s) = star (energy s) := by
  simp only [energy, star_add, star_inv₀]

/-- Complex conjugation supplies the other side of the energy slit. -/
theorem particleCoefficient_conjugate (σ : Sign) (N : ℕ) {E : ℂ}
    (hE : E ∈ energyDomain) :
    particleCoefficient σ N (star E) = star (particleCoefficient σ N E) := by
  obtain ⟨hs, he⟩ := exteriorEnergyInverse_spec hE
  cases σ with
  | positive =>
    rw [← he, ← energy_conj, particleCoefficient_positive_energy,
      particleCoefficient_positive_energy]
    exact IsingBulk.HT22.Physical.signedCoefficient_conj false N hs
  | negative =>
    rw [← he, ← energy_conj, particleCoefficient_negative_energy,
      particleCoefficient_negative_energy]
    exact IsingBulk.HT22.Physical.signedCoefficient_conj true N hs

theorem fullEnergySum_conjugate (ν : Phase) (σ : Sign) {E : ℂ}
    (hE : E ∈ energyDomain) :
    fullEnergySum ν σ (star E) = star (fullEnergySum ν σ E) := by
  simp only [fullEnergySum, particleCoefficient_conjugate σ _ hE, tsum_star]

end
end IsoProof
