import IsoProof.IntegralsBridge
import IsingBulk.Preferred22.KernelProduct
import IsingBulk.Preferred22.HorizontalFourier
import IsingBulk.HT22.Physical.Holomorphy

/-! Even-particle determinant/product bridge, with no exclusion of coincident
or reciprocal angular points. This identifies exactly where the older even
Pfaffian route is applicable and where an odd-particle argument is still needed.
-/
namespace IsoProof
noncomputable section
open scoped BigOperators
open IsingBulk.First IsingBulk.Tail

/-- The old even-particle determinant is the literal pair product in the
manuscript, including the angular reciprocity locus. -/
theorem pairProduct_eq_even_determinant (n : ℕ) {s : ℂ} (hs : 1 < ‖s‖)
    (q : Fin (2*n) → ℝ) :
    pairProduct (energy s) q =
      (IsingBulk.Preferred22.gaugeKernel
        (fun i => IsingBulk.Preferred22.angleRoot (q i))
        (IsingBulk.Preferred22.angularRoots s q)).det := by
  rw [IsingBulk.Preferred22.physical_determinant_rational_product n hs q]
  unfold pairProduct canceledPairProduct
  apply Finset.prod_congr rfl
  intro i _
  have hf : Finset.univ.filter (fun j : Fin (2*n) => i < j) = Finset.Ioi i := by
    ext j
    simp
  rw [hf]
  apply Finset.prod_congr rfl
  intro j _
  simp only [canceledPair, anglePoint, IsingBulk.Tail.limitingAngle,
    IsingBulk.Preferred22.angleRoot, angleRoot, energy,
    IsingBulk.Preferred22.angularRoots, IsingBulk.Preferred22.angularW,
    IsingBulk.Preferred22.temperatureTrace]
  simp only [mul_comm (q i : ℂ) Complex.I, mul_comm (q j : ℂ) Complex.I]
  ring

/-- Exact even density, including the one-body normalization. -/
theorem particleDensity_positive_eq_preferred {N : ℕ}
    (hN : ∃ n : ℕ, N = 2*n) {s : ℂ} (hs : 1 < ‖s‖) (q : Fin N → ℝ) :
    particleDensity .positive (energy s) q =
      IsingBulk.Preferred22.fullAngularDensity s q := by
  obtain ⟨n, rfl⟩ := hN
  unfold particleDensity
  rw [pairProduct_eq_even_determinant n hs q]
  simp only [signValue, one_mul, IsingBulk.Preferred22.fullAngularDensity,
    IsingBulk.HT22.Physical.oneBody_eq_rational, IsingBulk.Preferred22.oneBody,
    angleRoot, energy, IsingBulk.Preferred22.angularRoots,
    IsingBulk.Preferred22.angularW, IsingBulk.Preferred22.temperatureTrace]

/-- Fundamental-domain change and exact factorial/power normalization. -/
theorem particleCoefficient_positive_eq_preferred {N : ℕ}
    (hN : ∃ n : ℕ, N = 2*n) {s : ℂ} (hs : 1 < ‖s‖) :
    particleCoefficient .positive N (energy s) = IsingBulk.Preferred22.coefficient N s := by
  cases N with
  | zero => simp [particleCoefficient, IsingBulk.Preferred22.coefficient]
  | succ k =>
    simp only [particleCoefficient, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      IsingBulk.Preferred22.coefficient]
    change ((k+1).factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^k *
      multiAngleIntegral k (fun q => particleDensity .positive (energy s)
        (constrainedAngles .positive k q)) = _
    have hd : (fun q : Fin k → ℝ =>
        particleDensity .positive (energy s) (constrainedAngles .positive k q)) =
        fun q => IsingBulk.Preferred22.fullAngularDensity s
          (IsingBulk.Preferred22.constrainedAngles q) := by
      funext q
      rw [particleDensity_positive_eq_preferred hN hs]
      simp only [constrainedAngles, signAngle, zero_sub, IsingBulk.Preferred22.constrainedAngles]
    rw [hd, IsingBulk.Preferred22.angularBox_integral_eq_multiAngleIntegral
      (fun q : Fin k → ℝ => IsingBulk.Preferred22.fullAngularDensity s
        (IsingBulk.Preferred22.constrainedAngles q))
      ((IsingBulk.Preferred22.fullAngularDensity_continuous (by omega) hs).comp
        (IsingBulk.Preferred22.constrainedAngles_continuous k))
      (IsingBulk.Preferred22.constrainedDensity_periodic s)]
    simp only [mul_inv_rev, ← inv_pow]
    ring

/-- The complete positive even sum is exactly the old literal even series. -/
theorem fullEnergySum_low_energy {s : ℂ} (hs : 1 < ‖s‖) :
    fullEnergySum .low .positive (energy s) = IsingBulk.Preferred22.evenSeries s := by
  apply tsum_congr
  intro n
  exact particleCoefficient_positive_eq_preferred ⟨n+1,rfl⟩ hs

end
end IsoProof
