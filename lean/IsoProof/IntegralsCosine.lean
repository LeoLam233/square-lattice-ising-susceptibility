import IsoProof.IntegralsBridge
import IsingBulk.HT.Contour.PhysicalLatticeReflection
import IsingBulk.HT.Contour.PhysicalAngularRegularity

/-! ONGP (4.2) uses a cosine Fourier multiplier. This module proves its
identity with the literal exponential multiplier in the new site integral.
The proof uses full angular reflection and finite-dimensional integration.
-/
namespace IsoProof
noncomputable section
open scoped BigOperators
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open MeasureTheory

private def realSiteFourierDensity (N A : ℕ) (B : ℤ) (t : ℝ)
    (q : Fin N → ℝ) : ℂ :=
  ((physicalAngularWeight t q*(physicalZ t q)^A : ℝ) : ℂ) *
    Complex.exp (Complex.I*(B : ℂ)*(∑ i, (q i : ℂ)))

private theorem realSiteFourierDensity_continuous (N A : ℕ) (B : ℤ)
    {t : ℝ} (ht : 1 < t) : Continuous (realSiteFourierDensity N A B t) := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp
      ((physicalAngularWeight_continuous N ht).mul ((physicalZ_continuous N ht).pow A))
  · exact Complex.continuous_exp.comp (by fun_prop)

private theorem multiAngleIntegral_add (N : ℕ) (f g : (Fin N → ℝ) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    multiAngleIntegral N (fun q => f q+g q) = multiAngleIntegral N f+multiAngleIntegral N g := by
  rw [multiAngleIntegral_eq_box N (fun q => f q+g q) (hf.add hg),
    multiAngleIntegral_eq_box N f hf, multiAngleIntegral_eq_box N g hg]
  exact integral_add (hf.continuousOn.integrableOn_compact isCompact_Icc)
    (hg.continuousOn.integrableOn_compact isCompact_Icc)

/-- The source's actual cosine integral, with its N-dimensional measure and
factorial. The real parameter t is exterior, also for high-temperature duality. -/
def publishedCosineSiteCoefficient (N A : ℕ) (B : ℤ) (t : ℝ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
    multiAngleIntegral N (fun q =>
      ((physicalAngularWeight t q*(physicalZ t q)^A : ℝ) : ℂ) *
        Complex.cos ((B : ℂ)*(∑ i, (q i : ℂ))))

theorem physicalLatticeCoefficient_eq_cosine (N A : ℕ) (B : ℤ)
    {t : ℝ} (ht : 1 < t) :
    physicalLatticeCoefficient N t A B = publishedCosineSiteCoefficient N A B t := by
  let f := realSiteFourierDensity N A B t
  let g := realSiteFourierDensity N A (-B) t
  have hp (q : Fin N → ℝ) :
      ((physicalAngularWeight t q*(physicalZ t q)^A : ℝ) : ℂ) *
        Complex.cos ((B : ℂ)*(∑ i, (q i : ℂ))) = (1/2 : ℂ)*(f q+g q) := by
    dsimp [f,g,realSiteFourierDensity]
    rw [Complex.cos]
    rw [show ((B : ℂ)*(∑ i,(q i : ℂ)))*Complex.I =
      Complex.I*(B : ℂ)*(∑ i,(q i : ℂ)) by ring]
    rw [show (-((B : ℂ)*(∑ i,(q i : ℂ))))*Complex.I =
      Complex.I*((-B : ℤ) : ℂ)*(∑ i,(q i : ℂ)) by push_cast; ring]
    ring
  have href := physicalLatticeCoefficient_horizontal_reflection N ht A B
  unfold publishedCosineSiteCoefficient
  simp_rw [hp]
  rw [physical_multiAngleIntegral_const_mul,
    multiAngleIntegral_add N f g (realSiteFourierDensity_continuous N A B ht)
      (realSiteFourierDensity_continuous N A (-B) ht)]
  have halg : (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
      ((1/2 : ℂ)*(multiAngleIntegral N f+multiAngleIntegral N g)) =
      (1/2 : ℂ)*(physicalLatticeCoefficient N t A B + physicalLatticeCoefficient N t A (-B)) := by
    unfold physicalLatticeCoefficient
    change _ = (1/2 : ℂ)*((N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
      multiAngleIntegral N f + (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
      multiAngleIntegral N g)
    ring
  rw [halg, href]
  ring

/-- Exact bridge from the paper's complex Fourier integral to ONGP's real
cosine integral. No missing factor two is absorbed into a physical premise. -/
theorem siteCoefficient_energy_real_eq_cosine (N A : ℕ) (B : ℤ)
    {t : ℝ} (ht : 1 < t) :
    siteCoefficient N A B (energy (t : ℂ)) = publishedCosineSiteCoefficient N A B t := by
  rw [siteCoefficient_energy_real N A B ht, physicalLatticeCoefficient_eq_cosine N A B ht]

end
end IsoProof
