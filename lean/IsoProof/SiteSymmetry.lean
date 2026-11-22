import IsoProof.SiteAnalytic
import IsingBulk.HT.Contour.PhysicalLatticeSummation
import IsingBulk.First.AnnularOnsiteDensity

/-! Both displacement powers are kept in the actual double contour before
the two circle families are exchanged.  The equality is first proved on
the complete real temperature ray and then extended by analytic identity
to every point of the physical energy slit domain. -/
namespace IsoProof
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
set_option maxHeartbeats 800000

theorem physicalFullLatticeCoefficient_axis_swap (N : ℕ) (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) (v : ℤ × ℤ) :
    physicalFullLatticeCoefficient N t v = physicalFullLatticeCoefficient N t v.swap := by
  obtain ⟨hr,hr1,hm⟩ := IsingBulk.HT22.Physical.realContourRadius_admissible ht
  let r := IsingBulk.HT22.Physical.realContourRadius t
  rw [physicalFullLatticeCoefficient_eq_box N hN ht hr hr1 hm,
    physicalFullLatticeCoefficient_eq_box N hN ht hr hr1 hm]
  congr 1
  let F : (Fin N → ℝ) × (Fin N → ℝ) → ℂ := fun p =>
    doubleAngularDensityOf r (onsiteDensity (t : ℂ)) p *
      ((coordinateProduct (angleTuple r p.1))^v.1.natAbs *
       (coordinateProduct (angleTuple r p.2))^v.2.natAbs)
  let G : (Fin N → ℝ) × (Fin N → ℝ) → ℂ := fun p =>
    doubleAngularDensityOf r (onsiteDensity (t : ℂ)) p *
      ((coordinateProduct (angleTuple r p.1))^v.2.natAbs *
       (coordinateProduct (angleTuple r p.2))^v.1.natAbs)
  change (∫ p in angleBox N ×ˢ angleBox N, F p) =
    ∫ p in angleBox N ×ˢ angleBox N, G p
  have he (p : (Fin N → ℝ) × (Fin N → ℝ)) : F p=G p.swap := by
    dsimp only [F,G,doubleAngularDensityOf,Prod.swap]
    rw [onsiteDensity_swap (t : ℂ) (angleTuple r p.1) (angleTuple r p.2)]
    ring
  simp_rw [he]
  exact setIntegral_prod_swap (angleBox N) (angleBox N) G

/-- Axis exchange for every positive particle number, with neither parity
nor either axis or the origin omitted. -/
theorem siteCoefficient_axis_swap (N : ℕ) (hN : 0 < N) (A B : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    siteCoefficient N A (B : ℤ) E = siteCoefficient N B (A : ℤ) E := by
  apply energy_eq_of_real_temperature
    (fun _ h => siteCoefficient_analyticAt N A (B : ℤ) h)
    (fun _ h => siteCoefficient_analyticAt N B (A : ℤ) h) ?_ hE
  intro t ht
  rw [siteCoefficient_energy_real N A (B : ℤ) ht,
    siteCoefficient_energy_real N B (A : ℤ) ht]
  simpa only [physicalFullLatticeCoefficient,Prod.swap,Int.natAbs_natCast] using
    physicalFullLatticeCoefficient_axis_swap N hN ht ((A : ℤ),(B : ℤ))

theorem siteCoefficient_horizontal_natAbs (N A : ℕ) (B : ℤ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    siteCoefficient N A B E = siteCoefficient N A (B.natAbs : ℤ) E := by
  apply energy_eq_of_real_temperature
    (fun _ h => siteCoefficient_analyticAt N A B h)
    (fun _ h => siteCoefficient_analyticAt N A (B.natAbs : ℤ) h) ?_ hE
  intro t ht
  rw [siteCoefficient_energy_real N A B ht,
    siteCoefficient_energy_real N A (B.natAbs : ℤ) ht]
  exact physicalLatticeCoefficient_horizontal_natAbs N ht A B

/-- The square shell radius, rather than one arbitrarily chosen coordinate,
is the transfer direction of the literal coefficient. -/
theorem siteCoefficient_square_sector (N : ℕ) (hN : 0 < N) (p : ℤ × ℤ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    siteCoefficient N p.1.natAbs p.2 E =
      siteCoefficient N (max p.1.natAbs p.2.natAbs)
        ((min p.1.natAbs p.2.natAbs : ℕ) : ℤ) E := by
  rw [siteCoefficient_horizontal_natAbs N p.1.natAbs p.2 hE]
  by_cases h : p.2.natAbs ≤ p.1.natAbs
  · simp only [max_eq_left h,min_eq_right h]
  · rw [max_eq_right (le_of_not_ge h),min_eq_left (le_of_not_ge h)]
    exact siteCoefficient_axis_swap N hN _ _ hE

/-- Axis reduction commutes with every actual complex energy derivative,
because it holds on an open neighborhood, not merely at boundary values. -/
theorem siteCoefficient_square_sector_jet (N : ℕ) (hN : 0 < N) (p : ℤ × ℤ)
    (j : ℕ) {E : ℂ} (hE : E ∈ energyDomain) :
    iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E =
      iteratedDeriv j (siteCoefficient N (max p.1.natAbs p.2.natAbs)
        ((min p.1.natAbs p.2.natAbs : ℕ) : ℤ)) E := by
  have he : siteCoefficient N p.1.natAbs p.2 =ᶠ[𝓝 E]
      siteCoefficient N (max p.1.natAbs p.2.natAbs)
        ((min p.1.natAbs p.2.natAbs : ℕ) : ℤ) := by
    filter_upwards [isOpen_energyDomain.mem_nhds hE] with w hw
    exact siteCoefficient_square_sector N hN p hw
  exact he.iteratedDeriv_eq j

end
end IsoProof
