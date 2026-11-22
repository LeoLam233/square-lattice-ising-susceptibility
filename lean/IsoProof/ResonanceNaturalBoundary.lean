import IsoProof.ResonanceSusceptibility
import IsingBulk.HT22.Final.SignedObstruction
import IsingBulk.HT22.Final.BoundaryTransfer
import IsingBulk.Preferred22.BoundaryPropagation

/-! Natural boundaries proved from the actual new sharp full-series
producers.  Only generic analytic-factor, signed-reflection, conjugation,
inversion, and dense-set propagation lemmas are reused; no old complete
natural-boundary terminal is invoked in these proof terms. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A genuine local extension makes every derivative continuous along every
physical approach path.  A proved divergent derivative therefore forbids it. -/
theorem no_localExtension_of_sharp_path {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ→ℂ} {z : ℂ} {path : ℝ→ℂ} {k : ℕ}
    (hp : Tendsto path (𝓝[>] 0) (𝓝 z))
    (hmem : ∀ᶠ t in 𝓝[>] (0:ℝ),path t∈D)
    (hsharp : Tendsto (fun t=>‖iteratedDeriv k f (path t)‖) (𝓝[>] 0) atTop) :
    ¬LocalExtension D f z := by
  rintro ⟨U,hU,hzU,G,hG,hEq⟩
  have hj : (fun t=>iteratedDeriv k f (path t))=ᶠ[𝓝[>] 0]
      (fun t=>iteratedDeriv k G (path t)) := by
    filter_upwards [hp.eventually (hU.mem_nhds hzU),hmem] with t htU htD
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [(hU.inter hD).mem_nhds ⟨htU,htD⟩] with w hw
    exact hEq hw
  have hcont : ContinuousAt (iteratedDeriv k G) z :=
    (IsingBulk.First.analyticAt_iteratedDeriv (hG z hzU) k).continuousAt
  have hfin : Tendsto (fun t=>‖iteratedDeriv k f (path t)‖)
      (𝓝[>] 0) (𝓝 ‖iteratedDeriv k G z‖) :=
    (tendsto_congr' (hj.fun_comp norm)).mpr (hcont.norm.tendsto.comp hp)
  exact not_tendsto_nhds_of_tendsto_atTop hsharp _ hfin

/-- The full upper prime family, including its effective negative-sign
members, has no extension by the newly proved sharp-order divergence. -/
theorem high_prime_no_extension_from_sharp {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.HT22.Arithmetic.PrimeIndex p a) :
    ¬IsingBulk.Final.HasExteriorExtension IsingBulk.HT22.Physical.oddSeries
      (IsingBulk.PrimeFamily.angleRoot p a) := by
  apply IsingBulk.HT22.Final.no_extension_original_of_effective_signed
  let ζ : ℂ := Complex.exp ((IsingBulk.HT22.Arithmetic.effectiveAngle
    (IsingBulk.PrimeFamily.angle p a):ℂ)*Complex.I)
  have hz : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hsharp : Tendsto (fun t=>‖iteratedDeriv (criticalOrder p)
      (IsingBulk.HT22.Physical.signedOddSeries
        (IsingBulk.HT22.Arithmetic.negativeSide (IsingBulk.PrimeFamily.angle p a)))
      (radialTemperature ζ t)‖) (𝓝[>] 0) atTop := by
    simpa only [radialTemperature,ζ,IsingBulk.Branch.radialParameter,
      IsingBulk.HT22.Arithmetic.primeBranchData,IsingBulk.HT22.Arithmetic.positiveTraceBranchData,
      Complex.ofReal_add,Complex.ofReal_one] using (high_prime_sharp_full_sum hp hp5 ha).1
  have hn := no_localExtension_of_sharp_path (isOpen_lt continuous_const continuous_norm)
    (radialTemperature_tendsto ζ)
    ((show ∀ᶠ t in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin).mono
      (fun _ ht=>radialTemperature_exterior hz ht)) hsharp
  rintro ⟨U,hU,hζU,G,hG,hEq⟩
  exact hn ⟨U,hU,hζU,G,hG,hEq.symm⟩

private theorem high_boundary_transfer_from_sharp :
    (∀ z : ℂ,‖z‖=1→ ¬IsingBulk.HT.Final.HasInteriorExtension
      IsingBulk.HT22.Physical.interiorBulk z) ∧
    (∀ J : ℝ,0<J→∀ z : ℂ,‖z‖=1→ ¬IsingBulk.HT.Final.HasInteriorExtension
      (IsingBulk.HT22.Physical.physicalSusceptibility J) z) := by
  apply IsingBulk.HT22.Final.boundary_transfer_of_prime_obstructions
  rintro z ⟨p,a,hp,hp5,ha,rfl⟩
  exact high_prime_no_extension_from_sharp hp hp5 ha

/-- All HT boundary points, including ±1 and ±i, from actual sharp full sums. -/
theorem reduced_high_naturalBoundary_from_sharp :
    NaturalBoundary (physicalDomain .high) (reducedSusceptibility .high) := by
  intro z hz he
  apply high_boundary_transfer_from_sharp.1 z hz
  obtain ⟨U,hU,hzU,G,hG,hEq⟩ := he
  refine ⟨U,hU,hzU,G,hG,?_⟩
  intro s hs
  exact (hEq ⟨hs.1,hs.2.2⟩).symm.trans (reduced_high_eq_ht22 hs.2.2)

/-- Low-temperature prime obstructions are supplied directly by the new
actual reduced-susceptibility sharp theorem, then propagated by the proved
even and conjugate symmetries and closed-arc density. -/
theorem reduced_low_naturalBoundary_from_sharp :
    NaturalBoundary (physicalDomain .low) (reducedSusceptibility .low) := by
  have heven : ∀ s : ℂ,1<‖s‖→ reducedSusceptibility .low (-s)=reducedSusceptibility .low s := by
    intro s hs
    rw [reduced_low_eq_existing (by simpa only [norm_neg] using hs),
      reduced_low_eq_existing hs,IsingBulk.Preferred22.bulkFunction_even hs]
  have hreal : ∀ s : ℂ,1<‖s‖→ reducedSusceptibility .low (star s)=star (reducedSusceptibility .low s) := by
    intro s hs
    rw [reduced_low_eq_existing (by simpa only [norm_star] using hs),
      reduced_low_eq_existing hs,IsingBulk.Preferred22.bulkFunction_conj hs]
  have hsel : ∀ z∈IsingBulk.Preferred22.primeRootFamily,
      ¬IsingBulk.Preferred22.HasExteriorExtension (reducedSusceptibility .low) z := by
    rintro z ⟨p,a,hp,hp5,ha,rfl⟩
    have hz := angleRoot_unit p a
    have hs := (reduced_prime_sharp .low hp hp5 ha).1
    have hn := no_localExtension_of_sharp_path
      (show IsOpen (physicalDomain .low) from isOpen_lt continuous_const continuous_norm)
      (radialTemperature_tendsto (IsingBulk.PrimeFamily.angleRoot p a))
      ((show ∀ᶠ t in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin).mono
        (fun _ ht=>radialTemperature_exterior hz ht)) hs
    rintro ⟨U,hU,hzU,G,hG,hEq⟩
    exact hn ⟨U,hU,hzU,G,hG,hEq.symm⟩
  have hfull := IsingBulk.Preferred22.unit_circle_no_extension_of_selected heven hreal hsel
  intro z hz he
  apply hfull z hz
  obtain ⟨U,hU,hzU,G,hG,hEq⟩ := he
  exact ⟨U,hU,hzU,G,hG,hEq.symm⟩

theorem reduced_naturalBoundary_from_sharp (ν : Phase) :
    NaturalBoundary (physicalDomain ν) (reducedSusceptibility ν) := by
  cases ν
  · exact reduced_high_naturalBoundary_from_sharp
  · exact reduced_low_naturalBoundary_from_sharp

/-- The canonical physical HT function has the same complete boundary,
using the analytic beta-factor transfer with the newly proved prime obstruction. -/
theorem physical_high_naturalBoundary_from_sharp {J : ℝ} (hJ : 0<J) :
    NaturalBoundary (physicalDomain .high) (physicalSusceptibility .high J) := by
  intro z hz he
  apply high_boundary_transfer_from_sharp.2 J hJ z hz
  obtain ⟨U,hU,hzU,G,hG,hEq⟩ := he
  refine ⟨U,hU,hzU,G,hG,?_⟩
  intro s hs
  exact (hEq ⟨hs.1,hs.2.2⟩).symm.trans (physical_high_eq_ht22 J hs.2.2)

/-- Every genuine exterior inverse-sinh sheet, including approach to ±i,
from the new reduced natural boundary and generic sheet-extension rigidity. -/
theorem physical_low_all_branches_naturalBoundary_from_sharp {J : ℝ} (hJ : 0<J) :
    ∀ z : ℂ,‖z‖=1→ ¬PhysicalExteriorExtension J (reducedSusceptibility .low) z := by
  apply IsingBulk.Preferred22.physical_no_boundary_extension reduced_low_analyticOn
  · intro z hz he
    apply reduced_low_naturalBoundary_from_sharp z hz
    obtain ⟨U,hU,hzU,G,hG,hEq⟩ := he
    exact ⟨U,hU,hzU,G,hG,hEq.symm⟩
  · exact hJ

end
end IsoProof
