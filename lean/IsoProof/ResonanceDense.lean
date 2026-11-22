import IsoProof.ResonanceSusceptibility

/-! A single arithmetically specified dense family works for both physical
phases and for both actual susceptibility normalizations.  Its definition
mentions neither a singularity hypothesis nor a differential relation. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open IsingBulk.PrimeFamily
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Explicit prime energy levels in the interval whose two sharp orders
exceed the requested jet order. -/
def primeSingularLevels (r : ℕ) (L U : ℝ) : Set ℝ :=
  {x | x∈Ioo L U ∧ ∃ p : ℕ, ∃ j : ℤ,
    p.Prime ∧ 5≤p ∧ Admissible p j ∧ r<criticalOrder p ∧
      r<criticalOrder (2*p) ∧ x=2*Real.cos (angle p j)}

theorem primeSingularLevels_subset (r : ℕ) (L U : ℝ) :
    primeSingularLevels r L U ⊆ Ioo L U := fun _ hx=>hx.1

/-- Density remains true after removing all primes below any fixed threshold
of sharp derivative order. -/
theorem primeSingularLevels_dense (r : ℕ) {L U : ℝ} (hL : 0<L) (hU : U<2) :
    Ioo L U ⊆ closure (primeSingularLevels r L U) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  let a := max L (x-ε/2)
  let b := min U (x+ε/2)
  have haL : L≤a := le_max_left _ _
  have hax : a<x := max_lt hx.1 (by linarith)
  have hxb : x<b := lt_min hx.2 (by linarith)
  have hbU : b≤U := min_le_left _ _
  obtain ⟨p,j,hp,hp5,hj,hk1,hk2,hy⟩ := exists_common_prime_energy_in_interval r
    (hL.trans_le haL) (hax.trans hxb) (hbU.trans_lt hU)
  refine ⟨2*Real.cos (angle p j),?_,?_⟩
  · exact ⟨⟨haL.trans_lt hy.1,hy.2.trans_le hbU⟩,p,j,hp,hp5,hj,hk1,hk2,rfl⟩
  · rw [Real.dist_eq,abs_lt]
    have hya : x-ε/2<2*Real.cos (angle p j) :=
      (le_max_right L (x-ε/2)).trans_lt hy.1
    have hyb : 2*Real.cos (angle p j)<x+ε/2 :=
      hy.2.trans_le (min_le_right U (x+ε/2))
    constructor <;> linarith

theorem phaseCriticalOrder_high_on_primeSingularLevels (ν : Phase)
    {r : ℕ} {L U x : ℝ} (hx : x∈primeSingularLevels r L U) :
    ∃ p : ℕ,∃ j : ℤ,p.Prime ∧ 5≤p ∧ Admissible p j ∧
      r<phaseCriticalOrder ν p ∧ x=2*Real.cos (angle p j) := by
  obtain ⟨_hI,p,j,hp,hp5,hj,hk1,hk2,hx⟩ := hx
  refine ⟨p,j,hp,hp5,hj,?_,hx⟩
  cases ν with
  | high => exact hk1
  | low => exact hk2

/-- Actual reduced susceptibility sharp singularities on the explicit dense
set.  No analytic estimate or asymptotic premise is supplied by the caller. -/
theorem reduced_sharp_on_primeSingularLevels (ν : Phase) (r : ℕ) {L U R : ℝ}
    (hR : 0<R) {x : ℝ} (hx : x∈primeSingularLevels r L U) :
    ∃ k : ℕ,r≤k ∧ SharpBoundaryApproach (reducedSusceptibility ν)
      (physicalEnergyChart ν) L U R x k := by
  obtain ⟨p,j,hp,hp5,hj,hk,hxeq⟩ := phaseCriticalOrder_high_on_primeSingularLevels ν hx
  refine ⟨phaseCriticalOrder ν p,hk.le,?_⟩
  rw [hxeq]
  exact reduced_prime_sharp_boundary ν hp hp5 hj hR (hxeq ▸ hx.1)

/-- The same explicit dense set works after the genuine beta normalization. -/
theorem physical_sharp_on_primeSingularLevels (ν : Phase) {J : ℝ} (hJ : 0<J)
    (r : ℕ) {L U R : ℝ} (hR : 0<R) {x : ℝ} (hx : x∈primeSingularLevels r L U) :
    ∃ k : ℕ,r≤k ∧ SharpBoundaryApproach (physicalSusceptibility ν J)
      (physicalEnergyChart ν) L U R x k := by
  obtain ⟨p,j,hp,hp5,hj,hk,hxeq⟩ := phaseCriticalOrder_high_on_primeSingularLevels ν hx
  refine ⟨phaseCriticalOrder ν p,hk.le,?_⟩
  rw [hxeq]
  exact physical_prime_sharp_boundary ν hJ hp hp5 hj hR (hxeq ▸ hx.1)

/-- An upper-collar equality suffices to replace a concrete physical chart by
its analytic continuation across the open cut. -/
theorem SharpBoundaryApproach.congr_chart {f g h : ℂ→ℂ} {L U R x : ℝ} {k : ℕ}
    (hs : SharpBoundaryApproach f g L U R x k)
    (he : EqOn g h (upperCollar L U R)) : SharpBoundaryApproach f h L U R x k := by
  obtain ⟨p,hp,htop,hlow⟩ := hs
  have hj (j : ℕ) : (fun t=>iteratedDeriv j f (g (p t)))=ᶠ[𝓝[>] 0]
      (fun t=>iteratedDeriv j f (h (p t))) :=
    (eventually_mem_of_tendsto_nhdsWithin hp).mono (fun _ ht=>congrArg _ (he ht))
  refine ⟨p,hp,htop.congr' ((hj k).fun_comp norm),?_⟩
  intro j hlt
  obtain ⟨C,hC⟩ := hlow j hlt
  refine ⟨C,?_⟩
  filter_upwards [hC,hj j] with t ht heq
  rwa [←heq]

end
end IsoProof
