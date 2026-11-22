import IsoProof.ContourRoot
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Uniform scalar bounds on any compact family of the explicit protected
sheet. This is the compactness step used after the concrete common graph
has been placed in its domain. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set

theorem contourRootDomain_isOpen : IsOpen contourRootDomain := by
  exact (Complex.isOpen_slitPlane.preimage (by fun_prop)).inter
    (Complex.isOpen_slitPlane.preimage (by fun_prop))

theorem exponential_dispersion (q E : ℂ) :
    Complex.exp (Complex.I*q)+(Complex.exp (Complex.I*q))⁻¹+
      continuedTransferRoot (E-Complex.cos q)+
      (continuedTransferRoot (E-Complex.cos q))⁻¹ = 2*E := by
  have hy : Complex.exp (Complex.I*q)+(Complex.exp (Complex.I*q))⁻¹ =
      2*Complex.cos q := by
    rw [Complex.two_cos, ← Complex.exp_neg]
    congr 1 <;> congr 1 <;> ring
  have hu := continuedTransferRoot_trace (E-Complex.cos q)
  linear_combination hy+hu

/-- Both diagonal and off-diagonal pair gaps follow from one coherent
explicit root. No independent pair-pole hypothesis is needed. -/
theorem compact_dispersion_coordinate_bounds {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) (q E : α → ℂ)
    (hq : ContinuousOn q K) (hE : ContinuousOn E K)
    (hdomain : ∀ p ∈ K, E p-Complex.cos (q p) ∈ contourRootDomain) :
    ∃ M > 0, ∃ δ > 0,
      (∀ p ∈ K, δ ≤ ‖Complex.exp (Complex.I*q p)‖) ∧
      (∀ p ∈ K, ‖Complex.exp (Complex.I*q p)‖ ≤ M) ∧
      (∀ p ∈ K, ‖continuedTransferRoot (E p-Complex.cos (q p))‖ ≤ M) ∧
      (∀ p ∈ K, ∀ p' ∈ K,
        δ ≤ ‖1-continuedTransferRoot (E p-Complex.cos (q p))*
          continuedTransferRoot (E p'-Complex.cos (q p'))‖) := by
  let u := fun p => continuedTransferRoot (E p-Complex.cos (q p))
  let z := fun p => Complex.exp (Complex.I*q p)
  have hW : ContinuousOn (fun p => E p-Complex.cos (q p)) K :=
    hE.sub (Complex.continuous_cos.comp_continuousOn hq)
  have hu : ContinuousOn u K := by
    intro p hp
    exact (continuedTransferRoot_analyticAt (hdomain p hp)).continuousAt.comp_continuousWithinAt
      (f := fun p => E p-Complex.cos (q p)) (hW p hp)
  have hz : ContinuousOn z K :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hq)
  obtain ⟨δz,hδz,hδzle⟩ := hK.exists_forall_le' hz.norm
    (fun p _ => norm_pos_iff.mpr (Complex.exp_ne_zero (Complex.I*q p)))
  have hufst : ContinuousOn (fun p : α × α => u p.1) (K ×ˢ K) :=
    hu.comp continuous_fst.continuousOn (fun _ h => h.1)
  have husnd : ContinuousOn (fun p : α × α => u p.2) (K ×ˢ K) :=
    hu.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hp : ContinuousOn (fun p : α × α => ‖1-u p.1*u p.2‖) (K ×ˢ K) :=
    (continuousOn_const.sub (hufst.mul husnd)).norm
  obtain ⟨δp,hδp,hδple⟩ := (hK.prod hK).exists_forall_le' hp
    (fun p h => continuedTransferRoot_pair_gap (hdomain p.1 h.1))
  obtain ⟨Mz,hMz⟩ := hK.bddAbove_image hz.norm
  obtain ⟨Mu,hMu⟩ := hK.bddAbove_image hu.norm
  refine ⟨max 1 (max Mz Mu), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    min δz δp, lt_min hδz hδp, ?_,?_,?_,?_⟩
  · intro p hp
    exact (min_le_left _ _).trans (hδzle p hp)
  · intro p hp
    exact (hMz (mem_image_of_mem _ hp)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro p hp
    exact (hMu (mem_image_of_mem _ hp)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · intro p hp p' hp'
    exact (min_le_right _ _).trans (hδple (p,p') ⟨hp,hp'⟩)

/-- Compact protected families remain protected on one common complex
energy disk, allowing actual Cauchy estimates once the Gaussian phase
majorant has been established. -/
theorem compact_dispersion_energy_disk {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) (W : α → ℂ) (hW : Continuous W)
    (hdomain : ∀ p ∈ K, W p ∈ contourRootDomain) :
    ∃ δ > 0, ∀ e : ℂ, ‖e‖ < δ → ∀ p ∈ K, W p+e ∈ contourRootDomain := by
  have he : ∀ᶠ e : ℂ in 𝓝 0, ∀ p ∈ K, W p+e ∈ contourRootDomain := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hc : Continuous (fun z : ℂ × α => W z.2+z.1) := by fun_prop
    exact (contourRootDomain_isOpen.preimage hc).mem_nhds
      (by simpa using hdomain p hp)
  obtain ⟨δ,hδ,hδprop⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ,hδ,fun e he p hp => hδprop (y := e) (by simpa using he) p hp⟩

end
end IsoProof
