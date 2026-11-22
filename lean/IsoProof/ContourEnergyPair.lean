import IsoProof.ContourEnergy

/-! Lipschitz control between two points of the protected energy disk.
This permits a fixed real-energy displacement followed by the shrinking
Cauchy displacement without introducing a factor growing with A. -/
namespace IsoProof
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

theorem compact_phase_energy_pair_lipschitz {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) (W : α → ℂ) (hW : Continuous W) (R : ℝ)
    (hDom : ∀ t∈K, ∀ e : ℂ, ‖e‖ ≤ R → W t+e∈contourRootDomain) :
    ∃ D > 0, ∀ t∈K, ∀ e₀ e₁ : ℂ, ‖e₀‖ ≤ R → ‖e₁‖ ≤ R →
      ‖continuedPhase (W t+e₁)-continuedPhase (W t+e₀)‖ ≤ D*‖e₁-e₀‖ := by
  let T := Metric.closedBall (0 : ℂ) R ×ˢ K
  have hT : IsCompact T := (isCompact_closedBall (0 : ℂ) R).prod hK
  have hD (p : ℂ × α) (hp : p∈T) : W p.2+p.1∈contourRootDomain :=
    hDom p.2 hp.2 p.1 (by simpa using hp.1)
  have hV : Continuous (fun p : ℂ × α => W p.2+p.1) :=
    (hW.comp continuous_snd).add continuous_fst
  have hφ : ContinuousOn (fun p : ℂ × α => continuedPhase (W p.2+p.1)) T := by
    intro p hp
    exact (continuedPhase_analyticAt (hD p hp)).continuousAt.comp_continuousWithinAt
      (f := fun p : ℂ × α => W p.2+p.1) hV.continuousWithinAt
  have hs := Complex.continuous_sin.comp_continuousOn hφ
  have hi := hs.inv₀ (fun p hp => continuedPhase_sin_ne_zero (hD p hp))
  obtain ⟨D₀,hD₀⟩ := hT.bddAbove_image hi.norm
  let D := max 1 D₀
  refine ⟨D,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro t ht e₀ e₁ he₀ he₁
  have hdF (e : ℂ) (he : e∈Metric.closedBall (0 : ℂ) R) :
      HasDerivAt (fun e => continuedPhase (W t+e))
        (-1/Complex.sin (continuedPhase (W t+e))) e := by
    simpa only [Function.comp_def,mul_one] using!
      (continuedPhase_hasDerivAt (hDom t ht e (by simpa using he))).comp e
        ((hasDerivAt_id e).const_add (W t))
  have hbound (e : ℂ) (he : e∈Metric.closedBall (0 : ℂ) R) :
      ‖deriv (fun e => continuedPhase (W t+e)) e‖ ≤ D := by
    rw [(hdF e he).deriv]
    have h := (hD₀ (mem_image_of_mem _ (show (e,t)∈T from ⟨he,ht⟩))).trans
      (le_max_right 1 D₀)
    simpa only [Pi.inv_apply,Function.comp_def,norm_div,norm_neg,norm_one,one_div,norm_inv,D] using h
  exact (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le
    (fun e he => (hdF e he).differentiableAt) hbound
    (by simpa using he₀) (by simpa using he₁)

end
end IsoProof
