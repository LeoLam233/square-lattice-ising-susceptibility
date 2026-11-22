import IsoProof.IntegralsGraphContour
import IsingBulk.First.AngularFubini
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact-domain Fubini for the actual piecewise graph functional.
Only continuity on the integration boxes is required. -/
namespace IsoProof
noncomputable section
open Set MeasureTheory

set_option backward.isDefEq.respectTransparency false in
theorem weighted_interval_box_fubini {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (l r : ℝ) (hlr : l ≤ r) (J : ℂ) (H : ℝ × (Fin n → ℝ) → ℂ)
    (hH : ContinuousOn H (Icc l r ×ˢ K)) :
    IntegrableOn (fun q => ∫ u : ℝ in l..r, H (u,q)*J) K ∧
    (∫ q in K, ∫ u : ℝ in l..r, H (u,q)*J) =
      ∫ u : ℝ in l..r, (∫ q in K, H (u,q))*J := by
  let G : ℝ × (Fin n → ℝ) → ℂ := fun p => H p*J
  have hG : ContinuousOn G (Icc l r ×ˢ K) := hH.mul continuousOn_const
  have hGi : IntegrableOn G (Icc l r ×ˢ K) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hG.integrableOn_compact (isCompact_Icc.prod hK)
  have hi : Integrable G ((volume.restrict (Icc l r)).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, IntegrableOn] using hGi
  have he (q : Fin n → ℝ) : (∫ u : ℝ in l..r, H (u,q)*J) =
      ∫ u in Icc l r, G (u,q) := by
    rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc]
  constructor
  · simpa only [he, IntegrableOn] using hi.integral_prod_right
  · simp only [he]
    rw [← integral_integral_swap hi]
    rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u _
    dsimp only [G]
    rw [integral_mul_const]

set_option backward.isDefEq.respectTransparency false in
theorem protectedGraphIntegral_box_fubini {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v c : ℝ)
    (F : ℂ → (Fin n → ℝ) → ℂ)
    (hF : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => F (scalarGraph b v p.1 c) p.2)
      (Icc (-Real.pi) Real.pi ×ˢ K)) :
    (∫ q in K, protectedGraphIntegral (fun z => F z q) b v c) =
      protectedGraphIntegral (fun z => ∫ q in K, F z q) b v c := by
  let J : ℂ := 1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))
  let J₀ : ℂ := 1+Complex.I*(v : ℂ)
  let H : ℝ × (Fin n → ℝ) → ℂ := fun p => F (scalarGraph b v p.1 c) p.2
  have hleft : ContinuousOn H (Icc (-Real.pi) (-b) ×ˢ K) :=
    hF.mono (Set.prod_mono (Icc_subset_Icc le_rfl (by linarith)) (Subset.refl _))
  have hmid : ContinuousOn H (Icc (-b) b ×ˢ K) :=
    hF.mono (Set.prod_mono (Icc_subset_Icc (by linarith) hbpi.le) (Subset.refl _))
  have hright : ContinuousOn H (Icc b Real.pi ×ˢ K) :=
    hF.mono (Set.prod_mono (Icc_subset_Icc (by linarith) le_rfl) (Subset.refl _))
  obtain ⟨hI₁,h₁⟩ := weighted_interval_box_fubini hK (-Real.pi) (-b) (by linarith) J H hleft
  obtain ⟨hI₂,h₂⟩ := weighted_interval_box_fubini hK (-b) b (by linarith) J₀ H hmid
  obtain ⟨hI₃,h₃⟩ := weighted_interval_box_fubini hK b Real.pi hbpi.le J H hright
  simp only [protectedGraphIntegral_eq_graph hb hbpi]
  change (∫ q in K, ((∫ u : ℝ in (-Real.pi)..(-b), H (u,q)*J) +
      (∫ u : ℝ in (-b)..b, H (u,q)*J₀)) + (∫ u : ℝ in b..Real.pi, H (u,q)*J)) = _
  have hadd₁ := integral_add (hI₁.add hI₂) hI₃
  have hadd₂ := integral_add hI₁ hI₂
  simp only [Pi.add_apply] at hadd₁ hadd₂
  rw [hadd₁, hadd₂, h₁, h₂, h₃]

end
end IsoProof
