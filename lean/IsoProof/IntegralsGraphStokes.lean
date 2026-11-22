import IsingBulk.Anisotropic.NegativeCycles.DensityForm
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Finite-dimensional contour transport for actual affine graph pieces.
The analyticity hypothesis is local on the displayed homotopy image. It is
not an assumption that either contour integral is invariant. -/
namespace IsoProof
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology
open IsingBulk.Anisotropic.NegativeCycles

/-- t is coordinate zero, and the real angle is coordinate one. -/
def affineGraphHomotopy (a b : ℝ) (x : Fin 2 → ℝ) : Fin 1 → ℂ :=
  fun _ => (x 1 : ℂ) + Complex.I*((x 0 : ℂ)*((a : ℂ)*(x 1 : ℂ)+(b : ℂ)))

theorem affineGraphHomotopy_contDiff (a b : ℝ) :
    ContDiff ℝ ∞ (affineGraphHomotopy a b) := by
  have h0 : ContDiff ℝ ∞ (fun x : Fin 2 → ℝ => (x 0 : ℂ)) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)).contDiff
  have h1 : ContDiff ℝ ∞ (fun x : Fin 2 → ℝ => (x 1 : ℂ)) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)).contDiff
  exact contDiff_pi.mpr (fun _ => h1.add
    (contDiff_const.mul (h0.mul ((contDiff_const.mul h1).add contDiff_const))))

theorem affineGraphHomotopy_fderiv (a b : ℝ) (x v : Fin 2 → ℝ) :
    fderiv ℝ (affineGraphHomotopy a b) x v = fun _ =>
      (v 1 : ℂ) + Complex.I*((v 0 : ℂ)*((a : ℂ)*(x 1 : ℂ)+(b : ℂ)) +
        (x 0 : ℂ)*(a : ℂ)*(v 1 : ℂ)) := by
  let L₀ : (Fin 2 → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0)
  let L₁ : (Fin 2 → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)
  have h := (L₁.hasFDerivAt (x := x)).add
    ((L₀.hasFDerivAt.mul ((L₁.hasFDerivAt.const_mul (a : ℂ)).add_const (b : ℂ))).const_mul Complex.I)
  have hpi := hasFDerivAt_pi.mpr (fun _ : Fin 1 => h)
  change HasFDerivAt (affineGraphHomotopy a b) _ x at hpi
  rw [hpi.fderiv]
  funext i
  simp [L₀,L₁]
  ring

/-- One-dimensional parameter-box integration is literally ordinary angle
integration; no measure normalization is hidden in the Stokes adapter. -/
theorem integral_finOne_interval (l r : ℝ) (hlr : l ≤ r) (f : ℝ → ℂ) :
    (∫ x : Fin 1 → ℝ in Icc (fun _ => l) (fun _ => r), f (x 0)) =
      ∫ t : ℝ in l..r, f t := by
  let e : ℝ ≃ᵐ (Fin 1 → ℝ) := (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).symm
  have hem : MeasurePreserving e := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm _
  have hpre : e ⁻¹' Icc (fun _ => l) (fun _ => r) = Icc l r := by
    ext t
    simp [e, Set.mem_Icc, Pi.le_def]
  rw [← hem.map_eq, setIntegral_map_equiv, hpre,
    intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc]
  congr 1

/-- Stokes for a single actual affine graph segment, before opposite side
faces from neighboring graph pieces are canceled. -/
theorem affineGraph_boundary_zero (a b l r T : ℝ) (hlr : l ≤ r) (hT : 0 ≤ T)
    (F : ℂ → ℂ)
    (hF : ∀ t∈Icc 0 T, ∀ u∈Icc l r,
      DifferentiableAt ℂ F ((u : ℂ)+Complex.I*((t : ℂ)*((a : ℂ)*(u : ℂ)+(b : ℂ))))) :
    boxBoundaryFlux
      (chainPullback (densityForm (fun z : Fin 1 → ℂ => F (z 0))) (affineGraphHomotopy a b))
      ![0,l] ![T,r] = 0 := by
  apply holomorphic_chain_boundary_zero
  · intro i
    fin_cases i
    · exact hT
    · exact hlr
  · intro x hx
    apply densityForm_differentiableAt
    exact (hF (x 0) ⟨hx.1 0,hx.2 0⟩ (x 1) ⟨hx.1 1,hx.2 1⟩).comp
      (f := fun z : Fin 1 → ℂ => z 0) (affineGraphHomotopy a b x) (differentiableAt_apply 0 _)
  · intro x _
    exact ((affineGraphHomotopy_contDiff a b).of_le (by simp)).contDiffAt

def affineGraphIntegral (F : ℂ → ℂ) (a b l r T : ℝ) : ℂ :=
  ∫ u : ℝ in l..r,
    F ((u : ℂ)+Complex.I*((T : ℂ)*((a : ℂ)*(u : ℂ)+(b : ℂ)))) *
      (1+Complex.I*((T : ℂ)*(a : ℂ)))

def verticalGraphIntegral (F : ℂ → ℂ) (r h T : ℝ) : ℂ :=
  ∫ t : ℝ in 0..T,
    F ((r : ℂ)+Complex.I*((t : ℂ)*(h : ℂ))) * (Complex.I*(h : ℂ))

set_option backward.isDefEq.respectTransparency false in
theorem affineGraph_face_zero (a b t : ℝ) (F : ℂ → ℂ) (x : Fin 1 → ℝ) :
    chainPullback (densityForm (fun z : Fin 1 → ℂ => F (z 0)))
      (affineGraphHomotopy a b) ((0 : Fin 2).insertNth t x)
      ((0 : Fin 2).removeNth (fun k => (Pi.single k (1 : ℝ) : Fin 2 → ℝ))) =
    F ((x 0 : ℂ)+Complex.I*((t : ℂ)*((a : ℂ)*(x 0 : ℂ)+(b : ℂ)))) *
      (1+Complex.I*((t : ℂ)*(a : ℂ))) := by
  rw [densityForm_chainPullback, Matrix.det_fin_one, affineGraphHomotopy_fderiv]
  simp [affineGraphHomotopy, Fin.removeNth]

set_option backward.isDefEq.respectTransparency false in
theorem affineGraph_face_one (a b r : ℝ) (F : ℂ → ℂ) (x : Fin 1 → ℝ) :
    chainPullback (densityForm (fun z : Fin 1 → ℂ => F (z 0)))
      (affineGraphHomotopy a b) ((1 : Fin 2).insertNth r x)
      ((1 : Fin 2).removeNth (fun k => (Pi.single k (1 : ℝ) : Fin 2 → ℝ))) =
    F ((r : ℂ)+Complex.I*((x 0 : ℂ)*((a : ℂ)*(r : ℂ)+(b : ℂ)))) *
      (Complex.I*((a : ℂ)*(r : ℂ)+(b : ℂ))) := by
  rw [densityForm_chainPullback, Matrix.det_fin_one, affineGraphHomotopy_fderiv]
  simp [affineGraphHomotopy, Fin.removeNth, Fin.insertNth_apply_below]

set_option backward.isDefEq.respectTransparency false in
theorem affineGraph_boundary_evaluation (a b l r T : ℝ) (hlr : l ≤ r) (hT : 0 ≤ T)
    (F : ℂ → ℂ) :
    boxBoundaryFlux
      (chainPullback (densityForm (fun z : Fin 1 → ℂ => F (z 0))) (affineGraphHomotopy a b))
      ![0,l] ![T,r] =
      affineGraphIntegral F a b l r T - (∫ u : ℝ in l..r, F (u : ℂ)) +
        verticalGraphIntegral F l (a*l+b) T - verticalGraphIntegral F r (a*r+b) T := by
  unfold boxBoundaryFlux
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, pow_zero,
    Fin.val_one, pow_one, neg_smul, one_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, affineGraph_face_zero, affineGraph_face_one]
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero,
    mul_one, integral_neg]
  have hs : (1 : Fin 2).succAbove = fun _ : Fin 1 => (0 : Fin 2) := by
    funext i
    fin_cases i
    rfl
  simp only [hs, Function.comp_def, Matrix.cons_val_zero, Fin.succAbove_zero]
  have hl : (fun x : Fin 1 => ![0,l] x.succ) = fun _ => l := by
    funext i
    fin_cases i
    rfl
  have hr : (fun x : Fin 1 => ![T,r] x.succ) = fun _ => r := by
    funext i
    fin_cases i
    rfl
  rw [hl, hr]
  rw [integral_finOne_interval l r hlr (fun u =>
      F ((u : ℂ)+Complex.I*((T : ℂ)*((a : ℂ)*(u : ℂ)+(b : ℂ)))) *
        (1+Complex.I*((T : ℂ)*(a : ℂ)))),
    integral_finOne_interval l r hlr (fun u => F (u : ℂ)),
    integral_finOne_interval 0 T hT (fun t =>
      F ((r : ℂ)+Complex.I*((t : ℂ)*((a : ℂ)*(r : ℂ)+(b : ℂ)))) *
        (Complex.I*((a : ℂ)*(r : ℂ)+(b : ℂ)))),
    integral_finOne_interval 0 T hT (fun t =>
      F ((l : ℂ)+Complex.I*((t : ℂ)*((a : ℂ)*(l : ℂ)+(b : ℂ)))) *
        (Complex.I*((a : ℂ)*(l : ℂ)+(b : ℂ))))]
  simp only [affineGraphIntegral, verticalGraphIntegral, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- Literal contour transport for one affine segment, including its two
vertical sides and its actual angular Jacobian. -/
theorem affineGraph_stokes (a b l r T : ℝ) (hlr : l ≤ r) (hT : 0 ≤ T)
    (F : ℂ → ℂ)
    (hF : ∀ t∈Icc 0 T, ∀ u∈Icc l r,
      DifferentiableAt ℂ F ((u : ℂ)+Complex.I*((t : ℂ)*((a : ℂ)*(u : ℂ)+(b : ℂ))))) :
    affineGraphIntegral F a b l r T - (∫ u : ℝ in l..r, F (u : ℂ)) =
      verticalGraphIntegral F r (a*r+b) T - verticalGraphIntegral F l (a*l+b) T := by
  have h := affineGraph_boundary_zero a b l r T hlr hT F hF
  rw [affineGraph_boundary_evaluation a b l r T hlr hT F] at h
  linear_combination h

private theorem affineGraph_flat_integrable (a b l r T : ℝ)
    (hlr : l ≤ r) (hT : 0 ≤ T) (F : ℂ → ℂ)
    (hF : ∀ t∈Icc 0 T, ∀ u∈Icc l r,
      DifferentiableAt ℂ F ((u : ℂ)+Complex.I*((t : ℂ)*((a : ℂ)*(u : ℂ)+(b : ℂ))))) :
    IntervalIntegrable (fun u : ℝ => F (u : ℂ)) volume l r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hlr
  intro u hu
  have hf := hF 0 ⟨le_rfl,hT⟩ u hu
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero] at hf
  exact (hf.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- Three actual affine graph pieces glue without a corner contribution.
Their internal vertical faces cancel by matching heights; the outside
vertical faces cancel by the stated periodicity. -/
theorem three_piece_periodic_graph_stokes
    (a₁ b₁ a₂ b₂ a₃ b₃ l₀ l₁ l₂ l₃ T : ℝ)
    (h₀₁ : l₀ ≤ l₁) (h₁₂ : l₁ ≤ l₂) (h₂₃ : l₂ ≤ l₃) (hT : 0 ≤ T)
    (h₁ : a₁*l₁+b₁=a₂*l₁+b₂) (h₂ : a₂*l₂+b₂=a₃*l₂+b₃)
    (hends : a₃*l₃+b₃=a₁*l₀+b₁) (F : ℂ → ℂ)
    (hp : Function.Periodic F ((l₃ : ℂ)-(l₀ : ℂ)))
    (hF₁ : ∀ t∈Icc 0 T, ∀ u∈Icc l₀ l₁,
      DifferentiableAt ℂ F ((u : ℂ)+Complex.I*((t : ℂ)*((a₁ : ℂ)*(u : ℂ)+(b₁ : ℂ)))))
    (hF₂ : ∀ t∈Icc 0 T, ∀ u∈Icc l₁ l₂,
      DifferentiableAt ℂ F ((u : ℂ)+Complex.I*((t : ℂ)*((a₂ : ℂ)*(u : ℂ)+(b₂ : ℂ)))))
    (hF₃ : ∀ t∈Icc 0 T, ∀ u∈Icc l₂ l₃,
      DifferentiableAt ℂ F ((u : ℂ)+Complex.I*((t : ℂ)*((a₃ : ℂ)*(u : ℂ)+(b₃ : ℂ))))) :
    affineGraphIntegral F a₁ b₁ l₀ l₁ T +
      affineGraphIntegral F a₂ b₂ l₁ l₂ T +
      affineGraphIntegral F a₃ b₃ l₂ l₃ T =
        ∫ u : ℝ in l₀..l₃, F (u : ℂ) := by
  have hs₁ := affineGraph_stokes a₁ b₁ l₀ l₁ T h₀₁ hT F hF₁
  have hs₂ := affineGraph_stokes a₂ b₂ l₁ l₂ T h₁₂ hT F hF₂
  have hs₃ := affineGraph_stokes a₃ b₃ l₂ l₃ T h₂₃ hT F hF₃
  have hv : verticalGraphIntegral F l₃ (a₃*l₃+b₃) T =
      verticalGraphIntegral F l₀ (a₁*l₀+b₁) T := by
    rw [hends]
    unfold verticalGraphIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show (l₃ : ℂ)+Complex.I*((t : ℂ)*((a₁*l₀+b₁ : ℝ) : ℂ)) =
      ((l₀ : ℂ)+Complex.I*((t : ℂ)*((a₁*l₀+b₁ : ℝ) : ℂ))) +
        ((l₃ : ℂ)-(l₀ : ℂ)) by ring, hp]
  rw [h₁] at hs₁
  rw [h₂] at hs₂
  rw [hv] at hs₃
  have hi₁ := affineGraph_flat_integrable a₁ b₁ l₀ l₁ T h₀₁ hT F hF₁
  have hi₂ := affineGraph_flat_integrable a₂ b₂ l₁ l₂ T h₁₂ hT F hF₂
  have hi₃ := affineGraph_flat_integrable a₃ b₃ l₂ l₃ T h₂₃ hT F hF₃
  have hsflat : (∫ u : ℝ in l₀..l₁, F (u : ℂ)) +
      (∫ u : ℝ in l₁..l₂, F (u : ℂ)) +
      (∫ u : ℝ in l₂..l₃, F (u : ℂ)) =
      ∫ u : ℝ in l₀..l₃, F (u : ℂ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
    exact intervalIntegral.integral_add_adjacent_intervals (hi₁.trans hi₂) hi₃
  linear_combination hs₁+hs₂+hs₃+hsflat

end
end IsoProof
