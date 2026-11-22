import IsoProof.ContourPhase
import IsingBulk.Analysis.BranchUpper
import IsingBulk.Preferred22.Physical
import Mathlib.Topology.Connected.TotallyDisconnected

/-! The continued sheet agrees with the actual physical root before
contour deformation. The proof uses continuity and the two algebraic
square roots, with no branch-choice assertion supplied as a premise. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set

theorem upper_all_mem_contourRootDomain {W : ℂ} (hW : 0 < W.im) :
    W ∈ contourRootDomain := by
  constructor
  · left
    simpa using hW
  · right
    simpa using hW.ne'

theorem one_sub_square_slit_upper {W : ℂ} (hW : 0 < W.im) :
    1-W^2 ∈ Complex.slitPlane := by
  by_cases hr : W.re=0
  · left
    simp only [Complex.sub_re,Complex.one_re,pow_two,Complex.mul_re,hr,zero_mul]
    nlinarith [sq_nonneg W.im]
  · right
    intro h
    simp only [Complex.sub_im,Complex.one_im,pow_two,Complex.mul_im] at h
    exact mul_ne_zero hr hW.ne' (by nlinarith)

/-- Continuous nonvanishing square roots on a connected set cannot switch
sign. A finite-valued continuous ratio makes the sheet argument explicit. -/
theorem continuous_square_root_unique {α : Type*} [TopologicalSpace α]
    {S : Set α} (hS : IsPreconnected S) (f g : α → ℂ)
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hg0 : ∀ x ∈ S, g x ≠ 0) (hsq : ∀ x ∈ S, (f x)^2=(g x)^2)
    {a : α} (ha : a ∈ S) (he : f a=g a) : EqOn f g S := by
  let h := fun x => f x/g x
  have hc : ContinuousOn h S := hf.div hg hg0
  have hmap : MapsTo h S ({1,-1} : Set ℂ) := by
    intro x hx
    have hp : (h x)^2=1 := by
      dsimp [h]
      rw [div_pow,hsq x hx,div_self (pow_ne_zero _ (hg0 x hx))]
    have hfac : (h x-1)*(h x+1)=0 := by linear_combination hp
    rcases mul_eq_zero.mp hfac with hh | hh
    · exact Or.inl (sub_eq_zero.mp hh)
    · exact Or.inr (eq_neg_of_add_eq_zero_left hh)
  intro x hx
  have hconst := hS.constant_of_mapsTo (Set.toFinite ({1,-1} : Set ℂ)).isDiscrete hc hmap hx ha
  have hbase : h a=1 := by simp only [h,he,div_self (hg0 a ha)]
  rw [hbase] at hconst
  exact (div_eq_one_iff_eq (hg0 x hx)).mp hconst

theorem continuedTransferRoot_zero : continuedTransferRoot 0 = -Complex.I := by
  have hd : downwardSquareRoot (-1 : ℂ) = Complex.I := by
    simpa using downwardSquareRoot_ofReal_neg (by norm_num : (-1 : ℝ) < 0)
  simp [continuedTransferRoot,hd]

/-- Exact equality with the full upper-half-plane inverse-cosine sheet. -/
theorem continuedTransferRoot_eq_upper {W : ℂ} (hW : 0 < W.im) :
    continuedTransferRoot W = (IsingBulk.Branch.inverseCosineRoot W)⁻¹ := by
  let P : ℝ → ℂ := fun t => (t : ℂ)*W
  have hPc : Continuous P := by fun_prop
  have hPim (t : ℝ) (ht : 0 < t) : 0 < (P t).im := by
    simpa [P] using mul_pos ht hW
  have hDom (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : P t ∈ contourRootDomain := by
    by_cases ht0 : t=0
    · subst t
      simpa [P] using real_mem_contourRootDomain (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) ≠ 1)
    · exact upper_all_mem_contourRootDomain (hPim t (lt_of_le_of_ne ht.1 (Ne.symm ht0)))
  have hSlit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1-(P t)^2 ∈ Complex.slitPlane := by
    by_cases ht0 : t=0
    · subst t
      simp [P,Complex.slitPlane]
    · exact one_sub_square_slit_upper (hPim t (lt_of_le_of_ne ht.1 (Ne.symm ht0)))
  let f : ℝ → ℂ := fun t => continuedTransferRoot (P t)-P t
  let g : ℝ → ℂ := fun t => -Complex.I*Complex.sqrt (1-(P t)^2)
  have hf : ContinuousOn f (Icc 0 1) := by
    apply ContinuousOn.sub _ hPc.continuousOn
    intro t ht
    exact (continuedTransferRoot_analyticAt (hDom t ht)).continuousAt.comp_continuousWithinAt
      (f := P) hPc.continuousWithinAt
  have hg : ContinuousOn g (Icc 0 1) := by
    apply ContinuousOn.mul continuousOn_const
    intro t ht
    exact (Complex.differentiableAt_sqrt (hSlit t ht)).continuousAt.comp_continuousWithinAt
      (f := fun t => 1-(P t)^2) (continuous_const.sub (hPc.pow 2)).continuousWithinAt
  have hgsq (t : ℝ) : (g t)^2=(P t)^2-1 := by
    dsimp [g]
    rw [mul_pow,neg_sq,Complex.I_sq,complex_sqrt_square]
    ring
  have hg0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t ≠ 0 := by
    intro hgzero
    have hh := hgsq t
    rw [hgzero,zero_pow (by decide)] at hh
    exact contourRootDomain_sq_ne_one (hDom t ht) (by linear_combination -hh)
  have hsq (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : (f t)^2=(g t)^2 := by
    rw [hgsq]
    dsimp [f]
    linear_combination continuedTransferRoot_quadratic (P t)
  have he : f 0=g 0 := by simp [f,g,P,continuedTransferRoot_zero]
  have ht := continuous_square_root_unique isPreconnected_Icc f g hf hg hg0 hsq
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) he (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  dsimp [f,g,P] at ht
  simp only [one_mul] at ht
  rw [IsingBulk.Branch.inverseCosineRoot_inverse]
  linear_combination ht

theorem continuedTransferRoot_upper_norm {W : ℂ} (hW : 0 < W.im) :
    ‖continuedTransferRoot W‖ < 1 := by
  rw [continuedTransferRoot_eq_upper hW,norm_inv]
  exact inv_lt_one_of_one_lt₀ (IsingBulk.Branch.inverseCosineRoot_norm_of_upper hW)

theorem continuedTransferRoot_eq_physicalRoot {W : ℂ} (hW : 0 < W.im) :
    continuedTransferRoot W = IsingBulk.Preferred22.physicalRoot W := by
  exact IsingBulk.Preferred22.root_unique_in_disk (continuedTransferRoot_trace W)
    (IsingBulk.Preferred22.physicalRoot_trace W) (continuedTransferRoot_ne_zero W)
    (IsingBulk.Preferred22.physicalRoot_ne_zero W) (continuedTransferRoot_upper_norm hW)
    (IsingBulk.Preferred22.physicalRoot_inside (Or.inl hW.ne'))

theorem continuedPhase_eq_lowerArccos {W : ℂ} (hW : 0 < W.im) :
    continuedPhase W = IsingBulk.Branch.lowerArccos W := by
  have harg : (IsingBulk.Branch.inverseCosineRoot W).arg ≠ Real.pi :=
    (Complex.arg_lt_pi_iff.mpr
      (Or.inr (IsingBulk.Branch.inverseCosineRoot_im_pos_of_upper hW).ne')).ne
  rw [continuedPhase,continuedTransferRoot_eq_upper hW,Complex.log_inv _ harg,
    IsingBulk.Branch.lowerArccos]
  ring

theorem continuedPhase_upper_sheet {W : ℂ} (hW : 0 < W.im) :
    0 < (continuedPhase W).re ∧ (continuedPhase W).re < Real.pi ∧
      (continuedPhase W).im < 0 := by
  rw [continuedPhase_eq_lowerArccos hW]
  exact (IsingBulk.Branch.lowerArccos_sheet_of_upper hW).2

end
end IsoProof
