import IsoProof.ResonanceConstrainedStokes
import IsoProof.SiteSummation

/-! Actual finite-order continuation across prime cut energies.  The analytic
extension is a fixed smooth constrained contour integral; Stokes identifies
it with the literal particle coefficient on an open upper neighborhood,
and analytic uniqueness then gives the entire upper half disk. -/
namespace IsoProof
noncomputable section
open Complex Filter Set MeasureTheory Function Metric
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def smoothConstrainedJacobian (σ : Sign) (n : ℕ) (g : ℝ→ℝ) (v t : ℝ)
    (θ : Fin n→ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j=>fderiv ℝ (smoothConstrainedHomotopy σ n g v)
    (Fin.cons t θ) (Pi.single i.succ 1) j

def smoothConstrainedCoefficient (σ : Sign) (n : ℕ) (g : ℝ→ℝ) (v t : ℝ) (E : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
    ∫θ in Icc (fun _ : Fin n=>-Real.pi) (fun _=>Real.pi),
      (smoothConstrainedJacobian σ n g v t θ).det *
        constrainedContinuedDensity σ n E (smoothConstrainedHomotopy σ n g v (Fin.cons t θ))

theorem smoothConstrainedJacobian_zero (σ : Sign) (n : ℕ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (v : ℝ) (θ : Fin n→ℝ) :
    smoothConstrainedJacobian σ n g v 0 θ=1 := by
  have hH := (smoothConstrainedHomotopy_contDiff σ n hg v).differentiable (by simp)
  have hd (q : Fin n) :
      fderiv ℝ (smoothConstrainedHomotopy σ n g v) (Fin.cons 0 θ) (Pi.single q.succ 1)=
        fun j=>if j=q then 1 else 0 := by
    have hh := (hH (Fin.cons 0 θ)).hasFDerivAt.comp_hasDerivAt_of_eq (θ q)
      (hasDerivAt_update (Fin.cons 0 θ) q.succ (θ q)) (by simp)
    have he : (fun t=>smoothConstrainedHomotopy σ n g v (Function.update (Fin.cons 0 θ) q.succ t))=
        fun t j=>(Function.update θ q t j:ℂ) := by
      funext t j
      have hq : (0:Fin (n+1))≠q.succ := (Fin.succ_ne_zero q).symm
      simp [smoothConstrainedHomotopy,constrainedGraph,constrainedAngles,Function.update_apply,hq]
    simp only [Function.comp_def] at hh
    rw [he] at hh
    have hl : HasDerivAt (fun t j=>(Function.update θ q t j:ℂ))
        (fun j=>if j=q then 1 else 0) (θ q) := by
      apply hasDerivAt_pi.mpr
      intro j
      by_cases hj : j=q
      · subst j
        convert! Complex.ofRealCLM.hasDerivAt (x:=θ q) using 1 <;> simp
        rfl
      · simpa [Function.update_of_ne hj,hj] using hasDerivAt_const (θ q) (θ j:ℂ)
    exact hh.unique hl
  ext i j
  simp only [smoothConstrainedJacobian,hd,Matrix.one_apply]
  by_cases hij : i=j
  · subst j
    simp
  · simp [hij,Ne.symm hij]

theorem smoothConstrainedCoefficient_eq_cap (σ : Sign) (n : ℕ) (g : ℝ→ℝ) (v t : ℝ) (E : ℂ) :
    smoothConstrainedCoefficient σ n g v t E=
      ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
        IsingBulk.Preferred22.cylinderCapIntegral (smoothConstrainedPullback σ n E g v)
          (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n) t := by
  unfold smoothConstrainedCoefficient IsingBulk.Preferred22.cylinderCapIntegral
  simp only [IsingBulk.Preferred22.homotopyBoxLower,IsingBulk.Preferred22.homotopyBoxUpper,
    Function.comp_def,Fin.succAbove_zero,Fin.cons_succ,Fin.insertNth_zero',Fin.removeNth_zero,
    smoothConstrainedPullback,densityForm_chainPullback]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  exact mul_comm _ _

theorem constrainedContinuedDensity_real_continuous (σ : Sign) (n : ℕ)
    {E : ℂ} (hE : 0<E.im) :
    Continuous (fun θ : Fin n→ℝ=>constrainedContinuedDensity σ n E (fun i=>(θ i:ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hgood : (E,constrainedComplexAngles σ n (fun i=>(θ i:ℂ)))∈finiteAngularDomain (n+1) σ := by
    rw [constrainedComplexAngles_real]
    exact real_angles_upper_mem_finiteAngularDomain (by omega) σ hE _
  exact (constrainedContinuedDensity_analyticAt σ n E _ hgood).continuousAt.comp
    (f:=fun θ : Fin n→ℝ=>fun i=>(θ i:ℂ))
    ((continuous_pi (fun i=>Complex.continuous_ofReal.comp (continuous_apply i))).continuousAt)

theorem constrainedContinuedDensity_real_periodic (σ : Sign) (n : ℕ) (E : ℂ) :
    IsingBulk.First.CoordinatePeriodic n
      (fun θ : Fin n→ℝ=>constrainedContinuedDensity σ n E (fun i=>(θ i:ℂ))) := by
  intro θ i
  have he : (fun j=>(Function.update θ i (θ i+2*Real.pi) j:ℂ))=
      (fun j=>(θ j:ℂ))+Pi.single i (2*Real.pi) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp
    · simp [Function.update_of_ne hji,Pi.single_eq_of_ne hji]
  dsimp only
  rw [he,constrainedContinuedDensity_periodic]

theorem smoothConstrainedCoefficient_zero (σ : Sign) (n : ℕ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (v : ℝ) {E : ℂ} (hE : 0<E.im) :
    smoothConstrainedCoefficient σ n g v 0 E=particleCoefficient σ (n+1) E := by
  unfold smoothConstrainedCoefficient
  simp_rw [smoothConstrainedJacobian_zero σ n hg v,Matrix.det_one,one_mul,
    smoothConstrainedHomotopy_zero]
  have hbox : IsingBulk.Preferred22.angularBox n =ᵐ[(volume : Measure (Fin n→ℝ))]
      Icc (fun _ : Fin n=>-Real.pi) (fun _=>Real.pi) := Measure.univ_pi_Ioc_ae_eq_Icc
  have hi : (∫θ in Icc (fun _ : Fin n=>-Real.pi) (fun _=>Real.pi),
      constrainedContinuedDensity σ n E (fun i=>(θ i:ℂ)))=
      IsingBulk.First.multiAngleIntegral n (fun θ=>constrainedContinuedDensity σ n E (fun i=>(θ i:ℂ))) := by
    calc
      _ = ∫θ in IsingBulk.Preferred22.angularBox n,
          constrainedContinuedDensity σ n E (fun i=>(θ i:ℂ)) := by
        convert! (setIntegral_congr_set (f:=fun θ=>constrainedContinuedDensity σ n E (fun i=>(θ i:ℂ))) hbox).symm using 1
      _ = _ := IsingBulk.Preferred22.angularBox_integral_eq_multiAngleIntegral _
        (constrainedContinuedDensity_real_continuous σ n hE)
        (constrainedContinuedDensity_real_periodic σ n E)
  rw [hi]
  simp only [constrainedContinuedDensity,constrainedComplexAngles_real,
    continuedParticleDensity_eq_actual σ hE]
  simp only [particleCoefficient,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,
    Nat.add_sub_cancel]
  convert! rfl using 1

theorem smoothConstrainedCoefficient_eq_particle (σ : Sign) (n : ℕ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : Periodic g (2*Real.pi)) (v : ℝ)
    {E : ℂ} (hE : 0<E.im)
    (hgood : ∀x∈Icc (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n),
      (E,constrainedComplexAngles σ n (smoothConstrainedHomotopy σ n g v x))∈finiteAngularDomain (n+1) σ) :
    smoothConstrainedCoefficient σ n g v 1 E=particleCoefficient σ (n+1) E := by
  rw [smoothConstrainedCoefficient_eq_cap,
    smooth_constrained_homotopy_caps σ n E hg hgp v hgood,
    ←smoothConstrainedCoefficient_eq_cap,smoothConstrainedCoefficient_zero σ n hg v hE]

theorem smoothConstrainedJacobian_continuous (σ : Sign) (n : ℕ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (v t : ℝ) : Continuous (smoothConstrainedJacobian σ n g v t) := by
  have hH := (smoothConstrainedHomotopy_contDiff σ n hg v).continuous_fderiv_apply (by simp)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hc : Continuous (fun θ : Fin n→ℝ =>
      ((Fin.cons t θ : Fin (n+1)→ℝ),(Pi.single i.succ (1:ℝ) : Fin (n+1)→ℝ))) := by fun_prop
  exact (continuous_apply j).comp (hH.comp hc)

theorem smoothConstrainedCoefficient_analyticOnNhd (σ : Sign) (n : ℕ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (v t : ℝ) {U : Set ℂ} (hU : IsOpen U)
    (hgood : ∀E∈U,∀θ∈Icc (fun _ : Fin n=>-Real.pi) (fun _=>Real.pi),
      (E,constrainedComplexAngles σ n (smoothConstrainedHomotopy σ n g v (Fin.cons t θ)))
        ∈finiteAngularDomain (n+1) σ) :
    AnalyticOnNhd ℂ (smoothConstrainedCoefficient σ n g v t) U := by
  intro E hE
  apply analyticAt_const.mul
  exact IsingBulk.First.compact_analytic_shape_integral_analyticAt isCompact_Icc hU
    (@continuedParticleDensity σ (n+1))
    (fun θ=>constrainedComplexAngles σ n (smoothConstrainedHomotopy σ n g v (Fin.cons t θ)))
    (by
      have hcc : Continuous (constrainedComplexAngles σ n) :=
        continuous_iff_continuousAt.mpr (fun q=>(constrainedComplexAngles_analyticAt σ n q).continuousAt)
      exact hcc.comp ((smoothConstrainedHomotopy_contDiff σ n hg v).continuous.comp (by fun_prop)))
    (fun θ=>(smoothConstrainedJacobian σ n g v t θ).det)
    (smoothConstrainedJacobian_continuous σ n hg v t).matrix_det
    (fun z hz θ hθ=>continuedParticleDensity_analyticAt (hgood z hz θ hθ)) hE

end
end IsoProof
