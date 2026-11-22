import IsoProof.ResonanceSmoothReplacement
import IsingBulk.Preferred22.ContourDeformation
import IsingBulk.Preferred22.HorizontalFourier

/-! Genuine Stokes transport of the coupled constrained smooth cycle.
Every face is retained.  Opposite faces cancel by exact periodicity of the
pullback, and the zero cap is the original normalized particle integral. -/
namespace IsoProof
noncomputable section
open Complex Filter Set MeasureTheory Function
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def constrainedContinuedDensity (σ : Sign) (n : ℕ) (E : ℂ) (q : Fin n→ℂ) : ℂ :=
  continuedParticleDensity σ (E,constrainedComplexAngles σ n q)

theorem constrainedComplexAngles_analyticAt (σ : Sign) (n : ℕ) (q : Fin n→ℂ) :
    AnalyticAt ℂ (constrainedComplexAngles σ n) q := by
  apply analyticAt_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [constrainedComplexAngles,Fin.snoc_last]
    exact analyticAt_const.sub (Finset.univ.analyticAt_fun_sum (fun j _=>
      (ContinuousLinearMap.proj j : (Fin n→ℂ)→L[ℂ]ℂ).analyticAt q))
  · simp only [constrainedComplexAngles,Fin.snoc_castSucc]
    convert! (ContinuousLinearMap.proj j : (Fin n→ℂ)→L[ℂ]ℂ).analyticAt q using 1

theorem constrainedContinuedDensity_analyticAt (σ : Sign) (n : ℕ) (E : ℂ) (q : Fin n→ℂ)
    (hgood : (E,constrainedComplexAngles σ n q)∈finiteAngularDomain (n+1) σ) :
    AnalyticAt ℂ (constrainedContinuedDensity σ n E) q :=
  (continuedParticleDensity_analyticAt hgood).comp
    (f := fun z : Fin n→ℂ => (E,constrainedComplexAngles σ n z))
    (analyticAt_const.prod (constrainedComplexAngles_analyticAt σ n q))

private theorem constrained_complex_periodic {Y : Type*} {f : ℂ→Y}
    (hf : Periodic f (2*Real.pi)) (σ : Sign) (n : ℕ) (q : Fin n→ℂ) (i : Fin n) :
    (fun j=>f (constrainedComplexAngles σ n (q+Pi.single i (2*Real.pi)) j))=
      (fun j=>f (constrainedComplexAngles σ n q j)) := by
  funext j
  refine Fin.lastCases ?_ (fun k=>?_) j
  · simp only [constrainedComplexAngles,Fin.snoc_last,Pi.add_apply,Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    push_cast
    rw [show (signAngle σ:ℂ)-((∑j,q j)+2*Real.pi)=
      ((signAngle σ:ℂ)-∑j,q j)-2*Real.pi by ring]
    exact hf.sub_eq _
  · simp only [constrainedComplexAngles,Fin.snoc_castSucc,Pi.add_apply]
    by_cases hki : k=i
    · subst k
      simpa only [Pi.single_eq_same,Complex.ofReal_mul,Complex.ofReal_ofNat] using hf (q i)
    · simp only [Pi.single_eq_of_ne hki,add_zero]

private theorem complex_exponential_angle_periodic :
    Periodic (fun q : ℂ=>Complex.exp (Complex.I*q)) (2*Real.pi) := by
  intro q
  dsimp only
  rw [mul_add,Complex.exp_add,show Complex.I*(2*Real.pi)=2*Real.pi*Complex.I by ring,
    Complex.exp_two_pi_mul_I,mul_one]

theorem constrainedContinuedDensity_periodic (σ : Sign) (n : ℕ) (E : ℂ)
    (q : Fin n→ℂ) (i : Fin n) :
    constrainedContinuedDensity σ n E (q+Pi.single i (2*Real.pi))=
      constrainedContinuedDensity σ n E q := by
  have hcos := constrained_complex_periodic Complex.cos_periodic σ n q i
  have hexp := constrained_complex_periodic complex_exponential_angle_periodic σ n q i
  have hroot : (fun j=>continuedAngularRoot E (constrainedComplexAngles σ n (q+Pi.single i (2*Real.pi)) j))=
      (fun j=>continuedAngularRoot E (constrainedComplexAngles σ n q j)) := by
    funext j
    unfold continuedAngularRoot
    rw [congrFun hcos j]
  simp only [constrainedContinuedDensity,continuedParticleDensity,hexp,congrFun hroot]

private theorem constrained_real_periodic {g : ℝ→ℝ} (hg : Periodic g (2*Real.pi))
    (σ : Sign) (n : ℕ) (q : Fin n→ℝ) (i : Fin n) :
    (fun j=>g (constrainedAngles σ n (q+Pi.single i (2*Real.pi)) j))=
      (fun j=>g (constrainedAngles σ n q j)) := by
  funext j
  refine Fin.lastCases ?_ (fun k=>?_) j
  · simp only [constrainedAngles,Fin.snoc_last,Pi.add_apply,Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    rw [show signAngle σ-((∑j,q j)+2*Real.pi)=(signAngle σ-∑j,q j)-2*Real.pi by ring]
    exact hg.sub_eq _
  · simp only [constrainedAngles,Fin.snoc_castSucc,Pi.add_apply]
    by_cases hki : k=i
    · subst k
      simpa only [Pi.single_eq_same] using hg (q i)
    · simp only [Pi.single_eq_of_ne hki,add_zero]

private theorem free_graph_periodic {g : ℝ→ℝ} (hg : Periodic g (2*Real.pi))
    (σ : Sign) (n : ℕ) (q : Fin n→ℝ) (i : Fin n) (t : ℝ) :
    (fun j : Fin n=>constrainedGraph g (constrainedAngles σ n (q+Pi.single i (2*Real.pi))) t j.castSucc)=
      (fun j : Fin n=>constrainedGraph g (constrainedAngles σ n q) t j.castSucc)+Pi.single i (2*Real.pi) := by
  have he := constrained_real_periodic hg σ n q i
  have hm : contourCenter g (constrainedAngles σ n (q+Pi.single i (2*Real.pi)))=
      contourCenter g (constrainedAngles σ n q) := by
    unfold contourCenter
    rw [show (∑j,g (constrainedAngles σ n (q+Pi.single i (2*Real.pi)) j))=
      ∑j,g (constrainedAngles σ n q j) from congrArg (fun f : Fin (n+1)→ℝ=>∑j,f j) he]
  funext j
  simp only [constrainedGraph]
  rw [hm,congrFun he j.castSucc]
  simp only [constrainedAngles,Fin.snoc_castSucc,Pi.add_apply]
  by_cases hji : j=i
  · subst j
    simp only [Pi.single_eq_same,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  · simp only [Pi.single_eq_of_ne hji,add_zero]

theorem smoothConstrainedHomotopy_periodic {g : ℝ→ℝ} (hg : Periodic g (2*Real.pi))
    (σ : Sign) (n : ℕ) (v : ℝ) (x : Fin (n+1)→ℝ) (i : Fin n) :
    smoothConstrainedHomotopy σ n g v (x+Pi.single i.succ (2*Real.pi))=
      smoothConstrainedHomotopy σ n g v x+Pi.single i (2*Real.pi) := by
  have hzero : (x+Pi.single i.succ (2*Real.pi) : Fin (n+1)→ℝ) 0=x 0 := by
    simp [Fin.succ_ne_zero]
  have htail : (fun j=>(x+Pi.single i.succ (2*Real.pi) : Fin (n+1)→ℝ) j.succ)=
      (fun j=>x j.succ)+Pi.single i (2*Real.pi) := by
    funext j
    simp [Pi.single_apply,Fin.succ_inj]
  unfold smoothConstrainedHomotopy
  rw [hzero,htail]
  exact free_graph_periodic hg σ n _ i _

theorem smoothConstrainedHomotopy_fderiv_periodic {g : ℝ→ℝ} (hg : Periodic g (2*Real.pi))
    (σ : Sign) (n : ℕ) (v : ℝ) (x : Fin (n+1)→ℝ) (i : Fin n) :
    fderiv ℝ (smoothConstrainedHomotopy σ n g v) (x+Pi.single i.succ (2*Real.pi))=
      fderiv ℝ (smoothConstrainedHomotopy σ n g v) x := by
  have he := congrArg (fun f : (Fin (n+1)→ℝ)→(Fin n→ℂ)=>fderiv ℝ f x)
    (funext (fun y=>smoothConstrainedHomotopy_periodic hg σ n v y i))
  rwa [fderiv_comp_add_right,fderiv_add_const] at he

def smoothConstrainedPullback (σ : Sign) (n : ℕ) (E : ℂ) (g : ℝ→ℝ) (v : ℝ) :=
  chainPullback (densityForm (constrainedContinuedDensity σ n E)) (smoothConstrainedHomotopy σ n g v)

theorem smoothConstrainedPullback_periodic {g : ℝ→ℝ} (hg : Periodic g (2*Real.pi))
    (σ : Sign) (n : ℕ) (E : ℂ) (v : ℝ) (x : Fin (n+1)→ℝ) (i : Fin n) :
    smoothConstrainedPullback σ n E g v (x+Pi.single i.succ (2*Real.pi))=
      smoothConstrainedPullback σ n E g v x := by
  ext w
  simp only [smoothConstrainedPullback,densityForm_chainPullback,
    smoothConstrainedHomotopy_periodic hg,smoothConstrainedHomotopy_fderiv_periodic hg,
    constrainedContinuedDensity_periodic]

/-- Full constrained cylinder Stokes for the actual continued density. -/
theorem smooth_constrained_homotopy_caps (σ : Sign) (n : ℕ) (E : ℂ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : Periodic g (2*Real.pi)) (v : ℝ)
    (hgood : ∀x∈Icc (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n),
      (E,constrainedComplexAngles σ n (smoothConstrainedHomotopy σ n g v x))∈finiteAngularDomain (n+1) σ) :
    IsingBulk.Preferred22.cylinderCapIntegral (smoothConstrainedPullback σ n E g v)
      (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n) 1=
    IsingBulk.Preferred22.cylinderCapIntegral (smoothConstrainedPullback σ n E g v)
      (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n) 0 := by
  have hboundary := holomorphic_chain_boundary_zero
    (densityForm (constrainedContinuedDensity σ n E)) (smoothConstrainedHomotopy σ n g v)
    (IsingBulk.Preferred22.homotopyBox_ordered n)
    (fun x hx=>densityForm_differentiableAt
      (constrainedContinuedDensity_analyticAt σ n E _ (hgood x hx)).differentiableAt)
    (fun x _=>((smoothConstrainedHomotopy_contDiff σ n hg v).of_le (by simp)).contDiffAt)
  have hfaces (i : Fin n) :
      IsingBulk.Preferred22.cylinderFaceFlux (smoothConstrainedPullback σ n E g v)
        (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n) i.succ=0 := by
    unfold IsingBulk.Preferred22.cylinderFaceFlux
    have he (x : Fin n→ℝ) :
        (i.succ.insertNth (IsingBulk.Preferred22.homotopyBoxUpper n i.succ) x : Fin (n+1)→ℝ)=
          (i.succ.insertNth (IsingBulk.Preferred22.homotopyBoxLower n i.succ) x : Fin (n+1)→ℝ)+
            Pi.single i.succ (2*Real.pi) := by
      funext j
      rcases i.succ.eq_self_or_eq_succAbove j with rfl|⟨k,rfl⟩
      · simp [IsingBulk.Preferred22.homotopyBoxUpper,IsingBulk.Preferred22.homotopyBoxLower]
        ring
      · simp [Fin.succAbove_ne]
    simp_rw [he,smoothConstrainedPullback_periodic hgp]
    exact sub_self _
  change boxBoundaryFlux (smoothConstrainedPullback σ n E g v)
    (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n)=0 at hboundary
  rw [IsingBulk.Preferred22.cylinderBoundaryFlux_caps] at hboundary
  simp only [hfaces,Finset.sum_const_zero,add_zero] at hboundary
  exact sub_eq_zero.mp hboundary

end
end IsoProof
