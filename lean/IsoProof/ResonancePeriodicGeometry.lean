import IsoProof.ResonanceSmoothContour
import IsoProof.ResonanceFiniteDensity

/-! Periodic representatives of the constrained angular cycle.  The
independent angles and their dependent last angle may have different winding
numbers; all of them are retained when transferring the compact pole gaps. -/
namespace IsoProof
noncomputable section
open Complex Filter Set Function
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

local instance : Fact (0<(2*Real.pi:ℝ)) := ⟨by positivity⟩

def principalContourAngle (r : ℝ) : ℝ :=
  AddCircle.equivIco (2*Real.pi) (-Real.pi) (r : AddCircle (2*Real.pi))

theorem principalContourAngle_mem (r : ℝ) : principalContourAngle r∈Icc (-Real.pi) Real.pi := by
  have h := (AddCircle.equivIco (2*Real.pi) (-Real.pi) (r : AddCircle (2*Real.pi))).prop
  exact ⟨h.1,by dsimp [principalContourAngle]; linarith [h.2]⟩

theorem principalContourAngle_coe (r : ℝ) :
    ((principalContourAngle r:ℝ):AddCircle (2*Real.pi))=(r : AddCircle (2*Real.pi)) :=
  AddCircle.coe_equivIco

theorem periodic_principalContourAngle {Y : Type*} {f : ℝ→Y}
    (hf : Function.Periodic f (2*Real.pi)) (r : ℝ) : f (principalContourAngle r)=f r := by
  have h := congrArg hf.lift (principalContourAngle_coe r)
  simpa only [Function.Periodic.lift_coe] using h

theorem periodicContourDisplacement_eq_principal {b : ℝ} (hbpi : b<Real.pi) (r : ℝ) :
    periodicContourDisplacement b r=contourDisplacement b (principalContourAngle r) := by
  rw [←periodic_principalContourAngle (periodicContourDisplacement_periodic b) r]
  exact periodicContourDisplacement_agrees hbpi (principalContourAngle_mem r)

theorem real_complex_exp_angle_periodic :
    Function.Periodic (fun r : ℝ=>Complex.exp ((r:ℂ)*Complex.I)) (2*Real.pi) := by
  intro r
  dsimp only
  rw [show ((r+2*Real.pi:ℝ):ℂ)*Complex.I=(r:ℂ)*Complex.I+2*Real.pi*Complex.I by push_cast; ring,
    Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

theorem real_shifted_complex_cos_periodic (h : ℂ) :
    Function.Periodic (fun r : ℝ=>Complex.cos ((r:ℂ)+h)) (2*Real.pi) := by
  intro r
  change Complex.cos (((r+2*Real.pi:ℝ):ℂ)+h)=Complex.cos ((r:ℂ)+h)
  rw [show (((r+2*Real.pi:ℝ):ℂ)+h)=((r:ℂ)+h)+2*Real.pi by push_cast; ring,
    Complex.cos_add_two_pi]

theorem exp_real_sum {N : ℕ} (r : Fin N→ℝ) :
    Complex.exp ((((∑i,r i):ℝ):ℂ)*Complex.I)=∏i,Complex.exp ((r i:ℂ)*Complex.I) := by
  rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]

theorem principal_tuple_mem_constrainedAngularTorus {N : ℕ} {σ : Sign}
    (r : Fin N→ℝ)
    (hphase : Complex.exp ((((∑i,r i):ℝ):ℂ)*Complex.I)=signValue σ) :
    (fun i=>principalContourAngle (r i))∈constrainedAngularTorus N σ := by
  refine ⟨fun i=>principalContourAngle_mem (r i),?_⟩
  rw [exp_real_sum]
  simp only [periodic_principalContourAngle real_complex_exp_angle_periodic]
  rw [←exp_real_sum,hphase]

theorem constrainedGraph_cos_eq_principal {b : ℝ} (hbpi : b<Real.pi)
    {N : ℕ} (r : Fin N→ℝ) (v : ℝ) (i : Fin N) :
    Complex.cos (constrainedGraph (periodicContourDisplacement b) r v i)=
      Complex.cos (constrainedGraph (contourDisplacement b)
        (fun j=>principalContourAngle (r j)) v i) := by
  have hc : contourCenter (periodicContourDisplacement b) r=
      contourCenter (contourDisplacement b) (fun j=>principalContourAngle (r j)) := by
    simp only [contourCenter,periodicContourDisplacement_eq_principal hbpi]
  unfold constrainedGraph
  rw [hc,periodicContourDisplacement_eq_principal hbpi]
  exact (periodic_principalContourAngle (real_shifted_complex_cos_periodic _) (r i)).symm

/-- No angular winding component is lost when transferring the protected
compact torus to the literal N−1 independent-coordinate integral. -/
theorem finiteAngularDomain_periodic_graph {N : ℕ} {σ : Sign} {b : ℝ} (hbpi : b<Real.pi)
    {E : ℂ} {v : ℝ} (r : Fin N→ℝ)
    (hphase : Complex.exp ((((∑i,r i):ℝ):ℂ)*Complex.I)=signValue σ)
    (hgood : ∀q∈constrainedAngularTorus N σ,
      (E,constrainedGraph (contourDisplacement b) q v)∈finiteAngularDomain N σ) :
    (E,constrainedGraph (periodicContourDisplacement b) r v)∈finiteAngularDomain N σ := by
  have h := hgood _ (principal_tuple_mem_constrainedAngularTorus r hphase)
  simpa only [finiteAngularDomain,mem_ofPred_eq,continuedAngularRoot,
    constrainedGraph_cos_eq_principal hbpi] using h

def constrainedComplexAngles (σ : Sign) (n : ℕ) (q : Fin n→ℂ) : Fin (n+1)→ℂ :=
  Fin.snoc q ((signAngle σ:ℂ)-∑i,q i)

theorem constrainedComplexAngles_real (σ : Sign) (n : ℕ) (q : Fin n→ℝ) :
    constrainedComplexAngles σ n (fun i=>(q i:ℂ))=fun i=>(constrainedAngles σ n q i:ℂ) := by
  ext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp [constrainedComplexAngles,constrainedAngles]
  · simp [constrainedComplexAngles,constrainedAngles]

theorem constrainedAngles_phase (σ : Sign) (n : ℕ) (q : Fin n→ℝ) :
    Complex.exp ((((∑i,constrainedAngles σ n q i):ℝ):ℂ)*Complex.I)=signValue σ := by
  rw [constrainedAngles_total]
  cases σ <;> simp [signAngle,signValue,Complex.exp_pi_mul_I]

/-- The smooth homotopy is represented in the N−1 independent complex
coordinates; its full dependent coordinate is the same exact balanced graph. -/
def smoothConstrainedHomotopy (σ : Sign) (n : ℕ) (g : ℝ→ℝ) (v : ℝ)
    (x : Fin (n+1)→ℝ) : Fin n→ℂ :=
  fun i=>constrainedGraph g (constrainedAngles σ n (fun j=>x j.succ)) (x 0*v) i.castSucc

theorem smoothConstrainedHomotopy_full (σ : Sign) (n : ℕ) (g : ℝ→ℝ) (v : ℝ)
    (x : Fin (n+1)→ℝ) :
    constrainedComplexAngles σ n (smoothConstrainedHomotopy σ n g v x)=
      constrainedGraph g (constrainedAngles σ n (fun j=>x j.succ)) (x 0*v) := by
  have hsum := constrainedGraph_sum (show 0<n+1 by omega) g
    (constrainedAngles σ n (fun j=>x j.succ)) (x 0*v)
  rw [constrainedAngles_total] at hsum
  rw [Fin.sum_univ_castSucc] at hsum
  ext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [constrainedComplexAngles,Fin.snoc_last,smoothConstrainedHomotopy]
    linear_combination -hsum
  · simp only [constrainedComplexAngles,Fin.snoc_castSucc,smoothConstrainedHomotopy]

theorem constrainedAngles_contDiff (σ : Sign) (n : ℕ) : ContDiff ℝ ∞ (constrainedAngles σ n) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [constrainedAngles,Fin.snoc_last]
    fun_prop
  · simp only [constrainedAngles,Fin.snoc_castSucc]
    fun_prop

theorem smoothConstrainedHomotopy_contDiff (σ : Sign) (n : ℕ) {g : ℝ→ℝ}
    (hg : ContDiff ℝ ∞ g) (v : ℝ) : ContDiff ℝ ∞ (smoothConstrainedHomotopy σ n g v) := by
  have hco := constrainedAngles_contDiff σ n
  have hcast : ContDiff ℝ ∞ (fun t : ℝ=>(t:ℂ)) := Complex.ofRealCLM.contDiff
  unfold smoothConstrainedHomotopy constrainedGraph contourCenter
  fun_prop

theorem smoothConstrainedHomotopy_zero (σ : Sign) (n : ℕ) (g : ℝ→ℝ) (v : ℝ)
    (q : Fin n→ℝ) : smoothConstrainedHomotopy σ n g v (Fin.cons 0 q)=fun i=>(q i:ℂ) := by
  funext i
  simp [smoothConstrainedHomotopy,constrainedGraph,constrainedAngles]

/-- Periodicity upgrades compact bump approximation to a uniform bound on
all real angular representatives. -/
theorem contourDisplacement_smooth_periodic_uniform_approx {b : ℝ}
    (hb : 0≤b) (hbpi : b<Real.pi) {ε : ℝ} (hε : 0<ε) :
    ∃g : ℝ→ℝ,ContDiff ℝ ∞ g ∧ Function.Periodic g (2*Real.pi) ∧
      ∀x,dist (g x) (periodicContourDisplacement b x)<ε := by
  obtain ⟨g,hg,hgp,happrox⟩ := contourDisplacement_smooth_periodic_approx hb hbpi
    (isCompact_Icc (a:= -Real.pi) (b:=Real.pi)) hε
  refine ⟨g,hg,hgp,?_⟩
  intro x
  have h := happrox (principalContourAngle x) (principalContourAngle_mem x)
  rwa [periodic_principalContourAngle hgp,
    periodic_principalContourAngle (periodicContourDisplacement_periodic b)] at h

end
end IsoProof
