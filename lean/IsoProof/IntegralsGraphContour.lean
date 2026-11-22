import IsoProof.IntegralsGraphStokes
import IsoProof.ContourProtected

/-! The three-piece Stokes theorem instantiated to the literal common
piecewise-linear contour of manuscript Section 3. -/
namespace IsoProof
noncomputable section
open Set

theorem contourDisplacement_left_affine {b r : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (hr : r ≤ -b) :
    contourDisplacement b r = (-b/(Real.pi-b))*r-b*Real.pi/(Real.pi-b) := by
  rw [contourDisplacement_eq_nested hb.le hbpi, ite_eq_left hr]
  ring

theorem contourDisplacement_middle_affine {b r : ℝ} (hr : r ∈ Icc (-b) b) :
    contourDisplacement b r = r :=
  contourDisplacement_interior (abs_le.mpr hr)

theorem contourDisplacement_right_affine {b r : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (hr : b ≤ r) :
    contourDisplacement b r = (-b/(Real.pi-b))*r+b*Real.pi/(Real.pi-b) := by
  by_cases he : r=b
  · subst r
    rw [contourDisplacement_interior (by simp [abs_of_pos hb])]
    field_simp [show Real.pi-b ≠ 0 by linarith]
    ring
  · have hneg : ¬r ≤ -b := by linarith
    have hmid : ¬r ≤ b := by exact not_le.mpr (lt_of_le_of_ne hr (Ne.symm he))
    rw [contourDisplacement_eq_nested hb.le hbpi, ite_eq_right hneg, ite_eq_right hmid]
    ring

/-- Integration over all three pieces, with the literal complex angular
Jacobian on each piece. -/
def protectedGraphIntegral (F : ℂ → ℂ) (b v c : ℝ) : ℂ :=
  affineGraphIntegral F (-b/(Real.pi-b)) (-b*Real.pi/(Real.pi-b)-c) (-Real.pi) (-b) v +
  affineGraphIntegral F 1 (-c) (-b) b v +
  affineGraphIntegral F (-b/(Real.pi-b)) (b*Real.pi/(Real.pi-b)-c) b Real.pi v

theorem scalarGraph_left_affine {b r : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (hr : r ≤ -b) (v c : ℝ) :
    scalarGraph b v r c = (r : ℂ)+Complex.I*((v : ℂ)*
      (((-b/(Real.pi-b) : ℝ) : ℂ)*(r : ℂ)+((-b*Real.pi/(Real.pi-b)-c : ℝ) : ℂ))) := by
  unfold scalarGraph
  rw [contourDisplacement_left_affine hb hbpi hr]
  push_cast
  ring

theorem scalarGraph_middle_affine {b r : ℝ} (hr : r ∈ Icc (-b) b) (v c : ℝ) :
    scalarGraph b v r c = (r : ℂ)+Complex.I*((v : ℂ)*((r : ℂ)+((-c : ℝ) : ℂ))) := by
  unfold scalarGraph
  rw [contourDisplacement_middle_affine hr]
  push_cast
  ring

theorem scalarGraph_right_affine {b r : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (hr : b ≤ r) (v c : ℝ) :
    scalarGraph b v r c = (r : ℂ)+Complex.I*((v : ℂ)*
      (((-b/(Real.pi-b) : ℝ) : ℂ)*(r : ℂ)+((b*Real.pi/(Real.pi-b)-c : ℝ) : ℂ))) := by
  unfold scalarGraph
  rw [contourDisplacement_right_affine hb hbpi hr]
  push_cast
  ring

theorem protectedGraphIntegral_eq_graph {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (F : ℂ → ℂ) (v c : ℝ) :
    protectedGraphIntegral F b v c =
      (∫ r : ℝ in (-Real.pi)..(-b), F (scalarGraph b v r c) *
        (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ)))) +
      (∫ r : ℝ in (-b)..b, F (scalarGraph b v r c) * (1+Complex.I*(v : ℂ))) +
      (∫ r : ℝ in b..Real.pi, F (scalarGraph b v r c) *
        (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ)))) := by
  unfold protectedGraphIntegral affineGraphIntegral
  congr 1
  · congr 1
    · apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (by linarith : -Real.pi ≤ -b)] at hr
      dsimp only
      rw [scalarGraph_left_affine hb hbpi hr.2]
    · apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (by linarith : -b ≤ b)] at hr
      dsimp only
      rw [scalarGraph_middle_affine hr]
      simp only [Complex.ofReal_one, one_mul, mul_one]
  · apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hbpi.le] at hr
    dsimp only
    rw [scalarGraph_right_affine hb hbpi hr.1]

theorem protectedGraphIntegral_congr {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    {F G : ℂ → ℂ} (v c : ℝ)
    (h : ∀ r∈Icc (-Real.pi) Real.pi, F (scalarGraph b v r c)=G (scalarGraph b v r c)) :
    protectedGraphIntegral F b v c = protectedGraphIntegral G b v c := by
  rw [protectedGraphIntegral_eq_graph hb hbpi, protectedGraphIntegral_eq_graph hb hbpi]
  congr 1
  · congr 1
    · apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (by linarith : -Real.pi ≤ -b)] at hr
      dsimp only
      rw [h r ⟨hr.1,hr.2.trans (by linarith)⟩]
    · apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (by linarith : -b ≤ b)] at hr
      dsimp only
      rw [h r ⟨(by linarith : -Real.pi ≤ -b).trans hr.1,hr.2.trans hbpi.le⟩]
  · apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hbpi.le] at hr
    dsimp only
    rw [h r ⟨(by linarith : -Real.pi ≤ b).trans hr.1,hr.2⟩]

/-- Actual one-variable contour deformation. It needs holomorphy only on
the displayed nonuniform homotopy, not on a surrounding horizontal strip. -/
theorem protectedGraphIntegral_eq_real {b v c : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (hv : 0 ≤ v) (F : ℂ → ℂ)
    (hp : Function.Periodic F (2*(Real.pi : ℂ)))
    (hF : ∀ t∈Icc 0 v, ∀ r∈Icc (-Real.pi) Real.pi,
      DifferentiableAt ℂ F (scalarGraph b t r c)) :
    protectedGraphIntegral F b v c = ∫ r : ℝ in (-Real.pi)..Real.pi, F (r : ℂ) := by
  have hd : Real.pi-b ≠ 0 := (sub_pos.mpr hbpi).ne'
  unfold protectedGraphIntegral
  apply three_piece_periodic_graph_stokes
  · linarith
  · linarith
  · exact hbpi.le
  · exact hv
  · field_simp
    ring
  · field_simp
    ring
  · ring
  · convert hp using 1
    push_cast
    ring
  · intro t ht r hr
    have he : scalarGraph b t r c =
        (r : ℂ)+Complex.I*((t : ℂ)*(((-b/(Real.pi-b) : ℝ) : ℂ)*(r : ℂ)+
          ((-b*Real.pi/(Real.pi-b)-c : ℝ) : ℂ))) := by
      unfold scalarGraph
      rw [contourDisplacement_left_affine hb hbpi hr.2]
      push_cast
      ring
    rw [← he]
    exact hF t ht r ⟨hr.1,hr.2.trans (by linarith)⟩
  · intro t ht r hr
    have he : scalarGraph b t r c =
        (r : ℂ)+Complex.I*((t : ℂ)*((1 : ℂ)*(r : ℂ)+((-c : ℝ) : ℂ))) := by
      unfold scalarGraph
      rw [contourDisplacement_middle_affine hr]
      push_cast
      ring
    simp only [Complex.ofReal_one]
    rw [← he]
    exact hF t ht r ⟨(by linarith : -Real.pi ≤ -b).trans hr.1,hr.2.trans hbpi.le⟩
  · intro t ht r hr
    have he : scalarGraph b t r c =
        (r : ℂ)+Complex.I*((t : ℂ)*(((-b/(Real.pi-b) : ℝ) : ℂ)*(r : ℂ)+
          ((b*Real.pi/(Real.pi-b)-c : ℝ) : ℂ))) := by
      unfold scalarGraph
      rw [contourDisplacement_right_affine hb hbpi hr.1]
      push_cast
      ring
    rw [← he]
    exact hF t ht r ⟨(by linarith : -Real.pi ≤ b).trans hr.1,hr.2⟩

end
end IsoProof
