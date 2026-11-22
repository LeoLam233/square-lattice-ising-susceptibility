import IsoProof.ContourGeometry
import IsoProof.ContourRoot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! Concrete domain protection for the manuscript's single common graph.
No graph membership or pole gap is postulated: they are produced from the
piecewise-linear displacement and a compact interval of centers. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set Filter
set_option maxHeartbeats 1000000

/-- A form convenient for checking continuity at the two corners. -/
theorem contourDisplacement_eq_nested {b : ℝ} (hb : 0 ≤ b)
    (hbpi : b < Real.pi) (r : ℝ) :
    contourDisplacement b r =
      if r ≤ -b then -b*(Real.pi+r)/(Real.pi-b)
      else if r ≤ b then r else b*(Real.pi-r)/(Real.pi-b) := by
  have hden : Real.pi-b ≠ 0 := by linarith
  by_cases hneg : r ≤ -b
  · rw [ite_eq_left hneg]
    by_cases hin : |r| ≤ b
    · have hr : r = -b := by linarith [(abs_le.mp hin).1]
      subst r
      rw [contourDisplacement_interior hin]
      field_simp
      ring
    · have hr0 : ¬ 0 ≤ r := by
        intro hr0
        have hr : r = 0 := by linarith
        subst r
        simp [hb] at hin
      simp [contourDisplacement,hin,hr0]
  · rw [ite_eq_right hneg]
    by_cases hpos : r ≤ b
    · have hin : |r| ≤ b := abs_le.mpr ⟨by linarith,hpos⟩
      simp [contourDisplacement,hin,hpos]
    · have hr0 : 0 ≤ r := by linarith
      have hin : ¬ |r| ≤ b := by simpa [abs_of_nonneg hr0] using hpos
      simp [contourDisplacement,hin,hpos,hr0]

theorem contourDisplacement_continuous {b : ℝ} (hb : 0 ≤ b)
    (hbpi : b < Real.pi) : Continuous (contourDisplacement b) := by
  have hden : Real.pi-b ≠ 0 := by linarith
  have hright : Continuous (fun r : ℝ =>
      if r ≤ b then r else b*(Real.pi-r)/(Real.pi-b)) := by
    refine Continuous.if_le continuous_id (by fun_prop) continuous_id continuous_const ?_
    intro r hr
    subst r
    field_simp
  have hn : Continuous (fun r : ℝ =>
      if r ≤ -b then -b*(Real.pi+r)/(Real.pi-b)
      else if r ≤ b then r else b*(Real.pi-r)/(Real.pi-b)) := by
    refine Continuous.if_le (by fun_prop) hright continuous_id continuous_const ?_
    intro r hr
    subst r
    rw [ite_eq_left (by linarith : -b ≤ b)]
    field_simp
    ring
  simpa only [← contourDisplacement_eq_nested hb hbpi] using hn

theorem cut_branch_angle_eq {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : r ∈ Icc (-Real.pi) Real.pi) (hW : x-Real.cos r=1) :
    r=cutHalfWidth x ∨ r= -cutHalfWidth x := by
  have habs : |r| ≤ Real.pi := abs_le.mpr hr
  have hcos : Real.cos |r| = Real.cos (cutHalfWidth x) := by
    rw [Real.cos_abs, cutHalfWidth, Real.cos_arccos (by linarith) (by linarith)]
    linarith
  have he := Real.strictAntiOn_cos.injOn ⟨abs_nonneg r,habs⟩
    ⟨(cutHalfWidth_range hx hx2).1.le,(cutHalfWidth_range hx hx2).2.le⟩ hcos
  exact (abs_eq (cutHalfWidth_range hx hx2).1.le).mp he

def graphDirection (b r c : ℝ) : ℝ :=
  Real.sin r*(contourDisplacement b r-c)

def scalarGraph (b v r c : ℝ) : ℂ :=
  (r : ℂ)+Complex.I*((v*(contourDisplacement b r-c) : ℝ) : ℂ)

def graphDispersion (x b v y r c : ℝ) : ℂ :=
  ((x : ℂ)+Complex.I*(y : ℂ))-Complex.cos (scalarGraph b v r c)

def graphRealPart (x b v r c : ℝ) : ℝ :=
  x-Real.cos r*Real.cosh (v*(contourDisplacement b r-c))

theorem graphDispersion_re (x b v y r c : ℝ) :
    (graphDispersion x b v y r c).re = graphRealPart x b v r c := by
  unfold graphDispersion scalarGraph graphRealPart
  generalize v*(contourDisplacement b r-c) = t
  rw [show Complex.I*(t : ℂ) = (t : ℂ)*Complex.I by ring,
    Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

theorem graphDispersion_im (x b v y r c : ℝ) :
    (graphDispersion x b v y r c).im =
      y+Real.sin r*Real.sinh (v*(contourDisplacement b r-c)) :=
  graph_dispersion_im x y r (v*(contourDisplacement b r-c))

theorem graphDirection_pos_at_branch {x r c : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : r ∈ Icc (-Real.pi) Real.pi) (hc : |c| < cutHalfWidth x)
    (hW : x-Real.cos r=1) : 0 < graphDirection (cutHalfWidth x) r c := by
  obtain ⟨hb,hbpi⟩ := cutHalfWidth_range hx hx2
  have hc' := abs_lt.mp hc
  rcases cut_branch_angle_eq hx hx2 hr hW with he | he
  · subst r
    rw [graphDirection, contourDisplacement_interior (by simp [abs_of_pos hb])]
    exact mul_pos (Real.sin_pos_of_pos_of_lt_pi hb hbpi) (by linarith)
  · subst r
    rw [graphDirection, contourDisplacement_interior (by simp [abs_of_pos hb]),
      Real.sin_neg]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi hb hbpi))
      (by linarith)

theorem graphDirection_positive_im {x b v y r c : ℝ} (hv : 0 < v)
    (hy : 0 ≤ y) (hdir : 0 < graphDirection b r c) :
    0 < (graphDispersion x b v y r c).im := by
  rw [graphDispersion_im]
  have hp : 0 < Real.sin r*Real.sinh (v*(contourDisplacement b r-c)) := by
    rcases mul_pos_iff.mp hdir with h | h
    · exact mul_pos h.1 (Real.sinh_pos_iff.mpr (mul_pos hv h.2))
    · exact mul_pos_of_neg_of_neg h.1 (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hv h.2))
  linarith

theorem slit_domain_of_re_and_im {W : ℂ} (hW : -1 < W.re)
    (h : 0 < W.im ∨ W.re ≠ 1) : W ∈ contourRootDomain := by
  constructor
  · rcases h with h | h
    · left
      simpa using h
    · right
      simpa using (sub_ne_zero.mpr h.symm)
  · left
    simpa using (show 0 < W.re+1 by linarith)

/-- For the literal graph and every center in [-d,d] strictly inside the
oscillatory interval, one uniform positive displacement protects both cuts.
The imaginary energy may be any nonnegative number. -/
theorem common_graph_domain {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (_hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∀ r ∈ Icc (-Real.pi) Real.pi, ∀ c ∈ Icc (-d) d, ∀ y, 0 ≤ y →
        graphDispersion x (cutHalfWidth x) v y r c ∈ contourRootDomain := by
  let b := cutHalfWidth x
  have hb : 0 < b := (cutHalfWidth_range hx hx2).1
  have hbpi : b < Real.pi := (cutHalfWidth_range hx hx2).2
  have hf := contourDisplacement_continuous hb.le hbpi
  let K : Set (ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ Icc (-d) d
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hprop : ∀ᶠ v in 𝓝 (0 : ℝ), ∀ p ∈ K,
      -1 < graphRealPart x b v p.1 p.2 ∧
      (0 < graphDirection b p.1 p.2 ∨ graphRealPart x b v p.1 p.2 ≠ 1) := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    have hreal : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        graphRealPart x b z.1 z.2.1 z.2.2) := by
      unfold graphRealPart
      fun_prop
    have hdir : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        graphDirection b z.2.1 z.2.2) := by
      unfold graphDirection
      fun_prop
    have hz : graphRealPart x b 0 p.1 p.2 = x-Real.cos p.1 := by
      simp [graphRealPart]
    have hlow : -1 < graphRealPart x b 0 p.1 p.2 := by
      rw [hz]
      linarith [Real.cos_le_one p.1]
    have ho : IsOpen {z : ℝ × (ℝ × ℝ) |
        -1 < graphRealPart x b z.1 z.2.1 z.2.2 ∧
        (0 < graphDirection b z.2.1 z.2.2 ∨
          graphRealPart x b z.1 z.2.1 z.2.2 ≠ 1)} :=
      (isOpen_lt continuous_const hreal).inter
        ((isOpen_lt continuous_const hdir).union (isOpen_ne_fun hreal continuous_const))
    apply ho.mem_nhds
    refine ⟨hlow,?_⟩
    by_cases he : x-Real.cos p.1=1
    · have hc : |p.2| < b := lt_of_le_of_lt (abs_le.mpr hp.2) hdb
      exact Or.inl (graphDirection_pos_at_branch hx hx2 hp.1 hc he)
    · exact Or.inr (by rwa [hz])
  obtain ⟨ε,hε,hprop⟩ := Metric.eventually_nhds_iff.mp hprop
  refine ⟨ε,hε,?_⟩
  intro v hv hvε r hr c hc y hy
  have hP := hprop (y := v) (by simpa [Real.dist_eq,abs_of_pos hv] using hvε) (r,c) ⟨hr,hc⟩
  apply slit_domain_of_re_and_im
  · simpa only [graphDispersion_re] using hP.1
  · rcases hP.2 with hh | hh
    · exact Or.inl (graphDirection_positive_im hv hy hh)
    · exact Or.inr (by rwa [graphDispersion_re])

end
end IsoProof
