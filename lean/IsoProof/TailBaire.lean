import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A Baire extraction used only to uniformize *proved* vertical estimates.
The closed sets use positive heights, where the literal site integrals are
analytic.  No boundary extension is assumed to define the sets.  Every open
real interval contains a smaller closed interval with one common constant
and one common positive height. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology

/-- A positive-height estimate whose constants may initially depend on the
real base point becomes uniform on a nondegenerate subinterval.  The index
type need not be countable: it is the countable set of possible constants
and heights, not the family of inequalities, to which Baire is applied. -/
theorem exists_uniform_vertical_bound {ι : Type*} {l u : ℝ} (hlu : l < u)
    (f : ι → ℂ → ℂ) (order : ι → ℕ) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hc : ∀ i (y : ℝ), 0 < y →
      ContinuousOn (fun x : ℝ => ‖f i ((x : ℂ)+Complex.I*(y : ℂ))‖) (Ioo l u))
    (hp : ∀ x ∈ Ioo l u, ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, 0 < R ∧
      ∀ i (y : ℝ), 0 < y → y ≤ R →
        ‖f i ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ C^(order i)*weight i) :
    ∃ a b C R : ℝ, l < a ∧ a < b ∧ b < u ∧ 0 < C ∧ 0 < R ∧
      ∀ x ∈ Icc a b, ∀ i (y : ℝ), 0 < y → y ≤ R →
        ‖f i ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ C^(order i)*weight i := by
  let X := Ioo l u
  have : Nonempty X := ⟨⟨(l+u)/2,by constructor <;> linarith⟩⟩
  have : BaireSpace X := isOpen_Ioo.baireSpace
  let S : ℕ × ℕ → Set X := fun mk =>
    {x | ∀ i (y : ℝ), 0 < y → y ≤ 1/(mk.2+1 : ℝ) →
      ‖f i ((x.1 : ℂ)+Complex.I*(y : ℂ))‖ ≤ (mk.1+1 : ℝ)^(order i)*weight i}
  have hclosed : ∀ mk, IsClosed (S mk) := by
    intro mk
    simp only [S, ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun y =>
      isClosed_iInter fun hy => isClosed_iInter fun _hR => ?_
    exact isClosed_le (continuousOn_iff_continuous_domRestrict.mp (hc i y hy))
      continuous_const
  have hcover : ⋃ mk, S mk = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨C,hC,R,hR,hbound⟩ := hp x.1 x.2
    obtain ⟨m,hm⟩ := exists_nat_gt C
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hR
    apply mem_iUnion.mpr
    refine ⟨(m,k),?_⟩
    intro i y hy hyR
    exact (hbound i y hy (hyR.trans hk.le)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hC.le (by exact (le_of_lt hm).trans (by linarith)) (order i))
        (hw i))
  obtain ⟨mk,x,hx⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let U : Set ℝ := Subtype.val '' interior (S mk)
  have hU : IsOpen U := isOpen_Ioo.isOpenMap_subtype_val _ isOpen_interior
  have hxU : x.1 ∈ U := ⟨x,hx,rfl⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x.1 hxU
  have hsub : Icc (x.1-ε/2) (x.1+ε/2) ⊆ U := by
    intro z hz
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hz.1,hz.2]
  have hl : l < x.1-ε/2 := by
    obtain ⟨z,_hz,he⟩ := hsub ⟨le_rfl,by linarith⟩
    simpa only [he] using z.2.1
  have hu : x.1+ε/2 < u := by
    obtain ⟨z,_hz,he⟩ := hsub ⟨by linarith,le_rfl⟩
    simpa only [he] using z.2.2
  refine ⟨x.1-ε/2,x.1+ε/2,(mk.1+1 : ℝ),1/(mk.2+1 : ℝ),
    hl,by linarith,hu,by positivity,by positivity,?_⟩
  intro z hz i y hy hyR
  obtain ⟨w,hw,he⟩ := hsub hz
  have h := interior_subset hw i y hy hyR
  simpa only [he] using h

end
end IsoProof
