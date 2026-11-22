import IsoProof.ContourProtected
import IsoProof.ContourCompact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! Actual common-contour scalar package, including a uniform complex
energy neighborhood. All bounds below are produced from x,d and the
literal graph, independently of particle number. -/
namespace IsoProof
noncomputable section
open scoped Topology
open Set

/-- Coordinates are `(height, angle, center)`. -/
def commonGraphBox (d : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc 0 1 ×ˢ (Icc (-Real.pi) Real.pi ×ˢ Icc (-d) d)

def commonGraphAngle (x v : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  scalarGraph (cutHalfWidth x) v p.2.1 p.2.2

def commonGraphEnergy (x : ℝ) (e : ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (x : ℂ)+Complex.I*(p.1 : ℂ)+e

/-- A nonempty positive range of actual graph heights works on a full
complex energy disk around every point of the closed upper collar.
This is the concrete producer for the both-parity determinant estimate. -/
theorem common_graph_scalar_bounds {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∃ ρ > 0, ∃ M > 0, ∃ δ > 0,
      let T := Metric.closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d
      let q := fun t : ℂ × (ℝ × (ℝ × ℝ)) => commonGraphAngle x v t.2
      let E := fun t : ℂ × (ℝ × (ℝ × ℝ)) => commonGraphEnergy x t.1 t.2
      (∀ t ∈ T, E t-Complex.cos (q t) ∈ contourRootDomain) ∧
      (∀ t ∈ T, δ ≤ ‖Complex.exp (Complex.I*q t)‖) ∧
      (∀ t ∈ T, ‖Complex.exp (Complex.I*q t)‖ ≤ M) ∧
      (∀ t ∈ T, ‖continuedTransferRoot (E t-Complex.cos (q t))‖ ≤ M) ∧
      (∀ t ∈ T, ∀ t' ∈ T,
        δ ≤ ‖1-continuedTransferRoot (E t-Complex.cos (q t))*
          continuedTransferRoot (E t'-Complex.cos (q t'))‖) := by
  obtain ⟨ε,hε,hgraph⟩ := common_graph_domain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε
  have hf := contourDisplacement_continuous
    (cutHalfWidth_range hx hx2).1.le (cutHalfWidth_range hx hx2).2
  have hq : Continuous (commonGraphAngle x v) := by
    unfold commonGraphAngle scalarGraph
    fun_prop
  have hW : Continuous (fun p =>
      commonGraphEnergy x 0 p-Complex.cos (commonGraphAngle x v p)) := by
    unfold commonGraphEnergy
    fun_prop
  have hK : IsCompact (commonGraphBox d) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hD : ∀ p ∈ commonGraphBox d,
      commonGraphEnergy x 0 p-Complex.cos (commonGraphAngle x v p) ∈ contourRootDomain := by
    intro p hp
    simpa only [commonGraphEnergy,add_zero,commonGraphAngle,graphDispersion]
      using hgraph v hv hvε p.2.1 hp.2.1 p.2.2 hp.2.2 p.1 hp.1.1
  obtain ⟨ρ',hρ',hρprop⟩ := compact_dispersion_energy_disk hK _ hW hD
  let ρ := ρ'/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρlt : ρ < ρ' := by dsimp [ρ]; linarith
  let T := Metric.closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d
  let q := fun t : ℂ × (ℝ × (ℝ × ℝ)) => commonGraphAngle x v t.2
  let E := fun t : ℂ × (ℝ × (ℝ × ℝ)) => commonGraphEnergy x t.1 t.2
  have hT : IsCompact T := (isCompact_closedBall (0 : ℂ) ρ).prod hK
  have hqt : Continuous q := hq.comp continuous_snd
  have hEt : Continuous E := by
    unfold E commonGraphEnergy
    fun_prop
  have hDt : ∀ t ∈ T, E t-Complex.cos (q t) ∈ contourRootDomain := by
    intro t ht
    have hnorm : ‖t.1‖ ≤ ρ := by simpa using ht.1
    have h := hρprop t.1 (hnorm.trans_lt hρlt) t.2 ht.2
    convert h using 1
    dsimp [E,q,commonGraphEnergy]
    ring
  obtain ⟨M,hM,δ,hδ,hbounds⟩ := compact_dispersion_coordinate_bounds hT q E
    hqt.continuousOn hEt.continuousOn hDt
  exact ⟨ρ,hρ,M,hM,δ,hδ,hDt,hbounds⟩

end
end IsoProof
