import IsoProof.JetTrace
import IsoProof.ResonanceCoordinate

/-! Finite, explicit Faà di Bruno and Leibniz trace formulas.  These transport
proved energy-jet traces to true temperature or w derivatives, retaining all
coordinate and physical prefactor derivatives. -/
namespace IsoProof
noncomputable section
open Filter Set
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def pullbackJetTrace (n : ℕ) (J : ℕ → ℂ → ℂ) (coord chart : ℂ → ℂ) (E : ℂ) : ℂ :=
  ∑ c : OrderedFinpartition n, J c.length E *
    ∏ i, iteratedDeriv (c.partSize i) coord (chart E)

def weightedPullbackJetTrace (n : ℕ) (J : ℕ → ℂ → ℂ)
    (coord chart A : ℂ → ℂ) (E : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
    pullbackJetTrace j J coord chart E * iteratedDeriv (n-j) A (chart E)

theorem coordinateJet_continuousOn {U : Set ℂ} {coord chart : ℂ → ℂ}
    (hc : ContinuousOn chart U) (hcoord : AnalyticOnNhd ℂ coord (chart '' U)) (j : ℕ) :
    ContinuousOn (fun E => iteratedDeriv j coord (chart E)) U := by
  intro E hE
  exact (analyticAt_iteratedDeriv (hcoord _ ⟨E,hE,rfl⟩) j).continuousAt.comp_continuousWithinAt
    (hc E hE)

theorem pullbackJetTrace_continuousOn {U : Set ℂ} (n : ℕ)
    {J : ℕ → ℂ → ℂ} {coord chart : ℂ → ℂ}
    (hJ : ∀ j ≤ n, ContinuousOn (J j) U) (hc : ContinuousOn chart U)
    (hcoord : AnalyticOnNhd ℂ coord (chart '' U)) :
    ContinuousOn (pullbackJetTrace n J coord chart) U := by
  apply continuousOn_finsetSum
  intro c _
  apply (hJ c.length c.length_le).mul
  apply continuousOn_finsetProd
  intro i _
  exact coordinateJet_continuousOn hc hcoord (c.partSize i)

theorem weightedPullbackJetTrace_continuousOn {U : Set ℂ} (n : ℕ)
    {J : ℕ → ℂ → ℂ} {coord chart A : ℂ → ℂ}
    (hJ : ∀ j ≤ n, ContinuousOn (J j) U) (hc : ContinuousOn chart U)
    (hcoord : AnalyticOnNhd ℂ coord (chart '' U))
    (hA : AnalyticOnNhd ℂ A (chart '' U)) :
    ContinuousOn (weightedPullbackJetTrace n J coord chart A) U := by
  apply continuousOn_finsetSum
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  exact (continuousOn_const.mul
    (pullbackJetTrace_continuousOn j (fun i hi => hJ i (hi.trans hjn)) hc hcoord)).mul
    (coordinateJet_continuousOn hc hA (n-j))

theorem pullbackJetTrace_eq (n : ℕ) {J : ℕ → ℂ → ℂ}
    {F coord chart : ℂ → ℂ} {E : ℂ} (hco : coord (chart E)=E)
    (hF : AnalyticAt ℂ F E) (hc : AnalyticAt ℂ coord (chart E))
    (hJ : ∀ j ≤ n, J j E=iteratedDeriv j F E) :
    pullbackJetTrace n J coord chart E=iteratedDeriv n (F ∘ coord) (chart E) := by
  have hFc : AnalyticAt ℂ F (coord (chart E)) := hco.symm ▸ hF
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    (n := (n : ℕ∞ω)) hFc.contDiffAt hc.contDiffAt le_rfl]
  apply Finset.sum_congr rfl
  intro c _
  rw [hco,hJ c.length c.length_le]

theorem weightedPullbackJetTrace_eq (n : ℕ) {J : ℕ → ℂ → ℂ}
    {F coord chart A : ℂ → ℂ} {E : ℂ} (hco : coord (chart E)=E)
    (hF : AnalyticAt ℂ F E) (hc : AnalyticAt ℂ coord (chart E))
    (hA : AnalyticAt ℂ A (chart E)) (hJ : ∀ j ≤ n, J j E=iteratedDeriv j F E) :
    weightedPullbackJetTrace n J coord chart A E =
      iteratedDeriv n ((F ∘ coord)*A) (chart E) := by
  have hFc : AnalyticAt ℂ F (coord (chart E)) := hco.symm ▸ hF
  have hcomp := hFc.comp hc
  rw [iteratedDeriv_mul hcomp.contDiffAt hA.contDiffAt]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [pullbackJetTrace_eq j hco hF hc (fun i hi => hJ i (hi.trans hjn))]

/-- Construct all actual coordinate-and-jet traces through order n-1.  The
only infinite-series input is the already constructed finite energy jet
trace J; every chain/product coefficient is explicitly differentiated. -/
theorem jetTraceOn_of_pullback_product {f F coord chart A : ℂ → ℂ}
    {a b R : ℝ} (n : ℕ) (J : ℕ → ℂ → ℂ)
    (hJcont : ∀ j < n, ContinuousOn (J j) (closedUpperCollar a b R))
    (hJeq : ∀ z ∈ upperCollar a b R, ∀ j < n, J j z=iteratedDeriv j F z)
    (hchart : ContinuousOn chart (closedUpperCollar a b R))
    (hcoord : AnalyticOnNhd ℂ coord (chart '' closedUpperCollar a b R))
    (hA : AnalyticOnNhd ℂ A (chart '' closedUpperCollar a b R))
    (hF : AnalyticOnNhd ℂ F (upperCollar a b R))
    (hinv : ∀ z ∈ upperCollar a b R, coord (chart z)=z)
    (hfg : ∀ z ∈ upperCollar a b R,
      f =ᶠ[𝓝 (chart z)] (F ∘ coord)*A) :
    Nonempty (JetTraceOn f chart n a b R) := by
  let value : ℕ → ℂ → ℂ
    | 0 => chart
    | j+1 => weightedPullbackJetTrace j J coord chart A
  refine ⟨⟨value,?_,?_⟩⟩
  · intro i hi
    cases i with
    | zero => exact hchart
    | succ j =>
        exact weightedPullbackJetTrace_continuousOn j
          (fun k hk => hJcont k (by omega)) hchart hcoord hA
  · intro i hi z hz
    cases i with
    | zero => rfl
    | succ j =>
        change weightedPullbackJetTrace j J coord chart A z=iteratedDeriv j f (chart z)
        rw [weightedPullbackJetTrace_eq j (hinv z hz) (hF z hz)
          (hcoord _ ⟨z,upperCollar_subset_closed _ _ _ hz,rfl⟩)
          (hA _ ⟨z,upperCollar_subset_closed _ _ _ hz,rfl⟩)
          (fun k hk => hJeq z hz k (by omega))]
        exact ((hfg z hz).iteratedDeriv_eq j).symm

end
end IsoProof
