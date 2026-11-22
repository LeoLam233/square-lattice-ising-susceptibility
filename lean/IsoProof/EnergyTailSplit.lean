import IsoProof.TailConvergence
import IsoProof.SeriesAtInfinity

/-! Exact finite/high-particle decomposition of the literal complete
energy sums.  The finite part retains precisely particle orders ≤ K;
there is no change to the odd/even indexing or the original full tsum. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

theorem fullEnergyTerms_norm_summable (ν : Phase) {E : ℂ} (hE : E ∈ energyDomain) :
    Summable (fun n : ℕ => ‖particleCoefficient .positive (particleOrder ν n) E‖) := by
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec hE
  cases ν with
  | high =>
    apply (IsingBulk.HT22.Physical.signedOdd_derivative_norm_summable false 0 hs).congr
    intro n
    simp only [iteratedDeriv_zero]
    change ‖IsingBulk.HT22.Physical.coefficient (2*n+1) (exteriorEnergyInverse E)‖ = _
    rw [← particleCoefficient_positive_energy,he]
    rfl
  | low =>
    apply (IsingBulk.Preferred22.even_coefficients_absolutely_summable hs).congr
    intro n
    rw [← particleCoefficient_positive_eq_preferred ⟨n+1,rfl⟩ hs,he]
    rfl

def finiteEnergyPart (ν : Phase) (σ : Sign) (K : ℕ) (E : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (K+1), if particleOrder ν n ≤ K then
    particleCoefficient σ (particleOrder ν n) E else 0

theorem particleOrder_index_le (ν : Phase) (n : ℕ) : n ≤ particleOrder ν n := by
  cases ν <;> dsimp [particleOrder] <;> omega

theorem fullEnergySum_eq_finite_add_tail (ν : Phase) (K : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    fullEnergySum ν .positive E = finiteEnergyPart ν .positive K E +
      energyTail ν .positive K E := by
  classical
  let f : ℕ → ℂ := fun n => particleCoefficient .positive (particleOrder ν n) E
  let lo : ℕ → ℂ := fun n => if particleOrder ν n ≤ K then f n else 0
  let hi : ℕ → ℂ := fun n => if K < particleOrder ν n then f n else 0
  have hs : Summable f := (fullEnergyTerms_norm_summable ν hE).of_norm
  have hl : Summable lo := by
    apply (hs.indicator {n | particleOrder ν n ≤ K}).congr
    intro n
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,lo]
  have hh : Summable hi := by
    apply (hs.indicator {n | K < particleOrder ν n}).congr
    intro n
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,hi]
  have hfin : ∑' n, lo n = finiteEnergyPart ν .positive K E := by
    apply tsum_eq_sum
    intro n hn
    have hnK : K < n := by
      simp only [Finset.mem_range,not_lt] at hn
      omega
    have ho : ¬ particleOrder ν n ≤ K := by have := particleOrder_index_le ν n; omega
    simp only [lo,ho,↓reduceIte]
  calc
    _ = (∑' n, (lo n+hi n)) := by
      apply tsum_congr
      intro n
      by_cases hn : particleOrder ν n ≤ K
      · simp [lo,hi,hn,not_lt.mpr hn,f]
      · simp [lo,hi,hn,lt_of_not_ge hn,f]
    _ = (∑' n, lo n)+(∑' n,hi n) := hl.tsum_add hh
    _ = _ := by rw [hfin]; rfl

theorem finiteEnergyPart_analyticAt (ν : Phase) (σ : Sign) (K : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    AnalyticAt ℂ (finiteEnergyPart ν σ K) E := by
  apply Finset.analyticAt_fun_sum
  intro n _hn
  by_cases hn : particleOrder ν n ≤ K
  · simpa only [hn,↓reduceIte] using particleCoefficient_analyticAt σ (particleOrder ν n) hE
  · simpa only [hn,↓reduceIte] using (analyticAt_const (v := (0 : ℂ)))

theorem energyTail_positive_analyticAt (ν : Phase) (K : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) : AnalyticAt ℂ (energyTail ν .positive K) E := by
  apply ((fullEnergySum_positive_analyticOn ν E hE).sub
    (finiteEnergyPart_analyticAt ν .positive K hE)).congr
  filter_upwards [isOpen_energyDomain.mem_nhds hE] with z hz
  exact (eq_sub_iff_add_eq.mpr (by
    rw [add_comm]
    exact (fullEnergySum_eq_finite_add_tail ν K hz).symm)).symm

theorem fullEnergySum_jet_eq_finite_add_tail (ν : Phase) (K j : ℕ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    iteratedDeriv j (fullEnergySum ν .positive) E =
      iteratedDeriv j (finiteEnergyPart ν .positive K) E +
      iteratedDeriv j (energyTail ν .positive K) E := by
  have he : fullEnergySum ν .positive =ᶠ[𝓝 E]
      fun z => finiteEnergyPart ν .positive K z + energyTail ν .positive K z := by
    filter_upwards [isOpen_energyDomain.mem_nhds hE] with z hz
    exact fullEnergySum_eq_finite_add_tail ν K hz
  rw [he.iteratedDeriv_eq j]
  exact iteratedDeriv_fun_add (finiteEnergyPart_analyticAt ν .positive K hE).contDiffAt
    (energyTail_positive_analyticAt ν K hE).contDiffAt

end
end IsoProof
