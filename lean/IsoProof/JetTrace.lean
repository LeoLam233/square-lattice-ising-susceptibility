import IsoProof.DifferentialBoundary

/-! Finite jets on a genuine closed upper collar.  The extension functions
include the independent coordinate at index zero and are related to the
actual analytic derivatives on the open upper collar. -/
namespace IsoProof
noncomputable section
open Filter MvPolynomial Set
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def upperCollar (a b R : ℝ) : Set ℂ := realCollar a b R ∩ {z : ℂ | 0 < z.im}
def closedUpperCollar (a b R : ℝ) : Set ℂ :=
  realCollar a b R ∩ {z : ℂ | 0 ≤ z.im}

theorem upperCollar_isOpen (a b R : ℝ) : IsOpen (upperCollar a b R) :=
  (isOpen_Ioo.reProdIm isOpen_Ioo).inter (isOpen_lt continuous_const Complex.continuous_im)

theorem upperCollar_subset_closed (a b R : ℝ) :
    upperCollar a b R ⊆ closedUpperCollar a b R :=
  fun z hz => ⟨hz.1,(show 0 < z.im from hz.2).le⟩

theorem ofReal_mem_closedUpperCollar {a b R x : ℝ}
    (hR : 0 < R) (hx : x ∈ Ioo a b) : (x : ℂ) ∈ closedUpperCollar a b R := by
  exact ⟨⟨hx,by simpa using And.intro (neg_lt_zero.mpr hR) hR⟩,by simp⟩

structure JetTraceOn (f chart : ℂ → ℂ) (n : ℕ) (a b R : ℝ) where
  value : ℕ → ℂ → ℂ
  continuous : ∀ i ≤ n, ContinuousOn (value i) (closedUpperCollar a b R)
  agrees : ∀ i ≤ n, EqOn (value i)
    (fun z => jetEvaluation f (chart z) i) (upperCollar a b R)

def JetTraceOn.polynomial {f chart : ℂ → ℂ} {n : ℕ} {a b R : ℝ}
    (T : JetTraceOn f chart n a b R) (P : DifferentialPolynomial) (z : ℂ) : ℂ :=
  MvPolynomial.eval (fun i => T.value i z) P

theorem continuousOn_polynomial_of_variableBound {U : Set ℂ}
    {v : ℕ → ℂ → ℂ} {P : DifferentialPolynomial} {n : ℕ}
    (hP : VariableBound P n) (hv : ∀ i ≤ n, ContinuousOn (v i) U) :
    ContinuousOn (fun z => MvPolynomial.eval (fun i => v i z) P) U := by
  change P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' Iic n) at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      simpa only [MvPolynomial.eval_X] using hv i hi
  | algebraMap c =>
      simpa only [MvPolynomial.algebraMap_eq,MvPolynomial.eval_C] using
        continuousOn_const (c := c)
  | add P Q hP hQ ihP ihQ => simpa only [map_add] using! ihP.add ihQ
  | mul P Q hP hQ ihP ihQ => simpa only [map_mul] using! ihP.mul ihQ

theorem JetTraceOn.polynomial_continuous {f chart : ℂ → ℂ} {n : ℕ} {a b R : ℝ}
    (T : JetTraceOn f chart n a b R) {P : DifferentialPolynomial}
    (hP : VariableBound P n) :
    ContinuousOn (T.polynomial P) (closedUpperCollar a b R) :=
  continuousOn_polynomial_of_variableBound hP T.continuous

theorem JetTraceOn.polynomial_agrees {f chart : ℂ → ℂ} {n : ℕ} {a b R : ℝ}
    (T : JetTraceOn f chart n a b R) {P : DifferentialPolynomial}
    (hP : VariableBound P n) :
    EqOn (T.polynomial P) (fun z => evaluateDifferentialPolynomial P f (chart z))
      (upperCollar a b R) := by
  intro z hz
  exact MvPolynomial.hom_congr_vars
    (f₁ := MvPolynomial.eval (fun i => T.value i z))
    (f₂ := MvPolynomial.eval (jetEvaluation f (chart z)))
    (p₁ := P) (p₂ := P) (by ext c; simp)
    (fun i hi _ => by
      simpa only [MvPolynomial.eval_X] using
        T.agrees i (MvPolynomial.mem_supported.mp hP hi) hz) rfl

theorem JetTraceOn.polynomial_tendsto {f chart : ℂ → ℂ} {n : ℕ} {a b R x : ℝ}
    (T : JetTraceOn f chart n a b R) {P : DifferentialPolynomial}
    (hP : VariableBound P n) (hR : 0 < R) (hx : x ∈ Ioo a b)
    {α : Type*} {l : Filter α} {p : α → ℂ}
    (hp : Tendsto p l (𝓝[upperCollar a b R] (x : ℂ))) :
    Tendsto (fun t => evaluateDifferentialPolynomial P f (chart (p t))) l
      (𝓝 (T.polynomial P (x : ℂ))) := by
  have hclosed := hp.mono_right (nhdsWithin_mono _ (upperCollar_subset_closed a b R))
  have hlim := (T.polynomial_continuous hP _ (ofReal_mem_closedUpperCollar hR hx)).tendsto.comp hclosed
  apply hlim.congr'
  filter_upwards [eventually_mem_of_tendsto_nhdsWithin hp] with t ht
  exact T.polynomial_agrees hP ht

theorem JetTraceOn.coordinate_tendsto {f chart : ℂ → ℂ} {n : ℕ} {a b R x : ℝ}
    (T : JetTraceOn f chart n a b R) (hR : 0 < R) (hx : x ∈ Ioo a b)
    {α : Type*} {l : Filter α} {p : α → ℂ}
    (hp : Tendsto p l (𝓝[upperCollar a b R] (x : ℂ))) :
    Tendsto (fun t => chart (p t)) l (𝓝 (T.value 0 (x : ℂ))) := by
  simpa only [JetTraceOn.polynomial, evaluateDifferentialPolynomial,
    MvPolynomial.eval_X, jetEvaluation] using
    T.polynomial_tendsto (variableBound_X (Nat.zero_le n)) hR hx hp

theorem analytic_zero_germ_of_injective_chart {F chart : ℂ → ℂ} {z : ℂ} {V : Set ℂ}
    (hV : IsOpen V) (hz : z ∈ V) (hinj : InjOn chart V)
    (hc : ContinuousAt chart z) (hF : AnalyticAt ℂ F (chart z))
    (hzero : (fun w => F (chart w)) =ᶠ[𝓝 z] (fun _ => 0)) :
    F =ᶠ[𝓝 (chart z)] (fun _ => 0) := by
  have hmap : Tendsto chart (𝓝[≠] z) (𝓝[≠] (chart z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [show ∀ᶠ w in 𝓝[≠] z, w ∈ V from
      nhdsWithin_le_nhds (hV.mem_nhds hz),
      self_mem_nhdsWithin] with w hw hwz
    exact fun he => hwz (hinj hw hz he)
  apply hF.frequently_zero_iff_eventually_zero.mp
  exact hmap.frequently ((hzero.filter_mono nhdsWithin_le_nhds).frequently)

end
end IsoProof
