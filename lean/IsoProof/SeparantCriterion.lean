import IsoProof.JetTrace

/-! The complete analytic separant argument of manuscript §5.  This is a
general theorem: the susceptibility application must construct its boundary
charts, continuous finite-jet traces, and dense sharp singularities.  No part
of those analytic inputs is encoded as a differential-algebra conclusion. -/
namespace IsoProof
noncomputable section
open Filter MvPolynomial Set
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- An actual one-sided path in the energy collar, on which the derivatives
are still taken in the function's own coordinate. -/
def SharpBoundaryApproach (f chart : ℂ → ℂ) (a b R x : ℝ) (k : ℕ) : Prop :=
  ∃ p : ℝ → ℂ,
    Tendsto p (𝓝[>] 0) (𝓝[upperCollar a b R] (x : ℂ)) ∧
    Tendsto (fun t => ‖iteratedDeriv k f (chart (p t))‖) (𝓝[>] 0) atTop ∧
    ∀ j < k, NormBoundedAlong (𝓝[>] 0) (fun t => iteratedDeriv j f (chart (p t)))

/-- The independently constructed data needed at one finite differentiability
order.  The chart is injective on an open collar and maps it into the analytic
domain.  Sharp singularities are dense in a nonempty real interval. -/
structure SmoothSingularBoundaryChart (f : ℂ → ℂ) (D : Set ℂ) (n : ℕ) where
  left : ℝ
  right : ℝ
  height : ℝ
  left_lt_right : left < right
  height_pos : 0 < height
  chart : ℂ → ℂ
  chart_analytic : AnalyticOnNhd ℂ chart (upperCollar left right height)
  chart_injective : InjOn chart (upperCollar left right height)
  chart_mapsTo : MapsTo chart (upperCollar left right height) D
  trace : JetTraceOn f chart n left right height
  singularSet : Set ℝ
  singular_subset : singularSet ⊆ Ioo left right
  singular_dense : Ioo left right ⊆ closure singularSet
  sharp : ∀ x ∈ singularSet, ∃ k : ℕ, n ≤ k ∧
    SharpBoundaryApproach f chart left right height x k

theorem upperCollar_nonempty {a b R : ℝ} (hab : a < b) (hR : 0 < R) :
    (upperCollar a b R).Nonempty := by
  refine ⟨((a+b)/2 : ℝ) + (R/2 : ℝ)*Complex.I, ?_⟩
  simp only [upperCollar, realCollar, mem_inter_iff, Complex.mem_reProdIm,
    mem_Ioo, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  constructor
  · constructor <;> constructor <;> linarith
  · linarith

/-- A polynomial relation's actual separant vanishes throughout the analytic
domain, if the relation's order has one smooth densely singular boundary
chart.  This is the contradiction-producing content of §5. -/
theorem separant_zero_on_of_boundary_chart {f : ℂ → ℂ} {D : Set ℂ}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D) (hf : AnalyticOnNhd ℂ f D)
    {n : ℕ} (hn : 1 ≤ n) (B : SmoothSingularBoundaryChart f D n)
    {P : DifferentialPolynomial} (hPbound : VariableBound P n)
    (hrel : EqOn (evaluateDifferentialPolynomial P f) 0 D) :
    EqOn (evaluateDifferentialPolynomial (MvPolynomial.pderiv n P) f) 0 D := by
  let S := MvPolynomial.pderiv n P
  have hSbound : VariableBound S n := pderiv_variableBound hPbound n
  let T : ℂ → ℂ := B.trace.polynomial S
  have hTc : ContinuousOn T (closedUpperCollar B.left B.right B.height) :=
    B.trace.polynomial_continuous hSbound
  have hTeq : EqOn T (fun z => evaluateDifferentialPolynomial S f (B.chart z))
      (upperCollar B.left B.right B.height) := B.trace.polynomial_agrees hSbound
  have hzero_dense : EqOn (fun x : ℝ => T (x : ℂ)) 0 B.singularSet := by
    intro x hx
    obtain ⟨k,hnk,p,hp,htop,hlow⟩ := B.sharp x hx
    have hpath : ∀ᶠ t in 𝓝[>] (0 : ℝ), B.chart (p t) ∈ D :=
      (eventually_mem_of_tendsto_nhdsWithin hp).mono (fun _ ht => B.chart_mapsTo ht)
    have hcoord := normBoundedAlong_of_tendsto
      (B.trace.coordinate_tendsto B.height_pos (B.singular_subset hx) hp)
    exact separant_limit_zero hDopen hf hrel hn hPbound hnk hpath hcoord hlow htop
      (B.trace.polynomial_tendsto hSbound B.height_pos (B.singular_subset hx) hp)
  have hboundary_cont : ContinuousOn (fun x : ℝ => T (x : ℂ)) (Ioo B.left B.right) :=
    hTc.comp Complex.continuous_ofReal.continuousOn
      (fun _ hx => ofReal_mem_closedUpperCollar B.height_pos hx)
  have hboundary : ∀ x ∈ Ioo B.left B.right, T (x : ℂ)=0 :=
    hzero_dense.of_subset_closure hboundary_cont continuousOn_const
      B.singular_subset B.singular_dense
  have hTan : AnalyticOnNhd ℂ (fun z => evaluateDifferentialPolynomial S f (B.chart z))
      (upperCollar B.left B.right B.height) := by
    intro z hz
    exact (polynomial_jet_evaluation_analyticAt S (hf _ (B.chart_mapsTo hz))).comp
      (B.chart_analytic z hz)
  have hTd : DifferentiableOn ℂ T (upperCollar B.left B.right B.height) :=
    hTan.differentiableOn.congr hTeq
  have hTzero : EqOn T 0 (closedUpperCollar B.left B.right B.height) :=
    eqOn_zero_of_upper_zero_trace B.left_lt_right B.height_pos hTc hTd hboundary
  obtain ⟨z,hz⟩ := upperCollar_nonempty B.left_lt_right B.height_pos
  have hcompzero : (fun w => evaluateDifferentialPolynomial S f (B.chart w))
      =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(upperCollar_isOpen B.left B.right B.height).mem_nhds hz] with w hw
    exact (hTeq hw).symm.trans (hTzero (upperCollar_subset_closed _ _ _ hw))
  have hSgerm : evaluateDifferentialPolynomial S f =ᶠ[𝓝 (B.chart z)] (fun _ => 0) :=
    analytic_zero_germ_of_injective_chart (upperCollar_isOpen _ _ _) hz B.chart_injective
      (B.chart_analytic z hz).continuousAt
      (polynomial_jet_evaluation_analyticAt S (hf _ (B.chart_mapsTo hz))) hcompzero
  have hSan : AnalyticOnNhd ℂ (evaluateDifferentialPolynomial S f) D :=
    fun w hw => polynomial_jet_evaluation_analyticAt S (hf w hw)
  exact hSan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDconn
    (B.chart_mapsTo hz) hSgerm

/-- The criterion concludes genuine differential transcendence over C(z),
using the proved rational/polynomial germ equivalence.  A chart may depend on
the finite order: finite low-order collision sets can therefore be avoided. -/
theorem differential_transcendentalAt_of_boundary_charts {f : ℂ → ℂ} {D : Set ℂ}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D) (hf : AnalyticOnNhd ℂ f D)
    (hcharts : ∀ n : ℕ, 1 ≤ n → Nonempty (SmoothSingularBoundaryChart f D n))
    {a : ℂ} (ha : a ∈ D) : DifferentiallyTranscendentalAt f a := by
  intro hrat
  have hpoly := (rational_relation_iff_polynomial_relation (hf a ha)).mp hrat
  obtain ⟨n,P,hn,hP0,hPbound,hnvars,hrel,hsep⟩ :=
    exists_minimal_relation_nonzero_separant hpoly
  obtain ⟨B⟩ := hcharts n hn
  have hglobal := differential_relation_global hDconn ha hf hrel
  have hz := separant_zero_on_of_boundary_chart hDopen hDconn hf hn B hPbound hglobal
  apply hsep
  filter_upwards [hDopen.mem_nhds ha] with z hzin
  exact hz hzin

end
end IsoProof
