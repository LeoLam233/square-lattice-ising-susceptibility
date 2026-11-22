import IsoProof.IntegralsBridge
import IsoProof.ContourPhysical
import IsingBulk.HT22.Physical.Holomorphy

/-! Literal analytic site density on the coherent continued sheet. This
function agrees with the original site integrand before the deformation. -/
namespace IsoProof
noncomputable section
open Set
open scoped BigOperators
open IsingBulk.Tail

def continuedAnglePoint (q : ℂ) : ℂ := Complex.exp (Complex.I*q)

def continuedAngleRoot (E q : ℂ) : ℂ := continuedTransferRoot (E-Complex.cos q)

def continuedSiteDensity {N : ℕ} (A : ℕ) (B : ℤ) (E : ℂ) (q : Fin N → ℂ) : ℂ :=
  canceledPairProduct (fun i => continuedAngleRoot E (q i))
    (fun i => continuedAnglePoint (q i)) *
  ∏ i, (continuedAngleRoot E (q i))^A * (continuedAnglePoint (q i))^B *
    IsingBulk.HT22.Physical.oneBody (continuedAngleRoot E (q i))

/-- Joint E/angle analyticity on the actual coherent root domain. All pair
gaps, including the one-body diagonal gap, follow from the root theorem. -/
theorem continuedSiteDensity_joint_analyticAt {N : ℕ} (A : ℕ) (B : ℤ)
    (p : ℂ × (Fin N → ℂ))
    (hW : ∀ i, p.1-Complex.cos (p.2 i) ∈ contourRootDomain) :
    AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => continuedSiteDensity A B x.1 x.2) p := by
  have dq (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dy (i : Fin N) :
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => continuedAnglePoint (x.2 i)) p :=
    (analyticAt_const.mul (dq i)).cexp
  have dz (i : Fin N) :
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => continuedAngleRoot x.1 (x.2 i)) p :=
    (continuedTransferRoot_analyticAt (hW i)).comp
      (f := fun x : ℂ × (Fin N → ℂ) => x.1-Complex.cos (x.2 i))
      (analyticAt_fst.sub (Complex.analyticAt_cos.comp (dq i)))
  have hy0 (i : Fin N) : continuedAnglePoint (p.2 i) ≠ 0 := Complex.exp_ne_zero _
  have hpair (i j : Fin N) :
      1-continuedAngleRoot p.1 (p.2 i)*continuedAngleRoot p.1 (p.2 j) ≠ 0 :=
    norm_pos_iff.mp (continuedTransferRoot_pair_gap (V := p.1-Complex.cos (p.2 j)) (hW i))
  have dpair (i j : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPair (continuedAnglePoint (x.2 i)) (continuedAnglePoint (x.2 j))
        (continuedAngleRoot x.1 (x.2 i)) (continuedAngleRoot x.1 (x.2 j))) p :=
    (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy0 i) (hy0 j)) (pow_ne_zero 2 (hpair i j)))
  have dpairs : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPairProduct (fun i => continuedAngleRoot x.1 (x.2 i))
        (fun i => continuedAnglePoint (x.2 i))) p := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i < j)).analyticAt_fun_prod
    intro j _
    exact dpair i j
  apply dpairs.mul
  apply Finset.univ.analyticAt_fun_prod
  intro i _
  have dbody : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      IsingBulk.HT22.Physical.oneBody (continuedAngleRoot x.1 (x.2 i))) p := by
    simp_rw [IsingBulk.HT22.Physical.oneBody_eq_rational]
    exact (analyticAt_const.mul (dz i)).div (analyticAt_const.sub ((dz i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  exact (((dz i).pow A).mul ((dy i).zpow (hy0 i))).mul dbody

theorem continuedSiteDensity_analyticAt {N : ℕ} (A : ℕ) (B : ℤ)
    (E : ℂ) (q : Fin N → ℂ) (hW : ∀ i, E-Complex.cos (q i) ∈ contourRootDomain) :
    AnalyticAt ℂ (continuedSiteDensity A B E) q :=
  (continuedSiteDensity_joint_analyticAt A B (E,q) hW).comp
    (analyticAt_const.prod analyticAt_id)

theorem continuedAnglePoint_real (q : ℝ) : continuedAnglePoint (q : ℂ) = anglePoint q := by
  unfold continuedAnglePoint anglePoint limitingAngle
  congr 1
  ring

theorem continuedAngleRoot_real {E : ℂ} (hE : 0 < E.im) (q : ℝ) :
    continuedAngleRoot E (q : ℂ) = angleRoot E q := by
  rw [continuedAngleRoot, ← Complex.ofReal_cos,
    continuedTransferRoot_eq_physicalRoot (by simpa using hE)]
  rfl

theorem continuedSiteDensity_real {N : ℕ} (A : ℕ) (B : ℤ)
    {E : ℂ} (hE : 0 < E.im) (q : Fin N → ℝ) :
    continuedSiteDensity A B E (fun i => (q i : ℂ)) =
      pairProduct E q * ∏ i, (angleRoot E (q i))^A * (anglePoint (q i))^B *
        IsingBulk.HT22.Physical.oneBody (angleRoot E (q i)) := by
  simp only [continuedSiteDensity, continuedAnglePoint_real, continuedAngleRoot_real hE,
    pairProduct]

theorem continuedAnglePoint_periodic :
    Function.Periodic continuedAnglePoint (2*(Real.pi : ℂ)) := by
  intro q
  simp only [continuedAnglePoint, mul_add, Complex.exp_add]
  rw [show Complex.I*(2*(Real.pi : ℂ))=2*(Real.pi : ℂ)*Complex.I by ring,
    Complex.exp_two_pi_mul_I, mul_one]

theorem continuedSiteDensity_coordinate_periodic {N : ℕ} (A : ℕ) (B : ℤ)
    (E : ℂ) (q : Fin N → ℂ) (i : Fin N) :
    continuedSiteDensity A B E (Function.update q i (q i+2*(Real.pi : ℂ))) =
      continuedSiteDensity A B E q := by
  have hy : (fun j => continuedAnglePoint (Function.update q i (q i+2*(Real.pi : ℂ)) j)) =
      fun j => continuedAnglePoint (q j) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self]
      exact continuedAnglePoint_periodic (q i)
    · rw [Function.update_of_ne hj]
  have hz : (fun j => continuedAngleRoot E (Function.update q i (q i+2*(Real.pi : ℂ)) j)) =
      fun j => continuedAngleRoot E (q j) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self, continuedAngleRoot, Complex.cos_add_two_pi]
    · rw [Function.update_of_ne hj]
  simp only [continuedSiteDensity, congrFun hy, congrFun hz]

end
end IsoProof
