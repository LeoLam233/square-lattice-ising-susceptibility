import IsoProof.Objects
import IsingBulk.Preferred22.KernelProduct
import IsingBulk.Preferred22.Hadamard
import IsingBulk.HT22.Algebra.OddBordered

/-!
Both-parity bound for the exact removable pair product on an arbitrary
complex dispersion contour. The hypotheses are scalar bounds on the actual
coordinates, not an assertion of a determinant bound or a convergence target.
The odd bordered determinant and the even dispersion determinant are exact
algebraic identities, so angular reciprocity is included throughout.
-/
namespace IsoProof
noncomputable section
open scoped BigOperators
open IsingBulk.Tail

private theorem physicalPair_eq_canceledPair (a b z w : ℂ) :
    IsingBulk.HT22.Algebra.physicalPair a b z w = canceledPair a b z w := by
  rw [IsingBulk.HT22.Algebra.physicalPair_eq]
  unfold canceledPair
  ring

/-- Exact even identity for arbitrary complex angular coordinates. -/
theorem complex_pairProduct_even_determinant (n : ℕ) (E : ℂ)
    (y z : Fin (2*n) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hc : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*E)
    (hd : ∀ i j, i ≠ j → 1-z i*z j ≠ 0) :
    canceledPairProduct z y = (IsingBulk.Preferred22.gaugeKernel y z).det := by
  rw [IsingBulk.Preferred22.gaugeKernel_eq_dispersionMatrix,
    IsingBulk.Preferred22.dispersion_determinant_product n E y z
      (fun i => Complex.sqrt (z i/y i)) hy hz hc hd
      (fun i => IsingBulk.Preferred22.complex_sqrt_sq _)]
  unfold canceledPairProduct
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr
  · ext j
    simp
  · intro j _
    rw [← physicalPair_eq_canceledPair]
    exact (IsingBulk.HT22.Algebra.scaledPair_sq _ _ _ _ _ _
      (IsingBulk.Preferred22.complex_sqrt_sq _) (IsingBulk.Preferred22.complex_sqrt_sq _)).symm

/-- Exact odd identity; the extra row and column are retained in the norm
estimate and are never confused with an odd skew determinant. -/
theorem complex_pairProduct_odd_determinant (n : ℕ) (E : ℂ)
    (y z : Fin (2*n+1) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hc : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*E)
    (hd : ∀ i j, i ≠ j → 1-z i*z j ≠ 0) :
    canceledPairProduct z y = (IsingBulk.HT22.Algebra.constantBorderFirst y z).det := by
  rw [IsingBulk.HT22.Algebra.odd_constantBorderFirst_determinant n E y z hy hz hc hd]
  unfold canceledPairProduct
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr
  · ext j
    simp
  · intro j _
    exact (physicalPair_eq_canceledPair _ _ _ _).symm

/-- An N-independent entry bound determined by coordinate size and pair gap. -/
def pairEntryEnvelope (M δ : ℝ) : ℝ :=
  max 1 ((M/δ+1)^2*(2*M/δ))

private theorem sqrt_ratio_norm_bound {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    {y z : ℂ} (hy : δ ≤ ‖y‖) (hz : ‖z‖ ≤ M) :
    ‖Complex.sqrt (z/y)‖ ≤ M/δ+1 := by
  have hs : ‖Complex.sqrt (z/y)‖^2 = ‖z‖/‖y‖ := by
    rw [← norm_pow, IsingBulk.Preferred22.complex_sqrt_sq, norm_div]
  have hr : ‖z‖/‖y‖ ≤ M/δ :=
    (div_le_div_of_nonneg_right hz (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hM hδ hy)
  have hp : 0 ≤ M/δ := div_nonneg hM hδ.le
  nlinarith [sq_nonneg (M/δ), norm_nonneg (Complex.sqrt (z/y))]

private theorem ordinaryEntry_norm_bound {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    {yi yj zi zj : ℂ} (hi : ‖yi‖ ≤ M) (hj : ‖yj‖ ≤ M)
    (hd : δ ≤ ‖1-zi*zj‖) :
    ‖IsingBulk.HT22.Algebra.ordinaryEntry yi yj zi zj‖ ≤ 2*M/δ := by
  have hn : ‖yi-yj‖ ≤ 2*M := (norm_sub_le _ _).trans (by linarith)
  simp only [IsingBulk.HT22.Algebra.ordinaryEntry,
    IsingBulk.Preferred22.dispersionB, norm_mul, norm_neg, Complex.norm_I,
    one_mul, norm_div]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) hδ hd)

theorem gaugeKernel_entry_bound {N : ℕ} {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (y z : Fin N → ℂ) (hy0 : ∀ i, δ ≤ ‖y i‖)
    (hy : ∀ i, ‖y i‖ ≤ M) (hz : ∀ i, ‖z i‖ ≤ M)
    (hd : ∀ i j, δ ≤ ‖1-z i*z j‖) (i j : Fin N) :
    ‖IsingBulk.Preferred22.gaugeKernel y z i j‖ ≤ pairEntryEnvelope M δ := by
  have hi := sqrt_ratio_norm_bound hM hδ (hy0 i) (hz i)
  have hj := sqrt_ratio_norm_bound hM hδ (hy0 j) (hz j)
  have hn : ‖y i-y j‖ ≤ 2*M := (norm_sub_le _ _).trans (by linarith [hy i,hy j])
  have hb : ‖Complex.sqrt (z i/y i)‖*‖Complex.sqrt (z j/y j)‖*‖y i-y j‖ ≤
      (M/δ+1)^2*(2*M) := by
    exact (mul_le_mul (mul_le_mul hi hj (norm_nonneg _) (by positivity)) hn
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  unfold IsingBulk.Preferred22.gaugeKernel
  rw [norm_div]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ ((M/δ+1)^2*(2*M))/‖1-z i*z j‖ :=
      div_le_div_of_nonneg_right hb (norm_nonneg _)
    _ ≤ ((M/δ+1)^2*(2*M))/δ :=
      div_le_div_of_nonneg_left (by positivity) hδ (hd i j)
    _ = (M/δ+1)^2*(2*M/δ) := by ring
    _ ≤ pairEntryEnvelope M δ := le_max_right _ _

theorem constantBorder_entry_bound {N : ℕ} {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (y z : Fin N → ℂ) (hy : ∀ i, ‖y i‖ ≤ M)
    (hd : ∀ i j, δ ≤ ‖1-z i*z j‖) (i j : Fin (N+1)) :
    ‖IsingBulk.HT22.Algebra.constantBorderFirst y z i j‖ ≤ pairEntryEnvelope M δ := by
  have hone : 1 ≤ pairEntryEnvelope M δ := le_max_left _ _
  have ho (a b : Fin N) :
      ‖IsingBulk.HT22.Algebra.ordinaryEntry (y a) (y b) (z a) (z b)‖ ≤ pairEntryEnvelope M δ := by
    have h0 := ordinaryEntry_norm_bound hM hδ (hy a) (hy b) (hd a b)
    have h1 : 1 ≤ (M/δ+1)^2 := by nlinarith [div_nonneg hM hδ.le]
    exact h0.trans ((le_mul_of_one_le_left (by positivity) h1).trans (le_max_right _ _))
  cases i using Fin.cases <;> cases j using Fin.cases
  · change ‖(0 : ℂ)‖ ≤ _
    simpa only [norm_zero] using zero_le_one.trans hone
  · change ‖(1 : ℂ)‖ ≤ _
    simpa only [norm_one] using hone
  · change ‖(-1 : ℂ)‖ ≤ _
    simpa only [norm_neg, norm_one] using hone
  · exact ho _ _

/-- Explicit complex-contour Hadamard bound, even parity. -/
theorem complex_pairProduct_even_norm (n : ℕ) (hn : 0 < n) (E : ℂ)
    (y z : Fin (2*n) → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hy0 : ∀ i, δ ≤ ‖y i‖) (hy : ∀ i, ‖y i‖ ≤ M)
    (hz0 : ∀ i, z i ≠ 0) (hz : ∀ i, ‖z i‖ ≤ M)
    (hc : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*E)
    (hd : ∀ i j, δ ≤ ‖1-z i*z j‖) :
    ‖canceledPairProduct z y‖ ≤
      (Real.sqrt (2*n : ℕ)*pairEntryEnvelope M δ)^(2*n) := by
  rw [complex_pairProduct_even_determinant n E y z
    (fun i => norm_pos_iff.mp (hδ.trans_le (hy0 i))) hz0 hc
    (fun i j _ => norm_pos_iff.mp (hδ.trans_le (hd i j)))]
  exact IsingBulk.Preferred22.determinant_bound (by omega) _
    (zero_le_one.trans (le_max_left _ _)) (gaugeKernel_entry_bound hM hδ y z hy0 hy hz hd)

/-- Explicit complex-contour Hadamard bound, odd parity. -/
theorem complex_pairProduct_odd_norm (n : ℕ) (E : ℂ)
    (y z : Fin (2*n+1) → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hy0 : ∀ i, δ ≤ ‖y i‖) (hy : ∀ i, ‖y i‖ ≤ M)
    (hz0 : ∀ i, z i ≠ 0)
    (hc : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*E)
    (hd : ∀ i j, δ ≤ ‖1-z i*z j‖) :
    ‖canceledPairProduct z y‖ ≤
      (Real.sqrt (2*n+2 : ℕ)*pairEntryEnvelope M δ)^(2*n+2) := by
  rw [complex_pairProduct_odd_determinant n E y z
    (fun i => norm_pos_iff.mp (hδ.trans_le (hy0 i))) hz0 hc
    (fun i j _ => norm_pos_iff.mp (hδ.trans_le (hd i j)))]
  exact IsingBulk.Preferred22.determinant_bound (by omega) _
    (zero_le_one.trans (le_max_left _ _)) (constantBorder_entry_bound hM hδ y z hy hd)

private theorem even_hadamard_to_three_quarters {N : ℕ} (hN : 0 < N)
    {C : ℝ} (hC : 0 ≤ C) :
    (Real.sqrt N*C)^N ≤ (C*(N : ℝ)^(3/4 : ℝ))^N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt N ≤ (N : ℝ)^(3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  exact pow_le_pow_left₀ (by positivity)
    ((mul_le_mul_of_nonneg_right hs hC).trans_eq (mul_comm _ _)) _

private theorem odd_hadamard_to_three_quarters {N : ℕ} (hN : 2 ≤ N)
    {C : ℝ} (hC : 1 ≤ C) :
    (Real.sqrt (N+1 : ℕ)*C)^(N+1) ≤ ((4*C^2)*(N : ℝ)^(3/4 : ℝ))^N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt (N+1 : ℕ) ≤ 2*Real.sqrt N := by
    have h1 := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (N+1 : ℕ) by positivity)
    push_cast at h2
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sqrt_nonneg ((N : ℝ)+1)]
  have hr : (Real.sqrt N)^(N+1) ≤ ((N : ℝ)^(3/4 : ℝ))^N := by
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg N),
      ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    push_cast
    linarith
  have hc : (2*C)^(N+1) ≤ (2*C)^(2*N) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  calc
    _ ≤ (2*Real.sqrt N*C)^(N+1) :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hs (by linarith)) _
    _ = (2*C)^(N+1)*(Real.sqrt N)^(N+1) := by rw [← mul_pow]; congr 1; ring
    _ ≤ (2*C)^(2*N)*((N : ℝ)^(3/4 : ℝ))^N :=
      mul_le_mul hc hr (by positivity) (by positivity)
    _ = _ := by rw [pow_mul, ← mul_pow]; congr 1; ring

/-- The paper's summable exponent, with one constant independent of particle
number and valid for both parities on every complex dispersion contour
satisfying the displayed coordinate bounds. -/
theorem complex_pairProduct_three_quarters (N : ℕ) (hN : 0 < N) (E : ℂ)
    (y z : Fin N → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hy0 : ∀ i, δ ≤ ‖y i‖) (hy : ∀ i, ‖y i‖ ≤ M)
    (hz0 : ∀ i, z i ≠ 0) (hz : ∀ i, ‖z i‖ ≤ M)
    (hc : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*E)
    (hd : ∀ i j, δ ≤ ‖1-z i*z j‖) :
    ‖canceledPairProduct z y‖ ≤
      ((4*(pairEntryEnvelope M δ)^2)*(N : ℝ)^(3/4 : ℝ))^N := by
  have hC : 1 ≤ pairEntryEnvelope M δ := le_max_left _ _
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨n, hn⟩ := he
    have heq : N = 2*n := by omega
    clear hn
    subst N
    have hb := complex_pairProduct_even_norm n (by omega) E y z hM hδ hy0 hy hz0 hz hc hd
    apply hb.trans
    apply (even_hadamard_to_three_quarters (by omega) (by linarith : 0 ≤ pairEntryEnvelope M δ)).trans
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (by positivity) _)
  · obtain ⟨n, hn⟩ := ho
    have heq : N = 2*n+1 := by omega
    clear hn
    subst N
    by_cases hn0 : n=0
    · subst n
      have hpair : canceledPairProduct z y = 1 := by
        unfold canceledPairProduct
        simp [Fin.eq_zero]
      rw [hpair, norm_one]
      norm_num
      nlinarith
    · have hb := complex_pairProduct_odd_norm n E y z hM hδ hy0 hy hz0 hc hd
      exact hb.trans (odd_hadamard_to_three_quarters (by omega) hC)

end
end IsoProof
