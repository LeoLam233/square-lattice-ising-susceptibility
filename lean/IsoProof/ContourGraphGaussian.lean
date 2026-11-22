import IsoProof.ContourGaussian
import IsoProof.IntegralsGraphTensor

/-! Actual recursive integration over all three graph pieces. The harmless
factor 3 per coordinate is retained explicitly, so no false replacement of
a piecewise Jacobian by a single tangent vector is made. -/
namespace IsoProof
noncomputable section
open Set
open scoped BigOperators

def graphJacobianBound (b v : ℝ) : ℝ :=
  max ‖(1 : ℂ)+Complex.I*(v : ℂ)‖
    ‖(1 : ℂ)+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))‖

theorem graphJacobianBound_nonneg (b v : ℝ) : 0 ≤ graphJacobianBound b v :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem protectedGraphIntegral_gaussian_bound {b β K : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (hβ : 0 < β) (hK : 0 ≤ K) (v c : ℝ) (F : ℂ → ℂ)
    (hF : ∀ r ∈ Icc (-Real.pi) Real.pi,
      ‖F (scalarGraph b v r c)‖ ≤ K*Real.exp (-β*(r-c)^2)) :
    ‖protectedGraphIntegral F b v c‖ ≤ K*(3*graphJacobianBound b v*Real.sqrt (Real.pi/β)) := by
  let J := graphJacobianBound b v
  have hJ : 0 ≤ J := graphJacobianBound_nonneg b v
  have hinterval (u w : ℝ) (huw : u ≤ w)
      (hsub : Icc u w ⊆ Icc (-Real.pi) Real.pi) (ζ : ℂ) (hζ : ‖ζ‖ ≤ J) :
      ‖∫ r in u..w, F (scalarGraph b v r c)*ζ‖ ≤
        (K*J)*Real.sqrt (Real.pi/β) := by
    apply norm_intervalIntegral_le_gaussian hβ (mul_nonneg hK hJ) c u w huw
    intro r hr
    rw [norm_mul]
    have h := mul_le_mul (hF r (hsub hr)) hζ (norm_nonneg _) (by positivity)
    nlinarith [Real.exp_pos (-β*(r-c)^2)]
  have hl := hinterval (-Real.pi) (-b) (by linarith)
    (by intro r hr; exact ⟨hr.1,hr.2.trans (by linarith)⟩)
    (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))) (le_max_right _ _)
  have hm := hinterval (-b) b (by linarith)
    (by intro r hr; exact ⟨(by linarith : -Real.pi ≤ -b).trans hr.1,hr.2.trans hbpi.le⟩)
    (1+Complex.I*(v : ℂ)) (le_max_left _ _)
  have hr := hinterval b Real.pi hbpi.le
    (by intro r hr; exact ⟨(by linarith : -Real.pi ≤ b).trans hr.1,hr.2⟩)
    (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))) (le_max_right _ _)
  rw [protectedGraphIntegral_eq_graph hb hbpi]
  have hnorm := (norm_add_le
    ((∫ r in (-Real.pi)..(-b), F (scalarGraph b v r c)*
      (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))))+
      (∫ r in (-b)..b, F (scalarGraph b v r c)*(1+Complex.I*(v : ℂ))))
    (∫ r in b..Real.pi, F (scalarGraph b v r c)*
      (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith

/-- Every angular coordinate contributes its genuine Gaussian half power.
This theorem is applied to the actual full coupled pair density. -/
theorem protectedGraphMultiIntegral_gaussian_bound {b β : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (hβ : 0 < β) (v c : ℝ) (N : ℕ) :
    ∀ {K : ℝ}, 0 ≤ K → ∀ F : (Fin N → ℂ) → ℂ,
      (∀ r : Fin N → ℝ, (∀ i, r i ∈ Icc (-Real.pi) Real.pi) →
        ‖F (fun i => scalarGraph b v (r i) c)‖ ≤ K*centeredGaussian N β c r) →
      ‖protectedGraphMultiIntegral b v c N F‖ ≤
        K*(3*graphJacobianBound b v*Real.sqrt (Real.pi/β))^N := by
  induction N with
  | zero =>
      intro K hK F hF
      have h := hF Fin.elim0 (fun i => Fin.elim0 i)
      have heq : (fun i : Fin 0 => scalarGraph b v (Fin.elim0 i) c) = (Fin.elim0 : Fin 0 → ℂ) := by
        funext i
        exact Fin.elim0 i
      simpa [protectedGraphMultiIntegral,centeredGaussian,heq] using h
  | succ n ih =>
      intro K hK F hF
      let L := 3*graphJacobianBound b v*Real.sqrt (Real.pi/β)
      have hJ := graphJacobianBound_nonneg b v
      have hL : 0 ≤ L := by dsimp [L]; positivity
      have hbound (r : ℝ) (hr : r ∈ Icc (-Real.pi) Real.pi) :
          ‖protectedGraphMultiIntegral b v c n
            (fun q => F (Fin.cons (scalarGraph b v r c) q))‖ ≤
            (K*L^n)*Real.exp (-β*(r-c)^2) := by
        have hi := ih (K := K*Real.exp (-β*(r-c)^2)) (by positivity)
          (fun q => F (Fin.cons (scalarGraph b v r c) q)) (by
            intro rs hrs
            have h := hF (Fin.cons r rs) (fun i => Fin.cases hr (fun j => hrs j) i)
            have heq : (fun i => scalarGraph b v ((Fin.cons r rs : Fin (n+1) → ℝ) i) c) =
                Fin.cons (scalarGraph b v r c) (fun i => scalarGraph b v (rs i) c) := by
              funext i
              refine Fin.cases ?_ (fun j => ?_) i <;> rfl
            rw [heq] at h
            simpa [centeredGaussian,Fin.prod_univ_succ,mul_assoc] using h)
        simpa only [L,mul_assoc,mul_left_comm,mul_comm] using hi
      have h := protectedGraphIntegral_gaussian_bound hb hbpi hβ
        (mul_nonneg hK (pow_nonneg hL _)) v c
        (fun z => protectedGraphMultiIntegral b v c n (fun q => F (Fin.cons z q))) hbound
      simpa only [protectedGraphMultiIntegral,L,pow_succ,mul_assoc] using h

end
end IsoProof
