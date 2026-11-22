import IsoProof.Objects
import IsoProof.JetTrace

/-! Shared producer interface for manuscript §5.  An interval may depend on
the finite jet order, so all finitely many low-order collision levels can be
removed before choosing it.  This record is not a terminal theorem premise:
the final susceptibility proof must supply an internally proved constructor. -/
namespace IsoProof
noncomputable section
open Set

structure RegularEnergyJetInterval (ν : Phase) (n : ℕ) where
  left : ℝ
  right : ℝ
  height : ℝ
  left_pos : 0 < left
  left_lt_right : left < right
  right_lt_two : right < 2
  height_pos : 0 < height
  jet : ℕ → ℂ → ℂ
  continuous : ∀ j < n, ContinuousOn (jet j) (closedUpperCollar left right height)
  agrees : ∀ E ∈ upperCollar left right height, ∀ j < n,
    jet j E = iteratedDeriv j (fullEnergySum ν .positive) E

end
end IsoProof
