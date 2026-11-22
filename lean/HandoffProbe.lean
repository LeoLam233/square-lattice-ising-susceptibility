import Mathlib.Lean.Expr.Basic

namespace HandoffProbe

/-- A small target for testing source compilation and kernel replay on a new machine. -/
theorem addZero (n : Nat) : n + 0 = n := Nat.add_zero n

end HandoffProbe
