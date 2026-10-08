/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EnclCert.Outer

/-!
# The outer-range checker's verdicts

Both meshes pass: the ceiling cells from `-8%` to `2.3%` and the floor cells from `8.7%` to
`20%`. Each verdict is established by `native_decide`, compiled evaluation of the checker of
`EnclCert.Outer` (about five minutes), and introduces the `Lean.ofReduceBool` axiom; everything
downstream (`OLG/OuterBridge`, `OLG/OuterTheorem`) is checked by the kernel.
-/

namespace LeanEconomics.EnclCert

/-- **The ceiling mesh passes.** -/
theorem lowCheck_eq_true : lowCheck () = true := by native_decide

/-- **The floor mesh passes.** -/
theorem highCheck_eq_true : highCheck () = true := by native_decide

end LeanEconomics.EnclCert
