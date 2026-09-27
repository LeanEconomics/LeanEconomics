/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EnclCert.Check

/-!
# The certificate, replayed

`EnclCert.enclCheckOf R1 R2` is the enclosure certificate of `numerics/rational/encl.py` as a Lean program:
the two rates `1/25` and `23/500`, relative risk aversion `3`, the seven-state Rouwenhorst chain,
sixty periods, a grid of `1255` points up to the cap `2000`. This module evaluates it. It is a
separate module so that the seventeen minutes of compiled arithmetic are paid only when the
checker changes; what the value `true` means for the economy is proved in `OLG/EnclBridge`.
-/

namespace LeanEconomics.EnclCert

/-- **The arithmetic of the enclosure certificate holds.** Evaluated by compiled code
(`native_decide`). -/
theorem enclCheck_eq_true : enclCheckOf R1 R2 = true := by native_decide

end LeanEconomics.EnclCert
