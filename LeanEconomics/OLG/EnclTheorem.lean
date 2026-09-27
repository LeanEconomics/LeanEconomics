/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LeanEconomics.OLG.EnclCertified
import LeanEconomics.OLG.EnclFinal

/-!
# The certified increment at `γ = 3`

The checker's verdict (`EnclCertified`, by `native_decide`) meets the bridge (`EnclFinal`): for
the seven-state life cycle `olg7` with `γ = 3`, `β = 24/25` and the cap `2000`, capital supply
rises between `4%` and `4.6%` by more than the firm's demand falls. The two rates are therefore
not both stationary equilibria. This is the pairwise statement the certificate proves; it is not
uniqueness on an interval.
-/

namespace LeanEconomics.EnclCert

/-- **The certified pairwise single crossing at `γ = 3`.** -/
theorem olg7_increment :
    olgDemand (23 / 500) - olgDemand (1 / 25)
      < olg7hi.olgCapital 59 nuR - olg7.olgCapital 59 nuR :=
  increment_of_enclCheck enclCheck_eq_true

end LeanEconomics.EnclCert
