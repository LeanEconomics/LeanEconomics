/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EnclCert.Check

/-!
# The outer-range checker: ceiling below demand, floor above demand, on cells of rates

A computable replay of `numerics/rational/outer_proto.py`. On a cell of rates `[m₁, m₂]` (in units
of `10⁻⁶`) it computes, as integers over `D`, interval bounds on the finite-horizon propensity
`κ_k`, the patience factor `Þ`, human wealth, risk-adjusted human wealth, the cohort slope and
the affine ceiling intercept (`cohortCeil`), and, on the other side, the clamped floor
`cohortFloorAt` on a grid; and it then compares the ceiling with demand at the top of the cell and
the floor with demand at the bottom.

Every stored value is computed however is convenient and then **verified** by an exact
integer inequality with denominators cleared; only those inequalities are used by the bridge
(`OLG/OuterBridge`), so nothing here needs to be proved correct beyond the final `Bool`.
-/

namespace LeanEconomics.EnclCert

/-- `D` as an integer. -/
def DI : Int := (D : Int)
/-- Rates are integers over `RD`: `r = m / RD`. -/
def RD : Int := 1000000
/-- The asset cap of the outer-range economy, `10⁶` (a level, not over `D`). -/
def CAPC : Int := 1000000
/-- The gross rate `R = (RD + m) / RD`, numerator. -/
def Rn (m : Int) : Int := RD + m

/-- Ceiling division for a positive divisor. -/
def cdiv (a b : Int) : Int := -((-a) / b)

def yDn (z : Nat) : Int := (((yN z).1 * D) / (yN z).2 : Nat)
def yUp (z : Nat) : Int := (ceilDiv ((yN z).1 * D) (yN z).2 : Nat)
def piI (z w : Nat) : Int := (piNum z w : Int)
def piDenI : Int := (piDen : Int)
def nuI (z : Nat) : Int := ((nuN z).1 : Int)
def sumI (f : Nat → Int) : Int := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6

/-- Integer cube root, rounded down: binary search. -/
def icbrtAux : Nat → Nat → Nat → Nat → Nat
  | 0, lo, _, _ => lo
  | fuel + 1, lo, hi, n =>
    if hi ≤ lo then lo else
      let mid := (lo + hi + 1) / 2
      if mid ^ 3 ≤ n then icbrtAux fuel mid hi n else icbrtAux fuel lo (mid - 1) n
def icbrt (n : Nat) : Nat := icbrtAux 400 0 (2 ^ (n.log2 / 3 + 2)) n

/-! ### Patience and the propensity -/

/-- `tLo/D ≤ Þ` on the cell: `(tLo/D)³ ≤ β R₁`. -/
def mkTLo (m1 : Int) : Int := (icbrt ((24 * Rn m1 * DI ^ 3) / (25 * RD)).toNat : Int)
/-- `Þ ≤ tHi/D` on the cell: `β R₂ ≤ (tHi/D)³`. -/
def mkTHi (m2 : Int) : Int :=
  let x := cdiv (24 * Rn m2 * DI ^ 3) (25 * RD)
  let c : Int := (icbrt x.toNat : Int)
  if x ≤ c ^ 3 then c else c + 1

def tOK (m1 m2 tLo tHi : Int) : Bool :=
  decide (0 < Rn m1) && decide (m1 ≤ m2) && decide (0 < tLo) && decide (0 < tHi)
    && decide (tLo ^ 3 * 25 * RD ≤ 24 * Rn m1 * DI ^ 3)
    && decide (24 * Rn m2 * DI ^ 3 ≤ tHi ^ 3 * 25 * RD)

/-- Lower bounds on `κ_k`: the recursion at `R₁` and `tHi`, rounded down. -/
def mkKapLo (m1 tHi : Int) : Array Int :=
  (List.range (J - 1)).foldl (fun arr _ =>
    let k := arr.back!
    let x := (k * Rn m1) / RD
    arr.push ((x * DI) / (tHi + x))) #[DI]
/-- Upper bounds on `κ_k`: the recursion at `R₂` and `tLo`, rounded up. -/
def mkKapHi (m2 tLo : Int) : Array Int :=
  (List.range (J - 1)).foldl (fun arr _ =>
    let k := arr.back!
    let x := cdiv (k * Rn m2) RD
    arr.push (cdiv (x * DI) (tLo + x))) #[DI]

def kapOK (m1 m2 tLo tHi : Int) (kLo kHi : Array Int) : Bool :=
  decide (kLo.size = J) && decide (kHi.size = J) && decide (kLo[0]! = DI) && decide (kHi[0]! = DI)
    && (List.range (J - 1)).all fun k =>
      decide (0 ≤ kLo[k+1]!)
        && decide (kLo[k+1]! * (tHi * RD + kLo[k]! * Rn m1) ≤ kLo[k]! * Rn m1 * DI)
        && decide (0 < kHi[k+1]!) && decide (kHi[k+1]! ≤ DI)
        && decide (kHi[k]! * Rn m2 * DI ≤ kHi[k+1]! * (tLo * RD + kHi[k]! * Rn m2))

/-! ### Human wealth, risk-adjusted and plain -/

/-- The scale of the power-mean sum. -/
def Q : Int := DI ^ 3
/-- One term of the rounded-up sum `∑ π (D/x)³`, over `Q`. -/
def sTerm (xs : Nat → Int) (z w : Nat) : Int :=
  if piNum z w = 0 then 0 else cdiv (piI z w * DI ^ 3 * Q) (piDenI * xs w ^ 3)
def sUp (xs : Nat → Int) (z : Nat) : Int := sumI (sTerm xs z)
/-- `m` with `m³ · sUp ≤ D³ Q`, so `m/D` is below the power mean of exponent `-3`. -/
def mkPM (xs : Nat → Int) (z : Nat) : Int := (icbrt ((DI ^ 3 * Q) / sUp xs z).toNat : Int)
def pmOK (xs : Nat → Int) (z : Nat) (m : Int) : Bool :=
  decide (0 ≤ m) && decide (m ^ 3 * sUp xs z ≤ DI ^ 3 * Q)
    && (List.range 7).all fun w =>
      decide (0 < xs w) && (piNum z w = 0
        || decide (piI z w * DI ^ 3 * Q ≤ sTerm xs z w * (piDenI * xs w ^ 3)))

/-- Lower bounds on risk-adjusted human wealth `Hr_k(z)`, with the power-mean bounds used. -/
def mkHr (m2 : Int) (kHi : Array Int) : Array (Array Int) × Array (Array Int) :=
  (List.range (J - 1)).foldl (fun (p : Array (Array Int) × Array (Array Int)) k =>
    let prev := p.1.back!
    let xs : Nat → Int := fun w => yDn w + prev[w]!
    let k1 := kHi[k+1]!
    let pm := Array.ofFn (n := 7) fun z => mkPM xs z
    let hr := Array.ofFn (n := 7) fun z =>
      let t1 := (pm[z]! * RD) / Rn m2
      let t2 := ((DI - k1) * yDn z) / k1
      max 0 (min t1 t2)
    (p.1.push hr, p.2.push pm)) (#[Array.replicate 7 0], #[Array.replicate 7 0])

def hrOK (m2 : Int) (kHi : Array Int) (hr pm : Array (Array Int)) : Bool :=
  decide (hr.size = J) && decide (pm.size = J)
    && ((List.range 7).all fun z => decide (hr[0]![z]! = 0))
    && (List.range (J - 1)).all fun k =>
      let xs : Nat → Int := fun w => yDn w + hr[k]![w]!
      (List.range 7).all fun z =>
        pmOK xs z pm[k+1]![z]!
          && decide (0 ≤ hr[k+1]![z]!)
          && decide (hr[k+1]![z]! * Rn m2 ≤ pm[k+1]![z]! * RD)
          && decide (hr[k+1]![z]! * kHi[k+1]! ≤ (DI - kHi[k+1]!) * yDn z)

/-- Upper bounds on human wealth `H_k(z)`: the recursion at `R₁`, rounded up. -/
def mkHHi (m1 : Int) : Array (Array Int) :=
  (List.range (J - 1)).foldl (fun arr _ =>
    let prev := arr.back!
    arr.push (Array.ofFn (n := 7) fun z =>
      cdiv (sumI (fun w => piI z w * (yUp w + prev[w]!)) * RD) (piDenI * Rn m1)))
    #[Array.replicate 7 0]

def hHiOK (m1 : Int) (hHi : Array (Array Int)) : Bool :=
  decide (hHi.size = J) && ((List.range 7).all fun z => decide (hHi[0]![z]! = 0))
    && (List.range (J - 1)).all fun k => (List.range 7).all fun z =>
      decide (sumI (fun w => piI z w * (yUp w + hHi[k]![w]!)) * RD
        ≤ hHi[k+1]![z]! * piDenI * Rn m1)

/-! ### The cohort slope and the ceiling -/

def mkG (m1 m2 : Int) (kLo kHi : Array Int) : Array Int × Array Int :=
  (List.range (J - 1)).foldl (fun (p : Array Int × Array Int) k =>
    let gLo := p.1.back!; let gHi := p.2.back!
    (p.1.push (DI + (gLo * (DI - kHi[k+1]!) * Rn m1) / (DI * RD)),
     p.2.push (DI + cdiv (gHi * (DI - kLo[k+1]!) * Rn m2) (DI * RD)))) (#[DI], #[DI])

def gOK (m1 m2 : Int) (kLo kHi gLo gHi : Array Int) : Bool :=
  decide (gLo.size = J) && decide (gHi.size = J) && decide (gLo[0]! = DI) && decide (gHi[0]! = DI)
    && (List.range (J - 1)).all fun k =>
      decide (0 ≤ gLo[k+1]!)
        && decide (gLo[k+1]! * DI * RD ≤ DI * DI * RD + gLo[k]! * (DI - kHi[k+1]!) * Rn m1)
        && decide (DI * DI * RD + gHi[k]! * (DI - kLo[k+1]!) * Rn m2 ≤ gHi[k+1]! * DI * RD)

/-- The ceiling intercept's per-stage increment, times `D²`. -/
def bTerm (kLo1 : Int) (hr1 : Array Int) (z : Nat) : Int :=
  (DI - kLo1) * yUp z - kLo1 * hr1[z]!

def mkFc (kLo gLo gHi : Array Int) (hr : Array (Array Int)) : Array (Array Int) :=
  (List.range (J - 1)).foldl (fun arr k =>
    let prev := arr.back!
    arr.push (Array.ofFn (n := 7) fun z =>
      let b := bTerm kLo[k+1]! hr[k+1]! z
      let G := if 0 ≤ b then gHi[k]! else gLo[k]!
      cdiv (DI * DI * sumI (fun w => piI z w * prev[w]!) + G * b * piDenI) (DI * DI * piDenI)))
    #[Array.replicate 7 0]

def fcOK (kLo gLo gHi : Array Int) (hr fc : Array (Array Int)) : Bool :=
  decide (fc.size = J) && ((List.range 7).all fun z => decide (fc[0]![z]! = 0))
    && (List.range (J - 1)).all fun k => (List.range 7).all fun z =>
      let b := bTerm kLo[k+1]! hr[k+1]! z
      let G := if 0 ≤ b then gHi[k]! else gLo[k]!
      decide (DI * DI * sumI (fun w => piI z w * fc[k]![w]!) + G * b * piDenI
        ≤ fc[k+1]![z]! * DI * DI * piDenI)

/-- Demand in wage units at `m/RD` is `225 RD / (16 (25 m + 2 RD))`; the ceiling, averaged with
`ν = nuN/64` over `60` cohorts and read over `D`, is below it iff this holds. -/
def ceilLtDemand (m2 : Int) (fc59 : Array Int) : Bool :=
  decide (0 < 25 * m2 + 2 * RD)
    && decide (sumI (fun z => nuI z * fc59[z]!) * 16 * (25 * m2 + 2 * RD) < 225 * RD * 3840 * DI)

/-- Cap slack at every stage, from impatience against the cap: either the limiting propensity
`1 - Þ/R` does the work (route A) or the rate is negative enough that `y_max + r·cap ≤ 0`
(route B). -/
def slackOK (m1 m2 tHi : Int) : Bool :=
  (decide (tHi * RD < DI * Rn m1)
    && decide ((212480 * RD + 72101 * m2 * CAPC) * DI * Rn m1 * tHi
      < (DI * Rn m1 - tHi * RD) * (19264 * RD + 72101 * Rn m1 * CAPC) * DI))
  || decide (212480 * RD + 72101 * m2 * CAPC ≤ 0)

/-- **The ceiling cell check.** -/
def cellCeilOK (m1 m2 : Int) : Bool :=
  let tLo := mkTLo m1; let tHi := mkTHi m2
  let kLo := mkKapLo m1 tHi; let kHi := mkKapHi m2 tLo
  let hrpm := mkHr m2 kHi
  let g := mkG m1 m2 kLo kHi
  let fc := mkFc kLo g.1 g.2 hrpm.1
  tOK m1 m2 tLo tHi && kapOK m1 m2 tLo tHi kLo kHi && hrOK m2 kHi hrpm.1 hrpm.2
    && gOK m1 m2 kLo kHi g.1 g.2 && fcOK kLo g.1 g.2 hrpm.1 fc
    && slackOK m1 m2 tHi && ceilLtDemand m2 fc[J-1]!

/-! ### The floor side -/

/-- The floor grid, integers over `D`: `0 .. 3` in steps of `1/100`, then `2%` steps to `3000`. -/
def geomF : Nat → Int → List Int
  | 0, _ => []
  | fuel + 1, a =>
    if a < 3000 * DI then
      let a' := cdiv (a * 51) 50
      a' :: geomF fuel a'
    else []
def gridF : Array Int :=
  ((List.range 301).map (fun (i : Nat) => (i : Int) * (DI / 100))).toArray ++ (geomF 2000 (3 * DI)).toArray
def NAF : Nat := gridF.size
def gridFOK (gF : Array Int) : Bool :=
  decide (0 < gF.size) && decide (gF[0]! = 0)
    && (List.range (gF.size - 1)).all fun i => decide (gF[i]! < gF[i+1]!)

/-- The largest grid index whose point is at most `φ` (binary search; `φ ≥ 0`). -/
def idxAux (gF : Array Int) : Nat → Nat → Nat → Int → Nat
  | 0, lo, _, _ => lo
  | fuel + 1, lo, hi, φ =>
    if hi ≤ lo then lo else
      let mid := (lo + hi + 1) / 2
      if gF[mid]! ≤ φ then idxAux gF fuel mid hi φ else idxAux gF fuel lo (mid - 1) φ
def idxBelow (gF : Array Int) (φ : Int) : Nat := idxAux gF 40 0 (gF.size - 1) φ

/-- Upper bounds on the crude reach `ρ_j` at `R₂`. -/
def mkReach (m2 : Int) : Array Int :=
  (List.range J).foldl (fun arr _ => arr.push (cdiv (arr.back! * Rn m2) RD + yUp 6)) #[0]
def reachOK (m2 : Int) (rc : Array Int) : Bool :=
  decide (rc.size = J + 1) && decide (rc[0]! = 0)
    && ((List.range J).all fun j => decide (rc[j]! * Rn m2 + yUp 6 * RD ≤ rc[j+1]! * RD))
    && decide (rc[J]! < CAPC * DI)

/-- The lower bound on the clamped saving floor `Φ_{k+1}(z, a_i)`, over `D` (before the clamp). -/
def phiLo (gF : Array Int) (m1 kHi1 hHi1z : Int) (z i : Nat) : Int :=
  ((DI - kHi1) * (yDn z + (gF[i]! * Rn m1) / RD)) / DI - cdiv (kHi1 * hHi1z) DI

/-- Lower bounds on `Λ_k(z, a_i)` (`cohortFloorAt`), stage by stage on the grid. -/
def mkLam (gF : Array Int) (m1 : Int) (kHi : Array Int) (hHi : Array (Array Int)) :
    Array (Array (Array Int)) :=
  (List.range (J - 1)).foldl (fun arr k =>
    let prev := arr.back!
    let k1 := kHi[k+1]!
    arr.push (Array.ofFn (n := 7) fun z =>
      let h1 := hHi[k+1]![z]!
      Array.ofFn (n := gF.size) fun i =>
        let j := idxBelow gF (max 0 (phiLo gF m1 k1 h1 z i))
        gF[i]! + (sumI (fun w => piI z w * prev[w]![j]!)) / piDenI))
    #[Array.ofFn (n := 7) fun _ => gF]

def lamOK (gF : Array Int) (m1 : Int) (kHi : Array Int) (hHi : Array (Array Int))
    (lam : Array (Array (Array Int))) : Bool :=
  decide (lam.size = J)
    && ((List.range 7).all fun z => (List.range gF.size).all fun i =>
        decide (lam[0]![z]![i]! = gF[i]!))
    && (List.range (J - 1)).all fun k => (List.range 7).all fun z =>
      (List.range gF.size).all fun i =>
      let j := idxBelow gF (max 0 (phiLo gF m1 kHi[k+1]! hHi[k+1]![z]! z i))
      decide (j < gF.size)
        && (decide (j = 0) || decide (gF[j]! * DI * RD
            ≤ (DI - kHi[k+1]!) * (yDn z * RD + gF[i]! * Rn m1) - kHi[k+1]! * hHi[k+1]![z]! * RD))
        && decide (lam[k+1]![z]![i]! * piDenI
            ≤ gF[i]! * piDenI + sumI (fun w => piI z w * lam[k]![w]![j]!))

def demandLtFloor (m1 : Int) (lam59 : Array (Array Int)) : Bool :=
  decide (0 < 25 * m1 + 2 * RD)
    && decide (225 * RD * 3840 * DI < sumI (fun z => nuI z * lam59[z]![0]!) * 16 * (25 * m1 + 2 * RD))

/-- **The floor cell check.** -/
def cellFloorOK (m1 m2 : Int) : Bool :=
  let tLo := mkTLo m1; let tHi := mkTHi m2
  let kLo := mkKapLo m1 tHi; let kHi := mkKapHi m2 tLo
  let hHi := mkHHi m1
  let rc := mkReach m2
  let lam := mkLam gridF m1 kHi hHi
  tOK m1 m2 tLo tHi && kapOK m1 m2 tLo tHi kLo kHi && hHiOK m1 hHi && reachOK m2 rc
    && gridFOK gridF && lamOK gridF m1 kHi hHi lam && demandLtFloor m1 lam[J-1]!

/-! ### The meshes -/

/-- Breakpoints of the low mesh, `-8%` to `2.3%`: `0.1` points to `1.5%`, `0.02` to `2.1%`,
`0.005` to `2.3%`. -/
def bLow (i : Nat) : Int :=
  if i ≤ 95 then -80000 + 1000 * (i : Int)
  else if i ≤ 125 then 15000 + 200 * ((i : Int) - 95)
  else 21000 + 50 * ((i : Int) - 125)
def nLow : Nat := 165

/-- Breakpoints of the high mesh, `8.7%` to `20%`: `0.01` points to `9.5%`, `0.1` to `12%`,
`0.5` to `20%`. -/
def bHigh (i : Nat) : Int :=
  if i ≤ 80 then 87000 + 100 * (i : Int)
  else if i ≤ 105 then 95000 + 1000 * ((i : Int) - 80)
  else 120000 + 5000 * ((i : Int) - 105)
def nHigh : Nat := 121

def lowCheck (_ : Unit) : Bool :=
  decide (bLow 0 = -80000) && decide (bLow nLow = 23000)
    && (List.range nLow).all fun i => decide (bLow i < bLow (i + 1)) && cellCeilOK (bLow i) (bLow (i + 1))

def highCheck (_ : Unit) : Bool :=
  decide (bHigh 0 = 87000) && decide (bHigh nHigh = 200000)
    && (List.range nHigh).all fun i =>
      decide (bHigh i < bHigh (i + 1)) && cellFloorOK (bHigh i) (bHigh (i + 1))

end LeanEconomics.EnclCert
