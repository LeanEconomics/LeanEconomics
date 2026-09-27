/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The enclosure certificate, as a Lean program

A computable replay of `numerics/rational/encl.py` at the calibration of `OLG7Witness` (whose
rational data are copied here as naturals, so that this module imports nothing and can be
precompiled), with
every inequality checked EXACTLY in natural-number arithmetic: no roots and no floating point.
Quantities are naturals over `D = 10^12`. The certification of a candidate `c = n/D` at a state
uses the rootless form of the interval Euler step,

  lower: `βR ∑ π (c/ℓ)^γ ≤ 1`,    upper: `βR ∑ π (c/h)^γ ≥ 1`,

cleared of denominators. The search for candidates is bisection on `n`, and only the checks
matter for soundness: `checkStage` re-verifies every stored value, and `enclCheck` is the
conjunction of the stage checks, the reach, the failure bound and the envelope.
-/

namespace LeanEconomics.EnclCert

/-- Fixed-point denominator. -/
def D : Nat := 10 ^ 12
def gam : Nat := 3
def nz : Nat := 7
def J : Nat := 60

/-- The two gross rates as `(num, den)`. -/
def R1 : Nat × Nat := (26, 25)
def R2 : Nat × Nat := (523, 500)
def beta : Nat × Nat := (24, 25)

/-- The Rouwenhorst row `z` as numerators over the common denominator `64000000`
(`piQ` of `OLG7Witness`, cleared of denominators), by cases so that proofs can evaluate it. -/
def piDen : Nat := 64000000
def piNum : Nat → Nat → Nat
  | 0, 0 => 47045881
  | 0, 1 => 14856594
  | 0, 2 => 1954815
  | 0, 3 => 137180
  | 0, 4 => 5415
  | 0, 5 => 114
  | 0, 6 => 1
  | 1, 0 => 2476099
  | 1, 1 => 47697486
  | 1, 2 => 12449085
  | 1, 3 => 1306820
  | 1, 4 => 68685
  | 1, 5 => 1806
  | 1, 6 => 19
  | 2, 0 => 130321
  | 2, 1 => 4979634
  | 2, 2 => 48090615
  | 2, 3 => 9986780
  | 2, 4 => 784815
  | 2, 5 => 27474
  | 2, 6 => 361
  | 3, 0 => 6859
  | 3, 1 => 392046
  | 3, 2 => 7490085
  | 3, 3 => 48222020
  | 3, 4 => 7490085
  | 3, 5 => 392046
  | 3, 6 => 6859
  | 4, 0 => 361
  | 4, 1 => 27474
  | 4, 2 => 784815
  | 4, 3 => 9986780
  | 4, 4 => 48090615
  | 4, 5 => 4979634
  | 4, 6 => 130321
  | 5, 0 => 19
  | 5, 1 => 1806
  | 5, 2 => 68685
  | 5, 3 => 1306820
  | 5, 4 => 12449085
  | 5, 5 => 47697486
  | 5, 6 => 2476099
  | 6, 0 => 1
  | 6, 1 => 114
  | 6, 2 => 5415
  | 6, 3 => 137180
  | 6, 4 => 1954815
  | 6, 5 => 14856594
  | 6, 6 => 47045881
  | _, _ => 0
/-- Income `y_z` as `(num, den)` (`yQ` of `OLG7Witness`). -/
def yN : Nat → Nat × Nat
  | 0 => (19264, 72101)
  | 1 => (28736, 72101)
  | 2 => (42880, 72101)
  | 3 => (64000, 72101)
  | 4 => (95488, 72101)
  | 5 => (142464, 72101)
  | 6 => (212480, 72101)
  | _ => (1, 1)
/-- The invariant law `ν_z` as `(num, den)` (`nuQ` of `OLG7Witness`). -/
def nuN : Nat → Nat × Nat
  | 0 => (1, 64)
  | 1 => (6, 64)
  | 2 => (15, 64)
  | 3 => (20, 64)
  | 4 => (15, 64)
  | 5 => (6, 64)
  | 6 => (1, 64)
  | _ => (0, 1)

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The economy's asset cap, over `D`: `2000`, the `assetCap` of `olg7`. -/
def CAP : Nat := 2000 * D

/-- The geometric part of the grid: `1%` steps from `a` up to the cap, the cap last. -/
def geom : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, a =>
    if a < CAP then
      let a' := min CAP (ceilDiv (a * 101) 100)
      a' :: geom fuel a'
    else []

/-- The grid, naturals over `D`: `0 .. 3` in steps of `1/200`, then `1%` steps up to the cap,
which is the last point. -/
def mkGrid : Array Nat :=
  ((List.range 601).map (fun i => i * (D / 200))).toArray ++ (geom 2000 (3 * D)).toArray

def grid : Array Nat := mkGrid
def NA : Nat := grid.size

/-- The grid is strictly increasing, starts at `0` and ends at the cap: checked, not proved. -/
def gridOK (_ : Unit) : Bool :=
  grid[0]! == 0 && grid[NA - 1]! == CAP &&
    (List.range (NA - 1)).all fun i => grid[i]! < grid[i+1]!

/-- Cash on hand `y_z + R a`, rounded down / up, for `a` over `D`. -/
def mDn (R : Nat × Nat) (z a : Nat) : Nat :=
  let (yn, yd) := yN z
  (yn * D * R.2 + R.1 * a * yd) / (yd * R.2)
def mUp (R : Nat × Nat) (z a : Nat) : Nat :=
  let (yn, yd) := yN z
  ceilDiv (yn * D * R.2 + R.1 * a * yd) (yd * R.2)

/-- One stage of the enclosure. `corner z` is a threshold below which `c = m` is certified. -/
structure Stage where
  lo : Array (Array Nat)
  hi : Array (Array Nat)
  corner : Array Nat
  deriving Inhabited

/-- Double indexing with runtime bounds checks. -/
def at2 (A : Array (Array Nat)) (z i : Nat) : Nat := (A[z]!)[i]!

/-- Index of the grid interval containing `ap` (last `i` with `grid[i] ≤ ap`), by bisection. -/
def findIdx (ap : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := NA - 1
  while lo < hi do
    let mid := (lo + hi + 1) / 2
    if grid[mid]! ≤ ap then lo := mid else hi := mid - 1
  return lo

/-- The chord of two lower bounds `l0 ≤ l1` at `a0 < a1`, evaluated at `ap ≥ a0` with a floored
division; the smaller of the two when they are not ordered; `0` when the points are not ordered. -/
def chordNat (a0 a1 ap l0 l1 : Nat) : Nat :=
  if a0 < a1 && a0 ≤ ap then
    (if l0 ≤ l1 then l0 + (ap - a0) * (l1 - l0) / (a1 - a0) else min l0 l1)
  else 0

/-- The lower bound on a bracketing grid interval `i`: the chord of the stored lower bounds,
with the certified kink replacing the left end when it lies inside the interval. -/
def encLoAt (R : Nat × Nat) (S : Stage) (z ap i : Nat) : Nat :=
  if i + 1 < NA && grid[i]! ≤ ap && ap ≤ grid[i+1]! && grid[i]! < grid[i+1]! then
    if grid[i]! < S.corner[z]! && S.corner[z]! ≤ ap then
      chordNat (S.corner[z]! - 1) grid[i+1]! ap (mDn R z (S.corner[z]! - 1)) (at2 S.lo z (i+1))
    else chordNat grid[i]! grid[i+1]! ap (at2 S.lo z i) (at2 S.lo z (i+1))
  else 0

/-- Lower bound on stage consumption at `ap` from the stored enclosure: below the corner
threshold `c = m` exactly; beyond the cap `0`; otherwise the chord on the bracketing interval. -/
def encLo (R : Nat × Nat) (S : Stage) (z ap : Nat) : Nat :=
  if ap < S.corner[z]! then mDn R z ap else
  if CAP < ap then 0 else
  encLoAt R S z ap (findIdx ap)

/-- The left secant through `(am, lm)` and `(a0, h0)` extended forward to `ap ≥ a0`, rounded up. -/
def leftSec (am a0 ap lm h0 : Nat) : Nat :=
  h0 + ceilDiv ((ap - a0) * ceilDiv ((h0 - lm) * D) (a0 - am)) D

/-- The right secant through `(a1, h1)` and `(a2, l2)` extended backward to `ap ≤ a1`, with the
slope floored at zero and the correction rounded down. -/
def rightSec (a1 a2 ap h1 l2 : Nat) : Nat :=
  h1 - ((a1 - ap) * (((l2 - h1) * D) / (a2 - a1))) / D

/-- The upper bound on a bracketing grid interval `i`: cash on hand `mU`, the stored bound at the
right end, and the two secants where their points are available. -/
def encHiAt (R : Nat × Nat) (S : Stage) (z ap i mU : Nat) : Nat :=
  if i + 1 < NA && grid[i]! ≤ ap && ap ≤ grid[i+1]! && grid[i]! < grid[i+1]! then
    min (min mU (at2 S.hi z (i+1)))
      (min (if 0 < i && grid[i-1]! < grid[i]! then
              leftSec grid[i-1]! grid[i]! ap (at2 S.lo z (i-1)) (at2 S.hi z i)
            else mU)
           (if i + 2 < NA && grid[i+1]! < grid[i+2]! then
              rightSec grid[i+1]! grid[i+2]! ap (at2 S.hi z (i+1)) (at2 S.lo z (i+2))
            else mU))
  else mU

/-- Upper bound on stage consumption at `ap` from the stored enclosure. -/
def encHi (R : Nat × Nat) (S : Stage) (z ap : Nat) : Nat :=
  if ap < S.corner[z]! then mUp R z ap else
  if CAP < ap then mUp R z ap else
  encHiAt R S z ap (findIdx ap) (mUp R z ap)

/-- Scale for the rounded ratios `(c/x)^γ`. -/
def SCALE : Nat := 10 ^ 30

/-- A sum over the seven earnings states, written out so that proofs can read it. -/
def sum7 (f : Nat → Nat) : Nat := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6

/-- The rootless certification at state `z` for candidate `c` (over `D`) against numbers `xs`
(over `D`): `βR ∑ π (c/x)^γ ≤ 1` when `low`, and `≥ 1` otherwise. Each ratio `(c/x)^γ` is
replaced by a rounded value over `SCALE`, rounded up for the lower test and down for the upper,
so both tests are sufficient conditions for the exact inequality. -/
def eulerTest (R : Nat × Nat) (z c : Nat) (xs : Nat → Nat) (low : Bool) : Bool :=
  let c3 := c ^ gam
  let lhs := sum7 fun i =>
    let x3 := xs i ^ gam
    piNum z i * (if low then ceilDiv (c3 * SCALE) x3 else (c3 * SCALE) / x3)
  let l := beta.1 * R.1 * lhs
  let r := beta.2 * R.2 * piDen * SCALE
  if low then l ≤ r else r ≤ l

/-- All seven numbers positive. -/
def pos7 (xs : Nat → Nat) : Bool :=
  0 < xs 0 && 0 < xs 1 && 0 < xs 2 && 0 < xs 3 && 0 < xs 4 && 0 < xs 5 && 0 < xs 6

/-- Lower certification of `n` at grid state `(z, i)`: `n ≤ m` and the Euler test against the
lower enclosure at the saving `m - n`. -/
def certL (R : Nat × Nat) (S : Stage) (z i n : Nat) : Bool :=
  let m := mDn R z grid[i]!
  if 0 < n && n ≤ m then
    let ap := m - n
    let xs := fun z' => encLo R S z' ap
    ap ≤ CAP && pos7 xs && eulerTest R z n xs true
  else false

/-- Upper certification of `n` at grid state `(z, i)`: either `n ≥ m` or the Euler test against
the upper enclosure at the saving `m - n`. -/
def certH (R : Nat × Nat) (S : Stage) (z i n : Nat) : Bool :=
  let m := mUp R z grid[i]!
  if m ≤ n then true else
    if n == 0 then false else
    let ap := m - n
    let xs := fun z' => encHi R S z' ap
    ap ≤ CAP && pos7 xs && eulerTest R z n xs false

/-- The corner test at `a` (over `D`): the Euler test with `c = m_up(a)` at zero saving. -/
def cornerTest (R : Nat × Nat) (S : Stage) (z a : Nat) : Bool :=
  let xs := fun z' => encLo R S z' 0
  pos7 xs && eulerTest R z (mUp R z a) xs true

/-! ### Search -/

/-- Bisection for the largest `n` with `certL` true, given `certL lo = true`. -/
def bisectL (R : Nat × Nat) (S : Stage) (z i : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + max 1 (lo / 10 ^ 9) then lo else
    let mid := (lo + hi) / 2
    if certL R S z i mid then bisectL R S z i fuel mid hi else bisectL R S z i fuel lo mid

/-- Bisection for the smallest `n` with `certH` true, given `certH hi = true`. -/
def bisectH (R : Nat × Nat) (S : Stage) (z i : Nat) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    if hi ≤ lo + max 1 (lo / 10 ^ 9) then hi else
    let mid := (lo + hi) / 2
    if certH R S z i mid then bisectH R S z i fuel lo mid else bisectH R S z i fuel mid hi

/-- The corner threshold: `grid[i] + 1` for the largest grid index passing the corner test,
found by bisection on the index (the test is monotone in `a`); `0` if none. -/
def findCorner (R : Nat × Nat) (S : Stage) (z : Nat) : Nat :=
  if !(cornerTest R S z grid[0]!) then 0 else Id.run do
    let mut lo := 0
    let mut hi := NA - 1
    if cornerTest R S z grid[hi]! then return grid[hi]! + 1
    while lo + 1 < hi do
      let mid := (lo + hi) / 2
      if cornerTest R S z grid[mid]! then lo := mid else hi := mid
    return grid[lo]! + 1

def fuel : Nat := 40

/-- One stage step: from the stage-`k` enclosure to stage `k+1`, both rates share the code. -/
def stepStage (R : Nat × Nat) (S : Stage) : Stage := Id.run do
  let mut lo : Array (Array Nat) := #[]
  let mut hi : Array (Array Nat) := #[]
  let mut corner : Array Nat := #[]
  for z in [0:nz] do
    let cN := findCorner R S z
    corner := corner.push cN
    let mut lz : Array Nat := Array.mkEmpty NA
    let mut hz : Array Nat := Array.mkEmpty NA
    let mut prevL : Nat := 1
    let mut prevH : Nat := 1
    let mut prevA : Nat := 0
    for i in [0:NA] do
      let a := grid[i]!
      let mD := mDn R z a
      let mU := mUp R z a
      if a < cN then
        lz := lz.push mD
        hz := hz.push mU
        prevL := mD; prevH := mU; prevA := a
      else
        -- the fixed point rises with wealth by at most `R Δa`: warm brackets from the neighbour
        let step := ceilDiv (R.1 * (a - prevA)) R.2 + D / 10 ^ 6
        let cL :=
          if certL R S z i mD then mD else
          let lo0 := if certL R S z i prevL then prevL else 1
          let hi0 := min mD (prevL + step)
          if certL R S z i hi0 then bisectL R S z i fuel hi0 mD else bisectL R S z i fuel lo0 hi0
        let cH :=
          let hi0 := min mU (prevH + step)
          if certH R S z i hi0 then bisectH R S z i fuel cL hi0 else bisectH R S z i fuel hi0 mU
        let cL := min mD cL
        let cH := min mU cH
        lz := lz.push cL
        hz := hz.push cH
        prevL := cL; prevH := cH; prevA := a
    lo := lo.push lz
    hi := hi.push hz
  return { lo := lo, hi := hi, corner := corner }

/-- The terminal stage: consumption is cash on hand. -/
def terminal (R : Nat × Nat) : Stage :=
  { lo := (List.range nz).toArray.map (fun z => grid.map (fun a => mDn R z a))
    hi := (List.range nz).toArray.map (fun z => grid.map (fun a => mUp R z a))
    corner := (List.range nz).toArray.map (fun _ => grid[NA - 1]! + 1) }

/-- All stages `0 .. J-1` at rate `R`. -/
def runStages (R : Nat × Nat) : Array Stage := Id.run do
  let mut arr : Array Stage := #[terminal R]
  for _ in [1:J] do
    arr := arr.push (stepStage R arr[arr.size - 1]!)
  return arr

/-! ### Checks -/

/-- Every stored value re-verified: the lower and upper certifications at every grid state, and
the corner test at the threshold. -/
def checkStage (R : Nat × Nat) (prev next : Stage) : Bool :=
  (List.range nz).all fun z =>
    (next.corner[z]! == 0 || cornerTest R prev z (next.corner[z]! - 1)) &&
    (List.range NA).all fun i =>
      certL R prev z i (at2 (next.lo) z (i)) && certH R prev z i (at2 (next.hi) z (i))

def checkTerminal (R : Nat × Nat) (S : Stage) : Bool :=
  (List.range nz).all fun z =>
    (List.range NA).all fun i =>
      (at2 (S.lo) z (i)) ≤ mDn R z grid[i]! && mUp R z grid[i]! ≤ (at2 (S.hi) z (i))

def checkAllStages (R : Nat × Nat) (arr : Array Stage) : Bool :=
  arr.size == J && checkTerminal R arr[0]! &&
    (List.range (J - 1)).all fun k => checkStage R arr[k]! arr[k+1]!

/-- The largest of seven values. -/
def max7 (f : Nat → Nat) : Nat :=
  max (f 0) (max (f 1) (max (f 2) (max (f 3) (max (f 4) (max (f 5) (f 6))))))

/-- Reach: an upper bound on the assets a cohort can hold at age `j` (`j = 0` newborn), from
the saving bound `m_up - lo` of the stage a cohort of that age is at. -/
def reachOf (R : Nat × Nat) (arr : Array Stage) : Nat → Nat
  | 0 => 0
  | j + 1 =>
    let a := reachOf R arr j
    max7 fun z => mUp R z a - encLo R arr[J - 1 - j]! z a

/-- The maximum of `f` over `0 .. n-1`. -/
def maxRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxRange f n) (f n)

/-- `Δr = Rb - Ra` as a fraction. -/
def drOf (Ra Rb : Nat × Nat) : Nat × Nat := (Rb.1 * Ra.2 - Ra.1 * Rb.2, Ra.2 * Rb.2)

/-- The failure bound at stage `s` and state `z`: over the grid intervals `[a_i, a_{i+1}]` with
`a_i` inside the reach `rj`, the largest `hi₂(a_{i+1}) - lo₁(a_i) - Δr a_i`. -/
def failBound (Ra Rb : Nat × Nat) (S1 S2 : Stage) (rj z : Nat) : Nat :=
  maxRange (fun i => if grid[i]! ≤ rj then
      at2 S2.hi z (i+1) - at2 S1.lo z i - (grid[i]! * (drOf Ra Rb).1) / (drOf Ra Rb).2
    else 0) (NA - 1)

/-- Upper bound on the Lipschitz constants `cohortSlope` at the higher rate, from a lower bound
`kapLo` on every stage propensity. -/
def slopeUp (Rb : Nat × Nat) (kap : Rat) : Nat → Rat
  | 0 => 1
  | k + 1 => 1 + slopeUp Rb kap k * (1 - kap) * ((Rb.1 : Rat) / Rb.2)

/-- `∑_{i<n} q^i`. -/
def geomSum (q : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => geomSum q n + q ^ n

/-- `Þ ≤ tUp` at the higher rate, with `tUp^3 ≥ βR₂`; `κ_k ≥ 1/∑_{i<60} (tUp/R₂)^i`. -/
def tUp : Rat := (100139 : Rat) / 100000
def kapLoOf (Rb : Nat × Nat) : Rat := 1 / geomSum (tUp * Rb.2 / Rb.1) J

def budgetOf (Ra Rb : Nat × Nat) : Rat :=
  let al : Rat := 9 / 25
  let de : Rat := 2 / 25
  al / ((1 - al) * ((Ra.1 : Rat) / Ra.2 - 1 + de))
    - al / ((1 - al) * ((Rb.1 : Rat) / Rb.2 - 1 + de))

/-- `∑_{k<n} f k` in the rationals. -/
def sumRange (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- `∑_z ν_z f z` in the rationals. -/
def nuSum (f : Nat → Rat) : Rat :=
  sumRange (fun z => ((nuN z).1 : Rat) / (nuN z).2 * f z) nz

/-- The accumulated bound `B = ∑_{k<K} G_k ∑_z ν_z V_{k+1}(z) / (K+1)`, `K = J - 1`, with the
reach of the cohort at the age with `k+1` periods to go. -/
def accumulated (Ra Rb : Nat × Nat) (arr1 arr2 : Array Stage) (reach : Nat → Nat) : Rat :=
  sumRange (fun k => slopeUp Rb (kapLoOf Rb) k *
    nuSum fun z => (failBound Ra Rb arr1[k+1]! arr2[k+1]! (reach (J - 2 - k)) z : Rat) / D)
    (J - 1) / J

/-- **The certificate**, as a function of the two rates so that no closed subterm of it is a
whole run: instantiated at `(R1, R2)` only where it is evaluated. -/
def enclCheckOf (Ra Rb : Nat × Nat) : Bool :=
  let arr1 := runStages Ra
  let arr2 := runStages Rb
  let reach := fun j => max (reachOf Ra arr1 j) (reachOf Rb arr2 j)
  gridOK () && checkAllStages Ra arr1 && checkAllStages Rb arr2 &&
    (List.range J).all (fun j => reach j < CAP) &&
    tUp ^ 3 ≥ (beta.1 : Rat) / beta.2 * ((Rb.1 : Rat) / Rb.2) &&
    decide (accumulated Ra Rb arr1 arr2 reach < budgetOf Ra Rb)

/-- Diagnostics for a run outside the kernel. -/
def report : IO Unit := do
  let out ← IO.getStdout
  let say := fun (msg : String) => do out.putStrLn msg; out.flush
  let t0 ← IO.monoMsNow
  say s!"grid points {NA}"
  let mut arr1 : Array Stage := #[terminal R1]
  let mut arr2 : Array Stage := #[terminal R2]
  for k in [1:J] do
    arr1 := arr1.push (stepStage R1 arr1[arr1.size - 1]!)
    arr2 := arr2.push (stepStage R2 arr2[arr2.size - 1]!)
    let tk ← IO.monoMsNow
    let w := (List.range nz).foldl (fun acc z => (List.range NA).foldl (fun acc' i =>
      if grid[i]! ≤ 10 * D then
        max acc' ((at2 (arr2[k]!.hi) z (i)) - (at2 (arr2[k]!.lo) z (i)))
      else acc') acc) 0
    say s!"stage {k}: {tk - t0} ms, max width on a<=10 at rate 2: {w.toFloat / D.toFloat}"
  let t1 ← IO.monoMsNow
  let reach := fun j => max (reachOf R1 arr1 j) (reachOf R2 arr2 j)
  let rf := [reach 1, reach 10, reach 30, reach 59].map (fun x => x.toFloat / D.toFloat)
  say s!"reach at ages 1,10,30,59: {rf}"
  let ok1 := checkAllStages R1 arr1
  let ok2 := checkAllStages R2 arr2
  say s!"stage checks {ok1} {ok2}"
  let B := accumulated R1 R2 arr1 arr2 reach
  let bf := (B * 1000000).floor
  let gf := (budgetOf R1 R2 * 1000000).floor
  say s!"B ≈ {bf} e-6   budget ≈ {gf} e-6   gridOK {gridOK ()}"
  say s!"enclCheck = {decide (B < budgetOf R1 R2) && ok1 && ok2}"
  let t3 ← IO.monoMsNow
  say s!"checks in {t3 - t1} ms"

end LeanEconomics.EnclCert
