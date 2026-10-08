import EnclCert.Outer

/-- Runs the outer-range checker on both meshes and prints the verdicts with timings. -/
def main : IO Unit := do
  let t0 ← IO.monoMsNow
  let lo := LeanEconomics.EnclCert.lowCheck ()
  let t1 ← IO.monoMsNow
  IO.println s!"lowCheck (ceiling, 165 cells): {lo}  [{t1 - t0} ms]"
  let hi := LeanEconomics.EnclCert.highCheck ()
  let t2 ← IO.monoMsNow
  IO.println s!"highCheck (floor, 121 cells): {hi}  [{t2 - t1} ms]"
