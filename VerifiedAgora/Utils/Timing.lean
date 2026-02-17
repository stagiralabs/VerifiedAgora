import Lean

open Lean IO

structure TimingStats where
  totalMs : Nat := 0
  count : Nat := 0
  maxMs : Nat := 0
  deriving Inhabited

structure TimingState where
  order : Array String := #[]
  stats : Std.HashMap String TimingStats := {}
  deriving Inhabited

def recordTiming (timingsRef : IO.Ref TimingState) (label : String) (elapsedMs : Nat) : IO Unit := do
  timingsRef.modify fun s =>
    let existing := s.stats.get? label
    let prev := existing.getD {}
    let next : TimingStats := {
      totalMs := prev.totalMs + elapsedMs
      count := prev.count + 1
      maxMs := max prev.maxMs elapsedMs
    }
    let order := if existing.isSome then s.order else s.order.push label
    { order := order, stats := s.stats.insert label next }

def withTiming (timingsRef : IO.Ref TimingState) (label : String) (action : IO a) : IO a := do
  let start ← IO.monoMsNow
  try
    let out ← action
    let stop ← IO.monoMsNow
    recordTiming timingsRef label (stop - start)
    pure out
  catch e =>
    let stop ← IO.monoMsNow
    recordTiming timingsRef label (stop - start)
    throw e

def printTimingSummary (timingsRef : IO.Ref TimingState) : IO Unit := do
  let timings ← timingsRef.get
  IO.println "<TIMING_SUMMARY>"
  let mut totalMeasured : Nat := 0
  for label in timings.order do
    if let some stats := timings.stats.get? label then
      let avg := if stats.count == 0 then 0 else stats.totalMs / stats.count
      totalMeasured := totalMeasured + stats.totalMs
      IO.println s!"{label}: total={stats.totalMs}ms count={stats.count} avg={avg}ms max={stats.maxMs}ms"
  IO.println s!"TOTAL_MEASURED: {totalMeasured}ms"
  IO.println "</TIMING_SUMMARY>"
