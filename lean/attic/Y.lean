import HalfOne.Fast
namespace HalfOne
set_option maxRecDepth 100000
def newc (n M : ℕ) (_ : Unit) : ℕ :=
  let cl := candList n
  let L := (edgeList n).length
  let F := fullMask n
  countPow (fun m => (m &&& F == m) && goodBS cl L m) 0 M
def bench (name : String) (f : Unit → ℕ) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := f ()
  IO.println s!"{name}: {v}"
  let t1 ← IO.monoMsNow
  IO.println s!"   {t1 - t0} ms"
#eval show IO Unit from do
  bench "n=4" (newc 4 6)
  bench "n=5" (newc 5 10)
  bench "n=6" (newc 6 15)
end HalfOne
