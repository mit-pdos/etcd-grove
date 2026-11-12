/-
fs-v2-r7, finding 1: an open(O_TRUNC) racing an in-flight pwrite on the same file (allowed: OpenEffect
has no BusyAt guard). File [1,1] synced; PWriteStart of [2] at 0 (stamp 1); O_TRUNC (stamp 2);
PWriteFinish lands the byte. The page cache is [2] (size 1, byte 1 zero), Linux's serialized
"truncate, then write" result, but no stamp's valAt gives it, so SectorWhole excludes the crash that
keeps the page cache. Check: lake env lean notes/axiom-review/fs-v2-r7/otrunc_race.lean
-/
import GooseLang.Ext.Fs.Premises
open Perennial Fs

def f0 : OsFile := OsFile.ofBytes [1, 1]
def f1 : OsFile := f0.announceWrite 0 [2] 1          -- PWriteStart, stamp 1
def f2 : OsFile := (f1.announceResize 0 2).truncate 0 -- O_TRUNC, stamp 2
def f3 : OsFile := f2.landWrite 0 [2] 1               -- PWriteFinish, 1 byte

example : f3.size = 1 := by decide
example : f3.cache 0 = 2 ∧ f3.cache 1 = 0 := by decide
-- byte 0: stamp 0 -> 1, 1 -> 2, >= 2 -> 0; byte 1: 0 -> 1, 1 -> 1, >= 2 -> 0
example : valAt (f3.cand 0) 0 = 1 ∧ valAt (f3.cand 1) 0 = 1 := by decide
example : valAt (f3.cand 0) 1 = 2 ∧ valAt (f3.cand 1) 1 = 1 := by decide
example : valAt (f3.cand 0) 2 = 0 ∧ valAt (f3.cand 0) 100 = 0 := by decide
-- so for every m, (cache 0, cache 1) = (2, 0) is not (valAt (cand 0) m, valAt (cand 1) m)

/- Finding 5 (b): two disjoint writes in flight on one sector, the later-started one landed first
(allowed: PWriteStart only needs disjoint bytes). Page cache (1, 3); valAt at 0, 1, 2 gives
(1, 1), (2, 1), (2, 3): none. -/
def g1 : OsFile := (f0.announceWrite 0 [2] 1).announceWrite 1 [3] 2
def g2 : OsFile := g1.landWrite 1 [3] 1
example : g2.cache 0 = 1 ∧ g2.cache 1 = 3 := by decide
example : (valAt (g2.cand 0) 0, valAt (g2.cand 1) 0) = (1, 1) ∧
    (valAt (g2.cand 0) 1, valAt (g2.cand 1) 1) = (2, 1) ∧
    (valAt (g2.cand 0) 2, valAt (g2.cand 1) 2) = (2, 3) := by decide
