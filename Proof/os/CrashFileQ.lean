/-
Crash-aware specs of `os` under a premise `Q` on crashes: the crash invariant of a file whose
`Good` predicate needs the crash's facts (`CrashSeenR`, `GooseLang/Ext/Fs/CrashTok.lean`), not
only what the old generation's resources say of the crash (`FileCrashedR`).

`FileOk Good x` (`CrashFile.lean`) asks that every file a crash may leave of the file `x`, as its
resources describe it, be `Good`. minibolt's `Good` needs more: P1
(`Proof/.../bboltfs/BootP1.lean`) speaks of the crashed state itself (a meta slot of the image
that validates is the durable one, the page cache's or a write in flight's), which `CrashSeenR`
gives, coherent with the resources (`OsCoh`). `FileOkQ Q Good i x` is `FileOk` of the file of
inode `i` with those facts as a further hypothesis, so `FileOk` implies it (`fileOk_Q`). The crash
invariant that uses it is `csInv` (`CrashSt.lean`).
-/
module

public import Proof.os.CrashFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- The change in flight of the file `x` of inode `i`, as its token records it (`pwTok`). -/
def cToks (i : Ino) : CX → List (Nat × TokInfo)
  | (m, bs, some (t, off, data, n)) =>
      [(t, ⟨i, .write off data, n, m, pwAnn data n (cfRange m bs off data.length)⟩)]
  | _ => []

/-- Every file a crash under the premise `Q` may leave of the file `x` of inode `i` is `Good`,
given the crash's facts. -/
def FileOkQ (Q : OsState → OsState → Prop) (Good : Option OsFile → Prop) (i : Ino) (x : CX) : Prop :=
  ∀ f, FileCrashedR (fMeta x) (fRuns x) (some f) →
    CrashSeenR Q i (fMeta x) (fRuns x) (cToks i x) (some f) → Good (some f)

/-- `FileOk` gives `FileOkQ`. -/
theorem fileOk_Q {Q : OsState → OsState → Prop} {Good : Option OsFile → Prop} {i : Ino} {x : CX}
    (h : FileOk Good x) : FileOkQ Q Good i x :=
  fun f hc _ => h f hc

end Perennial
