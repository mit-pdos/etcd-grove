/-
**The file system does not fail** (session bbolt-inv): the premises on steps of `NoIoErr` and
`NoMapLockErr` (`Premises.lean`) for an `IoSet` that covers every file, as one proposition of the
semantics, `FsNoErr`. A proof can case on it (classically): when it holds, the error-free specs
apply (`DB.Close_noErr.spec`'s premises, as instances); when it does not, the failure is the
environment's, which a spec may report as `¬ FsNoErr` (bbolt's `DB.Close_own.spec`: the file is
given back, or the file system can fail). A definition only, no assumption. Untrusted.
-/
module

public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- The steps of the semantics satisfy `NoIoErr` and `NoMapLockErr` on every file and every path
(session S3f: the paths too, for `open`'s clause of `NoMapLockErr`). -/
def FsNoErr [ExtSemantics fsExt] : Prop :=
  ∃ Sio : IoSet, (∀ st i, Sio.ino st i) ∧ FsStepSat (NoIoErr Sio) ∧ FsStepSat (NoMapLockErr Sio) ∧
    (∀ p, Sio.path p)

/-- **The premises refute a witness `¬ FsNoErr`** (session S3f): what a client of a spec whose error
arm carries `⌜¬ FsNoErr⌝` (bbolt's `Open.spec`, `DB.Close.spec`) uses to rule the error out. -/
theorem fsNoErr_of [ExtSemantics fsExt] (Sio : IoSet) [h1 : FsStepSat (NoIoErr Sio)]
    [h2 : FsStepSat (NoMapLockErr Sio)] (hi : ∀ st i, Sio.ino st i) (hp : ∀ p, Sio.path p) :
    FsNoErr :=
  ⟨Sio, hi, h1, h2, hp⟩

/-- **The file system does not fail on every file and on the paths `Ps`** (wal-fsfix2, 2026-11-20):
`FsNoErr` with the paths narrowed to `Ps` (a call on an inode needs every inode covered; a path call on
`p` also `Ps p`). A spec of a call that cannot fail under the premises reports its error with the
witness `¬ FsNoErrOn Ps` for the paths it names (`FsNoErrIno`: none, an inode's call). A definition
only, no assumption. -/
def FsNoErrOn [ExtSemantics fsExt] (Ps : GoString → Prop) : Prop :=
  ∃ Sio : IoSet, (∀ st i, Sio.ino st i) ∧ FsStepSat (NoIoErr Sio) ∧ FsStepSat (NoMapLockErr Sio) ∧
    (∀ p, Ps p → Sio.path p)

/-- **The file system does not fail on every file** (`FsNoErrOn` of no path): the witness of a call on
an inode (an fsync, a write, a truncate, a lock). -/
abbrev FsNoErrIno [ExtSemantics fsExt] : Prop := FsNoErrOn (fun _ => False)

/-- The premises at `Sio` give `FsNoErrOn Ps` for the paths `Sio` covers. -/
theorem fsNoErrOn_of [ExtSemantics fsExt] (Sio : IoSet) [h1 : FsStepSat (NoIoErr Sio)]
    [h2 : FsStepSat (NoMapLockErr Sio)] (hi : ∀ st i, Sio.ino st i) {Ps : GoString → Prop}
    (hp : ∀ p, Ps p → Sio.path p) : FsNoErrOn Ps :=
  ⟨Sio, hi, h1, h2, hp⟩

/-- `FsNoErrOn` of fewer paths. -/
theorem FsNoErrOn.mono [ExtSemantics fsExt] {Ps Qs : GoString → Prop} (h : FsNoErrOn Ps)
    (hq : ∀ p, Qs p → Ps p) : FsNoErrOn Qs := by
  obtain ⟨Sio, hi, h1, h2, hp⟩ := h
  exact ⟨Sio, hi, h1, h2, fun p hq' => hp p (hq p hq')⟩

/-- `FsNoErr` is `FsNoErrOn` of every path. -/
theorem FsNoErr.on [ExtSemantics fsExt] {Ps : GoString → Prop} (h : FsNoErr) : FsNoErrOn Ps := by
  obtain ⟨Sio, hi, h1, h2, hp⟩ := h
  exact ⟨Sio, hi, h1, h2, fun p _ => hp p⟩

end Fs
end Perennial
