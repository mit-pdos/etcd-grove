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

end Fs
end Perennial
