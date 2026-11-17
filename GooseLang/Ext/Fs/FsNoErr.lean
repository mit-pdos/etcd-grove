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

/-- The steps of the semantics satisfy `NoIoErr` and `NoMapLockErr` on every file. -/
def FsNoErr [ExtSemantics fsExt] : Prop :=
  ∃ Sio : IoSet, (∀ st i, Sio.ino st i) ∧ FsStepSat (NoIoErr Sio) ∧ FsStepSat (NoMapLockErr Sio)

end Fs
end Perennial
