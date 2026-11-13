/-
`(*os.File).Sync()` of a directory's `*os.File` in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`): the model asks the fd's kind
(`FdKind`: a directory's), then `fsync(2)` (the extension's `DirSync`), retried on `EINTR`. The
directory fd holds nothing (`osDirFdS`: blind); a success commits every entry the log had when the
caller knew its length (`osLogLb n`), I1's `osCommitLb n`. It changes no claim, so it is a plain
triple. Proved in `Proof/os/File__SyncS.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.SharedAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Sync.specDirS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (R : Roots) (j : Ino) (ph : DirPhS)
    (n : Nat),
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ os.ownFile (GF := GF) f fd name dqf ∗ osDirFdS fd j ph ∗
      osLogLb n }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osDirFdS fd j ph ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ osCommitLb n) }}

end spec

end EtcdGrove
end Perennial
