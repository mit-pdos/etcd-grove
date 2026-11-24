/-
What `closeAll` (S/wal.go:1187-1199) closes: `wal.rcFile rc`, an `io.ReadCloser` that
`openWALFiles` collects (`rcs`): a `*fileutil.LockedFile` (write mode; its `Close` is the embedded
`*os.File`'s) or an `*os.File` (read mode), with the file and its fd whole, its name short enough that `Close`'s message is at most
`wal.closeMsgMax` bytes. W5 of
`notes/wal-fsext-plan.md`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.LockLemmas
public import Spec.os.File__CloseLe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The longest message `closeAll` collects** of a `Close` error (2026-11-24, fmt stage 1): what
`strings.Join` of a fully owned slice of such messages with `", "` needs (`maxAddr * (B + 2) ≤
joinMax`, `strings.Join_owned_bounded_of`). A file of a name of at most `wal.closeMsgMax - 72` bytes
(`os.closeErrMax`) qualifies: a WAL segment's path, a directory that fits (`DirFits`) and a name of at
most 255 bytes. -/
def wal.closeMsgMax : Nat := 2 ^ 14 - 2

/-- See the file header. -/
def wal.rcFile (rc : GoInterface) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
    (⌜rc = interface.mkOk (go.GoType.PointerType os.File.ty) #f⌝ ∨
      ∃ lf : Loc, ⌜rc = interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf⌝ ∗
        fileutil.lockedFile lf f) ∗
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ fdLocks fd d ∗
    ⌜os.closeErrMax name ≤ wal.closeMsgMax⌝)

/-- **A file `openWALFiles` opened, closable again** (the closer's precondition, per reader): the reader
`fr` a `*fileReader` over the `*os.File` `f`, the file and its fd whole (any name and fd state), in write
mode the lock `lf`'s `lockedFile` of `f`; the name short enough for `closeAll` (`wal.closeMsgMax`). -/
def wal.walClosable (write : Bool) (fr : GoInterfaceOk) (lf : Loc) : IProp GF :=
  iprop(∃ (f rl : Loc) (fd : w64) (nm : GoString) (fl : OsFd),
    ⌜GoInterface.ok fr = interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl⌝ ∗
    rl ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f ∗
    os.ownFile f fd nm (DFrac.own 1) ∗ osFd fd (DFrac.own 1) fl ∗ fdLocks fd fl ∗
    (if write then fileutil.lockedFile lf f else iprop(True)) ∗ ⌜os.closeErrMax nm ≤ wal.closeMsgMax⌝)

/-- **The closer `openWALFiles` returns** (`func() error { return closeAll(lg, rcs...) }`, S/wal.go:494):
not nil, and its call closes the files of the readers `frs` (locks `lfs`), returning some error. -/
def wal.walCloser (write : Bool) (frs : List GoInterfaceOk) (lfs : List Loc) (cl : GoFunc) : IProp GF :=
  iprop(⌜cl ≠ func.nil⌝ ∗
    □ {{ [∗list] m ↦ fr ∈ frs, wal.walClosable write fr (lfs.getD m null) }}
        (App (Val #cl) (Val #()))
      {{ (err : GoInterface), RET #err; True }})

end defs

end EtcdGrove
end Perennial
