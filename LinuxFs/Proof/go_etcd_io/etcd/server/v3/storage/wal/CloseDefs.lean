/-
What `closeAll` (S/wal.go:1187-1199) closes: `wal.rcFile rc`, an `io.ReadCloser` that
`openWALFiles` collects (`rcs`): a `*fileutil.LockedFile` (write mode; its `Close` is the embedded
`*os.File`'s) or an `*os.File` (read mode), with the file and its fd whole. W5 of
`notes/wal-fsext-plan.md`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs

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

/-- See the file header. -/
def wal.rcFile (rc : GoInterface) : IProp GF :=
  iprop(∃ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
    (⌜rc = interface.mkOk (go.GoType.PointerType os.File.ty) #f⌝ ∨
      ∃ lf : Loc, ⌜rc = interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty) #lf⌝ ∗
        fileutil.lockedFile lf f) ∗
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d)

end defs

end EtcdGrove
end Perennial
