/-
`fbr.FileInfo()` (filereader.go): the file info `NewFileBufReader` kept. Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/FileBufReader__FileInfo.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.bufio.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.FileInfo.spec : Prop :=
  ∀ (fbr b : Loc) (fi err : GoInterface) (dq : DFrac),
  {{ (fbr ↦{dq} go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err : IProp GF) }}
    (App (Val (fbr @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.ty @!! go!"FileInfo")) (Val #()))
  {{ RET #fi; fbr ↦{dq} go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err }}

end spec

end EtcdGrove
end Perennial
