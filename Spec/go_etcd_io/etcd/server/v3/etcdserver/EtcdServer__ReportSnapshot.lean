/-
`(*EtcdServer).ReportSnapshot` (`server.go`): `s.r.ReportSnapshot(id, status)`, raft's. Lean-first (no Rocq counterpart); D21 stage M2
(2026-10-19): the inbound path from the transport (`rafthttp.Raft`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.ReportSnapshot(x, st)`** returns (raft's `node.ReportSnapshot`). (restart3 A1, 2026-11-15) Over
what the call reads, the raft wrapper's node and its inbound methods (`rnStepIfc`), so that the apply
thread can report a dropped merged snapshot (`applyAll`'s merge, D-A0-6); until then over the whole
`srvProcOk γn s id γd`, which contains them (`NetBridge`'s caller). -/
abbrev EtcdServer.ReportSnapshot.spec : Prop :=
  ∀ (γ : RNNames GF) (s : Loc) (x : w64) (st : SnapshotStatus),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      rnNodeAddr (srvRAddr s) ↦□ rnNodeIface γ ∗ rnStepIfc γ (rnNodeIface γ) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ReportSnapshot")) (Val #x))
      (Val #st))
  {{ RET #(); True }}
end spec

end EtcdGrove
end Perennial
