/-
Port of `election_proof/spec_needStorageApplyMsg.v` (857d09190).
-/
import EtcdGrove.Raft.InvReadylog

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `needStorageApplyMsg(rd)` (`rawnode.go:368`): `len(rd.CommittedEntries) > 0`. -/
abbrev needStorageApplyMsg.spec : Prop :=
  ∀ (rd : Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions needStorageApplyMsg [])) (Val #rd))
  {{ RET #(decide (0 < sint.Z rd.CommittedEntries'.len)); True }}

end spec

end EtcdGrove
end Perennial
