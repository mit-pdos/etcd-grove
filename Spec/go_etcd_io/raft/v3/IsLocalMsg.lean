/- Lean-first (no Rocq counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `IsLocalMsg(msgt)`, a lookup in the table `isLocalMsg` (`util.go`). Only that it
returns is specified (see `isMsgInArray.spec`). -/
abbrev IsLocalMsg.spec : Prop :=
  ∀ (t : w32),
  0 ≤ sint.Z t →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions IsLocalMsg [])) (Val #t))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
