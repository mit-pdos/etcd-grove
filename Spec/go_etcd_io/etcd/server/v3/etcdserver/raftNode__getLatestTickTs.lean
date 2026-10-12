/-
`(*raftNode).getLatestTickTs()` (raft.go): `latestTickTs`, read under `tickMu`.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.getLatestTickTs()`, with one of `tickMu`'s reader slots (returned): some time. -/
abbrev raftNode.getLatestTickTs.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r mu : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗ rnTickMuAddr r ↦□ mu ∗ sync.ownRWMutex mu (rnTickInv r) }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"getLatestTickTs")) (Val #()))
  {{ (t : time.Time), RET #t; sync.ownRWMutex mu (rnTickInv r) }}

end spec

end EtcdGrove
end Perennial
