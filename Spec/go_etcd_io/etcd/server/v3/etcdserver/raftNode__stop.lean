/-
`(*raftNode).stop()` (raft.go): stops the loop and waits for `done`.
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

/-- `r.stop()`, from any goroutine, with the right to stop the transport (`E.ST`, which it sends on
`stopped` to the loop's `onStop`; D43 M5c): returns once `done` is closed. -/
abbrev raftNode.stop.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      E.ST }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
