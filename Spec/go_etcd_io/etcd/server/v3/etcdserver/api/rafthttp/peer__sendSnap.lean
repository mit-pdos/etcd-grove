/-
`(*peer).sendSnap(m)` (`peer.go`; rafthttp stage 7d, D42). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`p.sendSnap(m)`** of a started peer of `pid` and a merged message for `pid`: its snapshot
sender's `send` runs on a goroutine; it returns. -/
abbrev rafthttp.peer.sendSnap.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF) (p m ml : Loc)
    (rc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerOk Rh lid pid γd R p ∗ snap.msgIs m ml rc ∗ snapBundleTo Rh.γn.N pid ml rc }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.peer.ty @!! go!"sendSnap")) (Val #m))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
