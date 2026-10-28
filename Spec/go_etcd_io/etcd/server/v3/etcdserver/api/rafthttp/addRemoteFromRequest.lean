/-
`addRemoteFromRequest(tr, r)` (`util.go`; rafthttp stage 6d): the handlers' `AddRemote` of a
request's sender. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Pipe

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

/-- **`addRemoteFromRequest(tr, r)`** of a request from another member than `lid`
(`fromOkAt`), the transporter's `AddRemote` returning for such a member and its peer URLs (D22
J-T, W8: the request's `X-PeerURLs`, split at `,`): it returns. -/
abbrev rafthttp.addRemoteFromRequest.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid : w64) (ti : GoInterfaceOk) (r : Loc) (R : http.HReq)
    (rd : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      http.reqAt r R rd ∗ ⌜fromOkAt Rh lid R.hdr⌝ ∗
      □ (∀ (pid : w64) (sl : GoSlice) (us : List GoString),
        {{ sl ↦* us ∗ ⌜Rh.member pid ∧ pid ≠ lid ∧ peerURLsOk Rh pid us⌝ }}
          (App (App (Val #(methods ti.ty go!"AddRemote" ti.v)) (Val #pid)) (Val #sl))
        {{ RET #(); True }}) }}
    (App (App (Val (@! rafthttp.addRemoteFromRequest)) (Val #(GoInterface.ok ti))) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
