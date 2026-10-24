/-
`startPeer(t, urls, peerID, fs)` (`peer.go`; rafthttp stage 6b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
/-- **`startPeer(t, urls, peerID, fs)`** on a started transport of the member `lid` (`trFixed`), with
`peerID`'s URLs (non-empty, its own: `peerURL`), follower stats and eight of the transport's `Raft`
resources (the peer's two receiving goroutines' `Process` calls, its two stream writers' and its
pipeline's four goroutines'): a started peer (`peerOk`) and the right to stop it. -/
abbrev rafthttp.startPeer.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (urls : GoSlice)
    (uvs : List net.url.URL) (pid : w64) (fs : Loc),
  uvs ≠ [] → (∀ u ∈ uvs, peerURL Rh pid u) → fs ≠ null → Rh.member lid → lid ≠ pid → Rh.member pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trFixed Rh t lid γd R ∗ urls ↦*□ uvs ∗ [∗list] _x ∈ List.replicate 8 (), R }}
    (App (App (App (App (Val (@! rafthttp.startPeer)) (Val #t)) (Val #urls)) (Val #pid)) (Val #fs))
  {{ (p : Loc), RET #p; peerOk Rh lid pid γd R p ∗ peerStop Rh pid R p }}

end spec

end EtcdGrove
end Perennial
