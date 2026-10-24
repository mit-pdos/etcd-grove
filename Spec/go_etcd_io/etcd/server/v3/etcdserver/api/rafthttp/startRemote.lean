/-
`startRemote(tr, urls, id)` (`remote.go`; rafthttp stage 6b). Lean-first.
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

/-- **`startRemote(tr, urls, id)`** on a started transport of the member `lid`, with `id`'s URLs
(non-empty, its own) and four of the transport's `Raft` resources (its pipeline's goroutines'): a
started remote and the right to stop it. -/
abbrev rafthttp.startRemote.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (urls : GoSlice)
    (uvs : List net.url.URL) (pid : w64),
  uvs ≠ [] → (∀ u ∈ uvs, peerURL Rh pid u) → Rh.member lid → lid ≠ pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      trFixed Rh t lid γd R ∗ urls ↦*□ uvs ∗ R ∗ R ∗ R ∗ R }}
    (App (App (App (Val (@! rafthttp.startRemote)) (Val #t)) (Val #urls)) (Val #pid))
  {{ (g : Loc), RET #g; remoteOk Rh lid pid R g ∗ remoteStop Rh pid R g }}

end spec

end EtcdGrove
end Perennial
