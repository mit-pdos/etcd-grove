/-
`newSnapshotSender(tr, picker, to, status)` (`snapshot_sender.go`, untranslated; rafthttp stage 6b):
the trust boundary (D34, the snapshot stream an axiom at its own functions). Lean-first.
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

/-- **`newSnapshotSender(tr, picker, to, status)`** of a started transport's fields, a picker of
`to`'s URLs and a peer status: a snapshot sender to `to` and the right to stop it. -/
abbrev rafthttp.newSnapshotSender.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (pk : Loc) (pid : w64)
    (ps : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ trFixed Rh t lid γd R ∗ pickerOk pk (peerURL Rh pid) ∗ peerStatusOk ps }}
    (App (App (App (App (Val (@! rafthttp.newSnapshotSender)) (Val #t)) (Val #pk)) (Val #pid))
      (Val #ps))
  {{ (s : Loc), RET #s; snapSenderOk Rh pid s ∗ snapSenderStop s }}

end spec

end EtcdGrove
end Perennial
