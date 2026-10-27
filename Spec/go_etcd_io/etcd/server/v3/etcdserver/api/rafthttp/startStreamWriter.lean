/-
`startStreamWriter` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
`rafthttp/Writer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`startStreamWriter(lg, local, id, status, fs, r)`** of a writer of type `ty` from `lid` to
`pid` (a non-`nil` logger, a peer status, non-`nil` follower stats, a `Raft` whose calls take one
of the resources `Rr`, and one of them for the goroutine): the writer, started, and the right to
stop it. -/
abbrev rafthttp.startStreamWriter.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (lg ps fs : Loc)
    (r : GoInterface) (γd : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      ⌜lg ≠ null⌝ ∗ peerStatusOk ps ∗ ⌜fs ≠ null⌝ ∗ netRaftOk Rh.γn lid γd Rr r ∗ Rr }}
    (App (App (App (App (App (App (Val (@! rafthttp.startStreamWriter)) (Val #lg)) (Val #lid))
      (Val #pid)) (Val #ps)) (Val #fs)) (Val #r))
  {{ (cw : Loc), RET #cw; swFixed Rh ty lid pid Rr cw ∗ swStopRight cw }}

end spec

end EtcdGrove
end Perennial
