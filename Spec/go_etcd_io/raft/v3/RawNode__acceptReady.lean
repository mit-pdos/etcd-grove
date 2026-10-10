/-
`RawNode.acceptReady` (`rawnode.go:405`), Lean-first (2026-10-10): the second half of
`RawNode.Ready`, which `node.go`'s `run` calls after handing the `Ready` to the application.

Lean notes: as `RawNode.Ready.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.acceptReady(rd)`, for the `Ready` `readyWithoutAccept` returned, with nothing in
between (`ownRawNodeReady`): the node's new state as after `RawNode.Ready` -- `delivered`
grows by `ce`, `unpersisted` is `es`, the local messages for `Advance` are queued
(`steps`, opaque) -- and the right to append `es` to the node's storage
(`appendRight`). `acceptReady` does not read `rd.Messages`, which the application may
already hold (`ms`, what `readyWithoutAccept` handed out there, is only an index of
`ownRawNodeReady`, since 2026-10-10). -/
abbrev RawNode.acceptReady.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List raftpb.Entry) (ms : List raftpb.Message),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNodeReady γ rn id rs rd ce es ms }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"acceptReady")) (Val #rd))
  {{ (steps : List Pending), RET #();
      "Hrn" ∷ ownRawNode γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps } ∗
      "Happ" ∷ appendRight rs.storage es }}

end spec

end EtcdGrove
end Perennial
