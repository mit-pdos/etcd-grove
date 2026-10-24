/-
`s.sendMergedSnap(merged)` (`server.go`): the merged snapshot sent through the transport, the
in-flight count held until the send ends. Lean-first (no Rocq counterpart); D22 S-h, 2026-10-20
(`notes/decisions.md`, "D22 S-h carried out"); the vocabulary is `InvSnapSend.lean`. (A
`True`-postcondition axiom until D19p, 2026-10-18, which removed it as false.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.sendMergedSnap(mg)`, by a goroutine with `GoAttach`'s resources (`srvGoRes`, the logger's
reader slot), of a merged message `mg` of the raft message `ml` and the reader `rc`
(`mergedMsg`) with the network's snapshot bundle (`netSnapBundle`: the message's protocol facts,
the reader's streams, the image's certificate), given the server's started transport `tr`
(`netTransport`, the raft wrapper's `transport` field), `s.inflightSnapshots`'s invariant
(`srvInflight`), `s.stopping` and the member id: `inflightSnapshots.Add(1)`, the transport's
`SendSnapshot(mg)` (which takes the bundle), and a goroutine through `GoAttach` that waits for the
send's end (`CloseNotify()`) or the server's stop and, on a successful send, for
`releaseDelayAfterSnapshot` (`time.After`) or the stop, then `inflightSnapshots.Add(-1)`; the
log lines in between. -/
abbrev EtcdServer.sendMergedSnap.spec : Prop :=
  ∀ (s mg ml : Loc) (rc : GoInterface) (lg : Loc) (id : w64) (stg : Loc) (tr : GoInterface)
    (γn : NetNames GF) (S : IProp GF) (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvGoRes s ∗ srvLgReader s ∗ srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
      srvMemberIDAddr s ↦□ id ∗ srvInflight s ∗ srvStoppingAddr s ↦□ stg ∗ stopChan stg ∗
      rnTransportAddr (srvRAddr s) ↦□ tr ∗ netTransport γn lid tr S ∗
      mergedMsg mg ml rc ∗ netSnapBundle γn.N ml rc }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"sendMergedSnap")) (Val #mg))
  {{ RET #(); srvGoRes s ∗ srvLgReader s }}

end spec

end EtcdGrove
end Perennial
