/-
`(*rafthttp.Transport).Start()` (`transport.go`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an
axiom at the trust boundary since unit N4 (2026-10-17, D14e), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`t.Start()`** on a transport `t` the caller owns whole (`NewServer`'s literal), its logger
and stats set, for member `tv.ID` of the network `γn` (D21 M2, 2026-10-19): given the member's slot
(`netSlot`), its `Raft` (`tv.Raft`: `netRaftOk`, the calls the transport makes into it) and
`netProcSlots` copies of the resource `R` those calls borrow, an error, or the transport live
(`transportLive γn t`: `AddRemote`/`AddPeer` take it), which the caller gives up for
`transportStarted γn t` (`Send`, `Stop`, `ActiveSince`).

What the axiom asserts of the Go code (`transport.go`, `peer.go`, `stream.go`, `pipeline.go`,
`http.go` at the etcd pin), besides `Start`'s own steps (the two round trippers from the TLS info,
an error returned e.g. for an unreadable certificate; the two maps and probers; no goroutine):
* the transport's goroutines and handlers call `tv.Raft` only as `netRaftOk` admits: `Process`
  with a fresh copy (unmarshalled: `netRecv`) of a message some member's started transport was
  given by `Send` for `tv.ID` (`Send` routes by `To` to the peer added for it, which posts to that
  peer's URLs, served by the transport holding `To`'s slot: `AddPeer`'s directory premise), with
  that message's bundle; each sent message possibly lost (writers drop on error or a full buffer,
  reporting `ReportUnreachable`), never retried, so delivered at most once if `once`; the reports
  and `IsIDRemoved` at any time; at most `netProcSlots` calls at once, each borrowing an `R`
  (physically: each is a goroutine with its own stack);
* nothing is sent on `ErrorC`: rafthttp reports only `errMemberRemoved` there, on a `403`, which no
  member answers -- none is removed (static membership) and no message reaches the wrong member
  (`issues/etcd-rafthttp-misaddressed-403-member-removed.md`, excluded by the directory).
`Send` after `Stop` finds no peer and returns; `AddPeer` after `Stop` panics, hence the exclusive
`transportLive`, given up for `Stop`. -/
abbrev rafthttp.Transport.Start.spec : Prop :=
  ∀ (t : Loc) (tv : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport)
    (γn : NetNames GF) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      t ↦ tv ∗
      ⌜tv.Logger' ≠ null ∧ tv.ServerStats' ≠ null ∧ tv.LeaderStats' ≠ null⌝ ∗
      netSlot γn tv.ID' ∗ □ netRaftOk γn tv.ID' R tv.Raft' ∗
      [∗list] _x ∈ List.replicate netProcSlots (), R }}
    (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Start")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ transportLive γn t ∗ (transportLive γn t -∗ transportStarted γn t) }}

end spec

end EtcdGrove
end Perennial
