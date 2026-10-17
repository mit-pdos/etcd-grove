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
and stats set: an error, or the transport live (`transportLive t`: `AddRemote`/`AddPeer` take it),
which the caller gives up for `transportStarted t` (`Send`, `Stop`, `ActiveSince`).

Why it is true of the Go code (`transport.go` at the etcd pin): `Start` makes the two round
trippers from the TLS info (an error returned, e.g. an unreadable certificate), the two maps and
the two probers, and defaults the dial retry frequency; it starts no goroutine. Afterwards the
transport's maps are guarded by its `mu` (`AddRemote`, `AddPeer`, `Send`, `Stop`, `ActiveSince`
take it), so the caller's ownership goes into the transport; the peers' goroutines started later
call into `t.Raft` (`Process`, `ReportUnreachable`, `ReportSnapshot`, `IsIDRemoved`), the named
premise `transportEffectsOk`. `Send` after `Stop` finds no peer and returns; `AddPeer` after
`Stop` panics, hence the exclusive `transportLive`, given up for `Stop`. -/
abbrev rafthttp.Transport.Start.spec : Prop :=
  ∀ (t : Loc) (tv : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      ⌜transportEffectsOk⌝ ∗ t ↦ tv ∗
      ⌜tv.Logger' ≠ null ∧ tv.ServerStats' ≠ null ∧ tv.LeaderStats' ≠ null⌝ }}
    (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Start")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ transportLive t ∗ (transportLive t -∗ transportStarted t) }}

end spec

end EtcdGrove
end Perennial
