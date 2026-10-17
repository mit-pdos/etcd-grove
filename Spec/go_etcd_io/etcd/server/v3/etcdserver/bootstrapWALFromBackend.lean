/-
`bootstrapWALFromBackend(cfg, be)` (`bootstrap.go`, added by etcd-io/etcd#19693 in place of
`bootstrapWALFromSnapshot`; pr-verify, 2026-10-17): a restarting member's WAL, opened at the
backend's position. Lean-first (no Rocq counterpart); see `InvBootWALFromBackend.lean`.

**The code.** `consistentIndex, term := schema.ReadConsistentIndex(be.ReadTx())`; `pos :=
wal.Position{Index: consistentIndex, Term: term}`; `confstate :=
schema.ReadConfStateFromBackend(cfg.Logger, be.ReadTx())`; `openWALFromPosition(cfg, pos)`; the
`bootstrappedWAL` of these (`haveWAL: true`); with `cfg.ForceNewCluster`, the commit index raised
to the consistent index and the uncommitted entries replaced by the conf-change entries (**not
covered: the premise `ForceNewCluster = false`**); a log line.

**The post.** The WAL's position is the backend's (`ciPos m0`: what `ReadConsistentIndex` reads of
the meta keys `m0`), its conf state the backend's (`csRead`: `nil` or owned), its hard state and
entries the WAL's after that position (`EntsAfter`), `haveWAL` set, the logger `cfg.Logger`.
**Nothing relates the hard state's commit index to the position**: `raft.RestartNode` over the
storage built from it needs `pos.Index ≤ Commit` (`RestartOk`, `InvBootWAL.lean`), which the WAL
does not ensure (its last durable `HardState` may predate entries the backend applied:
`restartOk_counterexample`). Before the PR the WAL was opened at its latest snapshot record, below
any commit index it holds.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.openWALFromPosition

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev bootstrapWALFromBackend.spec : Prop :=
  ∀ (cv : go_etcd_io.etcd.server.v3.config.ServerConfig) (be : GoInterface) (m0 : MetaCI),
  cv.ForceNewCluster' = false →
  cv.Logger' ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      bootBackendOk be m0 }}
    (App (App (Val (@! bootstrapWALFromBackend)) (Val #cv)) (Val #be))
  {{ (bw : Loc), RET #bw; ∃ (v : bootstrappedWAL) (hs : HardStateM) (p : List EntryM)
      (mv : snapshotMetadata),
      bw ↦ v ∗ ⌜v.pos' = ciPos m0 ∧ v.haveWAL' = true ∧ v.lg' = cv.Logger'⌝ ∗
      csRead v.confstate' ∗ hsOpt v.st' hs ∗ entsPts v.ents' (DFrac.own 1) p ∗
      ⌜EntsAfter v.pos'.Index' p⌝ ∗ v.meta' ↦ mv }}

end spec

end EtcdGrove
end Perennial
