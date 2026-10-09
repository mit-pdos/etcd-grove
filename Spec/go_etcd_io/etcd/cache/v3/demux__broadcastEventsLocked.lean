/-
`demux.broadcastEventsLocked(events)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.broadcastEventsLocked(events)`, under the write lock, for the (sorted, non-empty) events
of a response whose batches are the stream's last ones, from `k` on: each active watcher with
next revision `n` behind the response (`n ≠ 0`, `n < firstRev`) becomes lagging; otherwise it
is sent `events[sendStart:]` (from the first event at or above `n`, a batch boundary; all of
them if `n = 0`) unless that is empty, and then becomes lagging if the send failed, or has
next revision `lastRev + 1`. Afterwards every active watcher is up to date with the whole
stream. -/
abbrev demux.broadcastEventsLocked.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (c : DemuxCore) (k : Nat)
    (regs : GMap Loc RegInfo) (views : GMap Loc View) (evSl : GoSlice) (evs : List EvModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      demuxLocked d γd cap C c k regs views ∗ eventsAt evSl evs ∗
      ⌜DemuxInv cap c ∧ evs ≠ [] ∧ EvRevSorted evs ∧
        c.stream = c.stream.take k ++ splitBatches evs⌝ }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"broadcastEventsLocked")) (Val #evSl))
  {{ RET #(); ∃ views', demuxLocked d γd cap C c c.stream.length regs views' }}

end spec

end EtcdGrove
end Perennial
