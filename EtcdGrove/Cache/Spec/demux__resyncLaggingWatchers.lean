/-
`demux.resyncLaggingWatchers()`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
import EtcdGrove.Cache.InvDemux

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

/-- `d.resyncLaggingWatchers()` (under the write lock, by the resync loop): every lagging
watcher is compacted at its next revision `n` if `n < minRev`; otherwise it is resent the
history from `n` on, and becomes active (next revision one above the last batch resent, or
`maxRev + 1` after a progress notification) or, if a send failed, stays lagging at the batch
it failed on (`ResyncStep`, `ResyncOutcome`). The states are the lock's at the time; the
delivery invariant is kept. -/
abbrev demux.resyncLaggingWatchers.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap ∗ demuxHandle d γd cap }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"resyncLaggingWatchers")) (Val #()))
  {{ RET #(); demuxHandle d γd cap ∗
      ⌜∃ (c : DemuxCore) (views views' : GMap Loc View),
        DemuxInv cap c ∧ ResyncStep c views views'⌝ }}

end spec

end EtcdGrove
end Perennial
