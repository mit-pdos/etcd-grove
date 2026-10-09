/-
`demux.Unregister(w)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.Unregister(w)`, by `w`'s registrant: `w` leaves both maps and is stopped. **The delivery
theorem**: the watcher is closed after a log `sent` (with cancel `c`: `none` if this call
stopped it or `purge` did, `some n` if it was compacted at `n`) of which `DeliveredLog`
holds: the events sent are exactly the stream's events from `s` on (up to the view's `n`),
filtered by `pred`, in order, with no gap and no duplicate, and progress notifications are
trustworthy. With `watcher_received_prefix_closed`, so is every prefix the consumer
received. -/
abbrev demux.Unregister.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (s : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isDemux d γd cap C ∗ demuxHandle d γd cap C ∗ demuxRegistered γd w γ pred s }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"Unregister")) (Val #w))
  {{ RET #(); demuxHandle d γd cap C ∗
      ∃ (sent : List RespModel) (c : Option w64),
        watcherClosed γ sent c ∗ ⌜DeliveredLog pred s sent c⌝ }}

end spec

end EtcdGrove
end Perennial
