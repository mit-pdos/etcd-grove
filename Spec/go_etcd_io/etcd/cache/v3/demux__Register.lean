/-
`demux.Register(w, startingRev)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.Register(w, startingRev)`, for a fresh (`watcherUnique`) open watcher with nothing
sent yet, publishing `demuxPub C pred startingRev`: returns the registration token, with the
start revision `s` resolved against the `maxRev` `M` at the time (`resolveStart`: `0` means
"from now"). From then on the lock delivers to `w` the stream from `s` on (`Delivered`), and
`w` publishes, with every log, its delivery facts and the delivered batches' certificates
(`demuxPub`). -/
abbrev demux.Register.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (startingRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isDemux d γd cap C ∗ demuxHandle d γd cap C ∗
      isWatcher w γ pred (demuxPub C pred startingRev) ∗ watcherOpen γ [] ∗ watcherUnique w }}
    (App (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"Register")) (Val #w)) (Val #startingRev))
  {{ RET #(); demuxHandle d γd cap C ∗
      ∃ (s M : w64), demuxRegistered γd w γ pred s ∗ ⌜s = resolveStart startingRev M⌝ }}

end spec

end EtcdGrove
end Perennial
