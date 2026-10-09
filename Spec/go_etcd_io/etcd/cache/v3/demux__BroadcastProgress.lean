/-
`demux.BroadcastProgress()`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.BroadcastProgress()`: a progress notification at `maxRev` to every active watcher (the
enqueue's result is ignored, the watchers' next revisions are unchanged); the delivery
invariant is kept (a notification at `maxRev` is above everything sent and below everything
still owed). -/
abbrev demux.BroadcastProgress.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap C ∗ demuxHandle d γd cap C }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"BroadcastProgress")) (Val #()))
  {{ RET #(); demuxHandle d γd cap C }}

end spec

end EtcdGrove
end Perennial
