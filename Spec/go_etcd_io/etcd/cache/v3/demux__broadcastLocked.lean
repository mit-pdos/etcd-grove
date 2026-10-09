/-
`demux.broadcastLocked(resp)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.broadcastLocked(resp)`, under the write lock, after `updateStoreLocked` (the state `c`
is the new one, see `BroadcastPre`): every active watcher processed as
`broadcastProgressLocked`/`broadcastEventsLocked` do; afterwards every active watcher is up to
date with the whole stream. -/
abbrev demux.broadcastLocked.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (c : DemuxCore) (k : Nat)
    (regs : GMap Loc RegInfo) (views : GMap Loc View)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      demuxLocked d γd cap C c k regs views ∗ respAt resp r ∗
      ⌜DemuxInv cap c ∧ BroadcastPre c k r⌝ }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"broadcastLocked")) (Val #resp))
  {{ RET #(); ∃ views', demuxLocked d γd cap C c c.stream.length regs views' }}

end spec

end EtcdGrove
end Perennial
