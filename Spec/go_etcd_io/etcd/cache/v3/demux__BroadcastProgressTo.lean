/-
`demux.BroadcastProgressTo(w)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.BroadcastProgressTo(w)`, by `w`'s registrant, under a read lock: a progress notification
at `maxRev` to `w` if it is active; the delivery invariant is kept. -/
abbrev demux.BroadcastProgressTo.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (w : Loc) (γ : WatcherNames)
    (pred : Option (GoString → Bool)) (s : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isDemux d γd cap C ∗ demuxHandle d γd cap C ∗ demuxRegistered γd w γ pred s }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"BroadcastProgressTo")) (Val #w))
  {{ RET #(); demuxHandle d γd cap C ∗ demuxRegistered γd w γ pred s }}

end spec

end EtcdGrove
end Perennial
