/-
`demux.Broadcast(resp)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.Broadcast(resp)`, by the writer, for a response modelled by `r` whose events are in
revision order (etcd's watch stream; `updateStoreLocked` relies on it) and whose revisions are
below `2^63 - 1` (`RespRevsBounded`, the overflow premise): `broadcastCore` says whether it
fails (`minRev = 0`: "not initialized", or `validateRevisions`; nothing changes) and the new
state. Every active watcher is sent its part of the response (or a progress notification), or
becomes lagging; which one depends on its consumer, so it is not stated, but the delivery
invariant is kept. -/
abbrev demux.Broadcast.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap ∗ demuxWriter d γd cap c ∗
      respAt resp r ∗ ⌜EvRevSorted r.events ∧ RespRevsBounded r⌝ }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"Broadcast")) (Val #resp))
  {{ (err : GoInterface), RET #err;
      match broadcastCore cap c r with
      | none => demuxWriter d γd cap c ∗ ⌜∃ e, err = GoInterface.ok e⌝
      | some c' => demuxWriter d γd cap c' ∗ ⌜err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
