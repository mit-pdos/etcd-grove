/-
`updateCommittedIndex(ap, rh)` (raft.go): the batch's last index (or the snapshot's) to the
ready handler.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `updateCommittedIndex(ap, rh)` on a batch with no snapshot (its fields read-only), with the
ready handler's resource `R` (2026-10-13, the request path's unit 4c) and the batch's committed
log (2026-10-16, stage R7b): and (2026-10-14, unit C2a) the committed index at least the batch's
last index after (`committedLast`). -/
abbrev updateCommittedIndex.spec : Prop :=
  ∀ (ap rh : Loc) (es : GoSlice) (ceL : List Loc) (A ce : List EntryModel) (R : IProp GF)
    (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      taEntriesAddr ap ↦□ es ∗ es ↦*□ ceL ∗ entriesAt ceL ce ∗
      structFieldRef toApply go!"snapshot" ap ↦□ (null : Loc) ∗ isReadyHandler rh R γr ∗ R ∗
      -- (2026-10-16, stage R7b) the batch committed after `A`, its indices consecutive from the
      -- start index (what the ready handler's `updateCommittedIndex` takes)
      srvRLogLb γr.raft (A ++ ce) ∗ ⌜srvIdxOk γr.raft.ai0 (A ++ ce)⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex)) (Val #ap)) (Val #rh))
  {{ RET #(); R ∗ committedLast γr ce }}

end spec

end EtcdGrove
end Perennial
