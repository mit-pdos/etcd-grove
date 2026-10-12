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

/-- `updateCommittedIndex(ap, rh)` on a batch with no snapshot. -/
abbrev updateCommittedIndex.spec : Prop :=
  ∀ (ap rh : Loc) (dq : DFrac) (apv : toApply) (ceL : List Loc) (ce : List EntryModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ap ↦{dq} apv ∗ apv.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗
      ⌜apv.snapshot' = null⌝ ∗ isReadyHandler rh }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex)) (Val #ap)) (Val #rh))
  {{ RET #(); ap ↦{dq} apv }}

end spec

end EtcdGrove
end Perennial
