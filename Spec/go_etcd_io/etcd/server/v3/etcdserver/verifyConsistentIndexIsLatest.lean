/-
`verifyConsistentIndexIsLatest(snapshot, cindex)` (`server.go`): the consistent index at least the
snapshot's index, checked under `ETCD_VERIFY`. Lean-first (no Rocq counterpart); D22 J4b
(2026-10-27), translated for `snapshot`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

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

/-- `verifyConsistentIndexIsLatest(sn, cindex)` of a read-only snapshot whose index is at most
`cindex` returns (`verify.Verify`'s check holds, so it does not panic when assertions are on). -/
abbrev verifyConsistentIndexIsLatest.spec : Prop :=
  ∀ (sn : Loc) (sv : SnapshotM) (cindex : w64),
  uint.Z sv.Metadata'.Index' ≤ uint.Z cindex →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ownSnapM sn DFrac.discard sv }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.verifyConsistentIndexIsLatest))
      (Val #sn)) (Val #cindex))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
