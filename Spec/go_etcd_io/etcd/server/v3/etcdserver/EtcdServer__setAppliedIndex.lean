/-
`(*EtcdServer).setAppliedIndex(v)` (server.go). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.setAppliedIndex(v')`, by the apply thread (the only writer), right after applying the entry
at index `v'`, with mvcc's certificate of the KV log `L` it left (the request path's unit 4b): it
stores `v'` into the atomic `s.appliedIndex` and, at that point, raises the ghost applied index to
`v'` and makes `L` the current applied log. Since 2026-10-14 (unit C2a) the log `L` is deposited
ahead as the log applied through `v' = v + 1` (`srvAppliedPre γr v v' L`, `applied_predeposit`:
before the entry's result goes to its proposer), and the store publishes it. Since 2026-10-17
(etcd-io/etcd#22529) `v'` is any index above `v` (`srvAppliedPre`, `applied_predeposit_gt`): a
leader snapshot's, which `applySnapshot` publishes (`EtcdServer.applySnapshot.publish_ok`). -/
abbrev EtcdServer.setAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v v' : w64) (L : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAppliedInv s E γr ∗ srvAppliedPre γr v v' L ∗ mvcc.idxCert E.γ.idx L }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setAppliedIndex")) (Val #v'))
  {{ RET #(); srvAppliedOwn γr v' ∗ appliedAtLeast γr v' ∗ appliedLogAt γr v' L }}

end spec

end EtcdGrove
end Perennial
