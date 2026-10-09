/-
`(*consistentIndex).ConsistentApplyingIndex()`. Lean-first (no Rocq counterpart); see
`InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.ConsistentApplyingIndex()` returns the applying index and term (the apply thread's). -/
abbrev consistentIndex.ConsistentApplyingIndex.spec : Prop :=
  ∀ (ci : Loc) (a t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ ciApplying ci a t }}
    (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentApplyingIndex")) (Val #()))
  {{ RET (PairV #a #t); ciApplying ci a t }}

end spec

end EtcdGrove
end Perennial
