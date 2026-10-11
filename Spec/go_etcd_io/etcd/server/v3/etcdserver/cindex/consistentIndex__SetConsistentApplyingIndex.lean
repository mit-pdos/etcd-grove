/-
`(*consistentIndex).SetConsistentApplyingIndex(v, term)`. Lean-first (no Rocq counterpart);
see `InvCindex.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.SetConsistentApplyingIndex(v, term)` sets the applying index and term (the apply
thread's). -/
abbrev consistentIndex.SetConsistentApplyingIndex.spec : Prop :=
  ∀ (ci : Loc) (a t v term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ ciApplying ci a t }}
    (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetConsistentApplyingIndex")) (Val #v)) (Val #term))
  {{ RET #(); ciApplying ci v term }}

end spec

end EtcdGrove
end Perennial
