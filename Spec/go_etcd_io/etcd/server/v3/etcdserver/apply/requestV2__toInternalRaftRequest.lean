/-
`apply.requestV2.toInternalRaftRequest` (`legacy_request.go`, `etcd#22634`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `r_ptr.toInternalRaftRequest(lg)` when `apply.legacyToIRR r = some rq` returns an
`etcdserverpb.InternalRaftRequest` struct value `v` satisfying
`apply.internalRaftRequestValIs v rq` (`legacyClusterVersionIRR` for `/0/version` or
`legacyMemberAttrIRR` for `/0/members/<hex>/attributes`). -/
abbrev apply.requestV2.toInternalRaftRequest.spec : Prop :=
  ∀ (r_ptr : Loc) (r : requestV2) (dq : DFrac) (lg : Loc) (rq : apply.IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      r_ptr ↦{dq} r ∗ ⌜lg ≠ null ∧ apply.legacyToIRR r = some rq⌝ }}
    (App (Val (r_ptr @!! go.GoType.PointerType requestV2.ty @!! go!"toInternalRaftRequest"))
      (Val #lg))
  {{ (v : etcdserverpb.InternalRaftRequest), RET #v;
      r_ptr ↦{dq} r ∗ apply.internalRaftRequestValIs v rq }}

end spec

end EtcdGrove
end Perennial
