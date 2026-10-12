/-
`apply.needAdminPermission` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`needAdminPermission(r)`**: whether the request changes users or roles, enables or disables auth, or lists users or roles (`needAdminPermission rq`). -/
abbrev apply.needAdminPermission.spec : Prop :=
  ∀ (p : Loc) (rq : IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.internalRaftRequestIs p rq }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.needAdminPermission)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = apply.needAdminPermission rq⌝ }}

end spec

end EtcdGrove
end Perennial
