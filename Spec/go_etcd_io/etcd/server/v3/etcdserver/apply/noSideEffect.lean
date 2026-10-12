/-
`apply.noSideEffect` (apply.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

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

/-- **`noSideEffect(r)`**: whether `r` is a range, a user or role get or the auth status
(`noSideEffect rq`). -/
abbrev apply.noSideEffect.spec : Prop :=
  ∀ (p : Loc) (rq : IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.internalRaftRequestIs p rq }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = apply.noSideEffect rq⌝ }}

end spec

end EtcdGrove
end Perennial
