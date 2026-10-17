/-
`(*toApply).notifyApplyCompleted()` (raft.go; etcd-io/etcd#22223, `pr-verify/etcd-22223`): the
apply side's completion signal. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `ap.notifyApplyCompleted()`: calls the completion callback if non-nil (with its resource
`P`), then closes the completion channel if non-nil (the right to close it is spent: the channel
is closed exactly once, by this call). -/
abbrev toApply.notifyApplyCompleted.spec : Prop :=
  ∀ (ap : Loc) (f : GoFunc) (acc : GoChan) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      taOnApplyCompletedAddr ap ↦□ f ∗ onApplyOk f P ∗ P ∗
      taApplyCompletedCAddr ap ↦□ acc ∗ applyDoneOk acc }}
    (App (Val (ap @!! go.GoType.PointerType toApply.ty @!! go!"notifyApplyCompleted")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
