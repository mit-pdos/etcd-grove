/-
`(*clientv3.lessor).closeRequireLeader()` (`client/v3/lease.go`; item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.closeRequireLeader()` on a lessor (`lessorAt`): under the lock, for each keep-alive, it
closes some of its channels (those whose contexts ask for a leader) and removes them from its
`chs`, with their contexts from its `ctxs`, keeping the lock invariant; it returns. (The lock
invariant does not pair a channel with its context, `kaCtxOk`: the alignment the fork's fix
restores, a7bd9a16e, `issues/etcd-lease-close-require-leader-ctx-misaligned.md`, is not
stated.) -/
abbrev lessor.closeRequireLeader.spec : Prop :=
  ∀ (l : Loc) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l addr }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"closeRequireLeader")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
