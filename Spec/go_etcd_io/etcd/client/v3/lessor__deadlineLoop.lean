/-
`(*clientv3.lessor).deadlineLoop()` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
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

/-- `l.deadlineLoop()` on a lessor (`lessorAt`): every second, under the lock, closes and removes
the keep-alives past their deadline, until `donec` is closed; it returns then (or runs forever). -/
abbrev lessor.deadlineLoop.spec : Prop :=
  ∀ (l : Loc) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l [addr] }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"deadlineLoop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
