/-
`(*clientv3.keepAlive).close()` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
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

/-- `ka.close()` on a keep-alive (`kaOwn`, at some registry `γr`: the right to close its `donec`
and each channel's token): closes `donec` and every channel. -/
abbrev keepAlive.close.spec : Prop :=
  ∀ (γr : GName) (ka : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kaOwn γr ka }}
    (App (Val (ka @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.keepAlive.ty @!! go!"close"))
      (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
