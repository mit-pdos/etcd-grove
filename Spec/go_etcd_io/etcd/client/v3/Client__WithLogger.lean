/-
`c.WithLogger(lg)` (`client/v3/client.go`; PR etcd#22658): overrides the client's logger under
`isClientLogger c` when `lg ≠ null`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClient

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

/-- `c.WithLogger(lg)` on a client with `isClientLogger c` and a non-nil `lg` stores `lg` into
`c.lg` (preserving `isClientLogger c`) and returns `c`. -/
abbrev Client.WithLogger.spec : Prop :=
  ∀ (cl lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClientLogger cl ∗ ⌜lg ≠ null⌝ }}
    (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"WithLogger"))
      (Val #lg))
  {{ (ret : Loc), RET #ret; ⌜ret = cl⌝ ∗ isClientLogger cl }}

end spec

end EtcdGrove
end Perennial
