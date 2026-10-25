/-
`kv.getPrevRev()` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart); see `InvOrdering.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.InvOrdering

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI go_etcd_io.etcd.client.v3.ordering

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

/-- `kv.getPrevRev()`: reads `kv.prevRev` under `kv.revMu.RLock()`, returning `prev` satisfying `□ R prev`. -/
abbrev kvOrdering.getPrevRev.spec : Prop :=
  ∀ (kvp : Loc) (R : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      kvOrderingHandle kvp R }}
    (App (Val (kvp @!! go.GoType.PointerType kvOrdering.ty @!! go!"getPrevRev")) (Val #()))
  {{ (prev : w64), RET #prev; kvOrderingHandle kvp R ∗ □ R prev }}

end spec

end ordering
end EtcdGrove
end Perennial
