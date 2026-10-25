/-
`kv.setPrevRev(currRev)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart); see `InvOrdering.lean`.
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

/-- `kv.setPrevRev(currRev)`: under `kv.revMu.Lock()`, sets `kv.prevRev = currRev` if
`currRev > kv.prevRev`, preserving the invariant `□ R prev`. -/
abbrev kvOrdering.setPrevRev.spec : Prop :=
  ∀ (kvp : Loc) (currRev : w64) (R : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      kvOrderingHandle kvp R ∗ □ R currRev }}
    (App (Val (kvp @!! go.GoType.PointerType kvOrdering.ty @!! go!"setPrevRev")) (Val #currRev))
  {{ RET #(); kvOrderingHandle kvp R }}

end spec

end ordering
end EtcdGrove
end Perennial
