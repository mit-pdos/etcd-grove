/-
`schema.ReadConsistentIndex(tx)`. Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
import EtcdGrove.Server.InvCindex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `ReadConsistentIndex(tx)`: `UnsafeReadConsistentIndex` between `tx.RLock()` and
`tx.RUnlock()`. -/
abbrev schema.ReadConsistentIndex.spec : Prop :=
  ∀ (rt : GoInterfaceOk) (E : CoPset) (View : MetaCI → IProp GF),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ metaReadTx rt E View) -∗
    readCIAU E View (fun m => Φ (PairV #m.1 #m.2)) -∗
    WP (App (Val (@! schema.ReadConsistentIndex)) (Val #(GoInterface.ok rt))) {{ Φ }}

end spec

end EtcdGrove
end Perennial
