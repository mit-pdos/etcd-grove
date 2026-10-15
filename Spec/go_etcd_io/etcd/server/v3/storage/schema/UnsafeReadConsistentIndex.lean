/-
`schema.UnsafeReadConsistentIndex(tx)`. Lean-first (no Rocq counterpart); see
`InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `UnsafeReadConsistentIndex(tx)` reads the index from `tx`'s view and, if it is not 0
(absent), the term (`readCIAUA`: two linearizable reads, each non-zero value decoded under the
reader's `Acc` of what it read; 2026-10-13: for the batch transaction's reads, whose slices are
valid under its lock), returning both. -/
abbrev schema.UnsafeReadConsistentIndex.spec : Prop :=
  ∀ (r : GoInterfaceOk) (E : CoPset) (View Acc : MetaCI → IProp GF),
  ⊢ ∀ Φ : val → IProp GF,
    (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ metaReader r E View Acc) -∗
    readCIAUA E View Acc (fun m => Φ (PairV #m.1 #m.2)) -∗
    WP (App (Val (@! schema.UnsafeReadConsistentIndex)) (Val #(GoInterface.ok r))) {{ Φ }}

end spec

end EtcdGrove
end Perennial
