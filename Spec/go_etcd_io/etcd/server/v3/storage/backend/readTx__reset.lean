/-
`readTx.reset` (the backend, `read_tx.go`). `rt.reset()`: the read buffer reset, a new empty buckets map, no bbolt transaction, a new `WaitGroup`.
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `rt.reset()`: the read buffer reset, a new empty buckets map, no bbolt transaction, a new `WaitGroup`. -/
abbrev backend.readTx.reset.spec : Prop :=
  ∀ (rt : Loc) (R : RBuf) (cm : GoMap) (tx wg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      ownRB (rbufOf (baseOf rt)) R ∗ rbktOf (baseOf rt) ↦ cm ∗ rtxOf (baseOf rt) ↦ tx ∗
      rwgOf (baseOf rt) ↦ wg }}
    (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"reset")) (Val #()))
  {{ (cm' : GoMap) (wg' : Loc), RET #(); ownRB (rbufOf (baseOf rt)) R.reset ∗
      rbktOf (baseOf rt) ↦ cm' ∗ cm' ↦$ (∅ : GMap w64 Loc) ∗ rtxOf (baseOf rt) ↦ Loc.null ∗
      rwgOf (baseOf rt) ↦ wg' ∗ wg' ↦ (zero_val sync.WaitGroup) }}

end spec

end EtcdGrove
end Perennial
