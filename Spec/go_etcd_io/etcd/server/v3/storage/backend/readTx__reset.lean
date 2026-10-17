/-
`readTx.reset` (the backend, `read_tx.go`). `rt.reset(lg)`: the read buffer reset, and its `sharedBoltTx` reset (`sharedBoltTx.reset`; changed by etcd#22215).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadSide

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

/-- `rt.reset(lg)`: the read buffer reset, and its `sharedBoltTx` `st` reset
(`sharedBoltTx.reset`: the interval's bbolt read transaction, if any, rolled back by a goroutine
once its readers are done; a new empty buckets map, no bbolt transaction, a new `WaitGroup`). -/
abbrev backend.readTx.reset.spec : Prop :=
  ∀ (γ : BNames) (rt st : Loc) (R : RBuf) (cm : GoMap) (tx wg lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      ownRB (rbufOf (baseOf rt)) R ∗ rstOf (baseOf rt) ↦□ stIf st ∗ rbktOf st ↦ cm ∗
      rtxOf st ↦ tx ∗ rwgOf st ↦ wg ∗ (rollbackRes γ tx wg ∨ ⌜tx = Loc.null⌝) }}
    (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"reset")) (Val #lg))
  {{ (cm' : GoMap) (wg' : Loc), RET #(); ownRB (rbufOf (baseOf rt)) R.reset ∗
      rbktOf st ↦ cm' ∗ cm' ↦$ (∅ : GMap w64 Loc) ∗ rtxOf st ↦ Loc.null ∗
      rwgOf st ↦ wg' ∗ wg' ↦ (zero_val sync.WaitGroup) }}

end spec

end EtcdGrove
end Perennial
