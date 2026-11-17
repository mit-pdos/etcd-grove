/-
`Cursor.Seek_kv` (bbolt). `c.Seek(key)`.
A corollary of bbolt's proved `Cursor.Seek` (`Spec/go_etcd_io/bbolt/Cursor__Seek.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Cursor__Seek_kv.lean` (stage S1 of
`notes/bbolt-integration-plan.md`, 2026-11-17; until then an axiom, the backend's trust boundary).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a
key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.Seek(key)` (with the transaction at the cursor's view, any fraction): the first entry whose
key is not below `key` (nil, nil past the end). -/
abbrev bbolt.Cursor.Seek_kv.spec : Prop :=
  ∀ (tx c : Loc) (γ : DBNames) (T : bbolt.TxView) (es : List Ent) (pos : Option Nat) (q : Qp)
    (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownCur tx γ c T es pos ∗ txLive tx γ q T ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Seek")) (Val #key))
  {{ (k v : GoSlice), RET (PairV #k #v); ownCur tx γ c T es (some (backend.seekIdx es kb)) ∗
      txLive tx γ q T ∗ key ↦*{dk} kb ∗ backend.curAt tx γ es (backend.seekIdx es kb) k v }}

end spec

end EtcdGrove
end Perennial
