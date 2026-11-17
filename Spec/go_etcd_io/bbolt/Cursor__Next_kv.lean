/-
`Cursor.Next_kv` (bbolt). `c.Next()` of a positioned cursor.
A corollary of bbolt's proved `Cursor.Next` (`Spec/go_etcd_io/bbolt/Cursor__Next.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Cursor__Next_kv.lean` (stage S1 of
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

/-- `c.Next()` of a positioned cursor (with the transaction at the cursor's view, any fraction): the
next entry, or nil, nil past the last, where the cursor *stays at the last entry* (Go's `next`:
"it stays there"; S1: bbolt's proved position, until then `min (i + 1) es.length`). -/
abbrev bbolt.Cursor.Next_kv.spec : Prop :=
  ∀ (tx c : Loc) (γ : DBNames) (T : bbolt.TxView) (es : List Ent) (i : Nat) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownCur tx γ c T es (some i) ∗ txLive tx γ q T }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v);
      ownCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
      txLive tx γ q T ∗ backend.curAt tx γ es (i + 1) k v }}

end spec

end EtcdGrove
end Perennial
