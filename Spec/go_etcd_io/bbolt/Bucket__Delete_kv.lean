/-
`Bucket.Delete_kv` (bbolt). `b.Delete(key)` in the write transaction.
A corollary of bbolt's proved `Bucket.Delete` (`Spec/go_etcd_io/bbolt/Bucket__Delete.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Bucket__Delete_kv.lean` (stage S1 of
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

/-- `b.Delete(key)` in the write transaction: the entry removed (if present). The key is the
caller's slice, or one of the transaction's own (`txBytes tx γ`: a key a cursor or a range of the
same transaction returned, as mvcc's compaction job deletes `keys[i]`; the backend-compaction
stage, review round 1, F3, the user's decision 2026-10-28): bbolt's `Delete` only reads the key.
`own` says which: the caller's slice comes back as it was given. -/
abbrev bbolt.Bucket.Delete_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData) (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool),
  G n = g → S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g ∗
      (if own then key ↦*{dk} kb else backend.txBytes tx γ key kb) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Delete")) (Val #key))
  {{ RET #GoInterface.nil; ownWTxG tx γ D (S.insert n (m.delete kb)) G ∗
      (if own then key ↦*{dk} kb else backend.txBytes tx γ key kb) }}

end spec

end EtcdGrove
end Perennial
