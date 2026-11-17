/-
`Bucket.Cursor_kvw` (bbolt). `b.Cursor()` in the write transaction.
A corollary of bbolt's proved `Bucket.Cursor` (`Spec/go_etcd_io/bbolt/Bucket__Cursor.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Bucket__Cursor_kvw.lean` (stage S1 of
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

/-- `b.Cursor()` in the write transaction: a cursor over the bucket's entries now, made at the
transaction's view (usable while the view does not change: a `Put` or `Delete` after it makes it
stale, Go's "You must reposition your cursor after mutating data"; until S1 the cursor held the
transaction's ownership instead). The handle must be at the bucket's current generation. -/
abbrev bbolt.Bucket.Cursor_kvw.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData),
  G n = g → S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ownCur tx γ c (wView D S G) (backend.bktEnts m) none ∗ ownWTxG tx γ D S G }}

end spec

end EtcdGrove
end Perennial
