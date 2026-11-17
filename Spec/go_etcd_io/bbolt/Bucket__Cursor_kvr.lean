/-
`Bucket.Cursor_kvr` (bbolt). `b.Cursor()` in a read transaction.
A corollary of bbolt's proved `Bucket.Cursor` (`Spec/go_etcd_io/bbolt/Bucket__Cursor.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Bucket__Cursor_kvr.lean` (stage S1 of
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

/-- `b.Cursor()` in a read transaction (any fraction): a cursor over the bucket's entries in the
snapshot, not positioned. -/
abbrev bbolt.Bucket.Cursor_kvr.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data) (b : Loc) (n : GoString) (m : backend.BktData),
  D.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ wBkt tx γ b n 0 ∗ txLive tx γ q (bbolt.TxView.ro D) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ownCur tx γ c (bbolt.TxView.ro D) (backend.bktEnts m) none ∗ txLive tx γ q (bbolt.TxView.ro D) }}

end spec

end EtcdGrove
end Perennial
