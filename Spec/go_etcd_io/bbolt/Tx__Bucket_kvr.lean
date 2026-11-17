/-
`Tx.Bucket_kvr` (bbolt). `tx.Bucket(name)` in a read transaction.
A corollary of bbolt's proved `Tx.Bucket` (`Spec/go_etcd_io/bbolt/Tx__Bucket.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Tx__Bucket_kvr.lean` (stage S1 of
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

/-- `tx.Bucket(name)` in a read transaction (any fraction): the snapshot's bucket's handle (at
generation `0`), or nil. -/
abbrev bbolt.Tx.Bucket_kvr.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ q (bbolt.TxView.ro D) ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; txLive tx γ q (bbolt.TxView.ro D) ∗ name ↦*{dq} n ∗
      ((⌜D.lookup n = none ∧ b = Loc.null⌝) ∨
       (∃ m : backend.BktData, ⌜D.lookup n = some m ∧ b ≠ Loc.null⌝ ∗ wBkt tx γ b n 0)) }}

end spec

end EtcdGrove
end Perennial
