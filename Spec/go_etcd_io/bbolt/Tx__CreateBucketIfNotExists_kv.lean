/-
`Tx.CreateBucketIfNotExists_kv` (bbolt). `tx.CreateBucketIfNotExists(name)`.
A corollary of bbolt's proved `Tx.CreateBucketIfNotExists` (`Spec/go_etcd_io/bbolt/Tx__CreateBucketIfNotExists.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Tx__CreateBucketIfNotExists_kv.lean` (stage S1 of
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

/-- `tx.CreateBucketIfNotExists(name)` (a name of `1..MaxKeySize` bytes): the bucket, empty if
it was absent, and its handle (bbolt copies the name). -/
abbrev bbolt.Tx.CreateBucketIfNotExists_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (name : GoSlice) (n : GoString)
    (dq : DFrac),
  0 < n.length → n.length ≤ backend.maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"CreateBucketIfNotExists")) (Val #name))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err); ⌜err = GoInterface.nil⌝ ∗
      ownWTxG tx γ D (if S.lookup n = none then S.insert n ∅ else S) G ∗ wBkt tx γ b n (G n) ∗
      name ↦*{dq} n }}

end spec

end EtcdGrove
end Perennial
