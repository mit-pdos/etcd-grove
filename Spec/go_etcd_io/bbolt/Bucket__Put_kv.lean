/-
`Bucket.Put_kv` (bbolt). `b.Put(key, value)` in the write transaction, over the backend's vocabulary
(`InvBbolt.lean`): a corollary of bbolt's proved `Bucket.Put` (`Spec/go_etcd_io/bbolt/Bucket__Put.lean`),
proof `Proof/go_etcd_io/bbolt/Bucket__Put_kv.lean`. Stage S1b of `notes/bbolt-integration-plan.md`
(2026-11-17): until then an axiom without the entry bound, which claimed for an entry above
`bboltEntryMax` what bbolt does not do (`issues/bbolt-max-value-size-unusable.md`). Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract, the
locks and the views".
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

/-- `b.Put(key, value)` in the write transaction, a key of `1..MaxKeySize` bytes and an entry of at
most `bboltEntryMax` bytes (`2 ^ 28`, below `MaxValueSize`: larger entries bbolt accepts but cannot
store, `Spec/go_etcd_io/bbolt/Data.lean`): `nil` and the entry set (bbolt copies the key and keeps the
value). The handle must be at the bucket's current generation (`G n = g`: not a handle of a deleted
bucket). -/
abbrev bbolt.Bucket.Put_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData) (key value : GoSlice) (kb vb : GoString) (dk : DFrac),
  G n = g → S.lookup n = some m → 0 < kb.length → kb.length ≤ backend.maxKeySize →
  kb.length + vb.length ≤ bbolt.bboltEntryMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g ∗ key ↦*{dk} kb ∗ value ↦*□ vb }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ RET #GoInterface.nil; key ↦*{dk} kb ∗ ownWTxG tx γ D (S.insert n (m.insert kb vb)) G }}

end spec

end EtcdGrove
end Perennial
