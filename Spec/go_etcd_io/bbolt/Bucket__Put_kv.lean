/-
`Bucket.Put_kv` (bbolt). `b.Put(key, value)` in the write transaction.
The trust boundary: bbolt's `Bucket.Put` as the backend uses it (`InvBbolt.lean`), an axiom in
`Proof/go_etcd_io/bbolt/Bucket__Put_kv.lean`: **the one `_kv` spec stage S1 of
`notes/bbolt-integration-plan.md` (2026-11-17) left an axiom.** bbolt's proved `Put`
(`Spec/go_etcd_io/bbolt/Bucket__Put.lean`) takes an entry bound, `kb.length + vb.length ≤
bboltEntryMax` (`2 ^ 28`: above it a page of four entries passes `MaxAllocSize` and `Commit` or a
later read panics, `issues/bbolt-max-value-size-unusable.md`), which no caller of the backend's
`unsafePut` can give today: mvcc's puts are bounded only by `k.length < 2 ^ 63 - 1`, and the
server's value-length law bounds each key and value by `etcdKeyMax = 2 ^ 27` apart, so a marshalled
`KeyValue` can pass `2 ^ 28` by its framing. So this spec keeps its pre-S1 statement (over the
proved bbolt's vocabulary) for every value up to `MaxValueSize`, and with the proved `Commit` it
claims what bbolt does not do for an entry above `bboltEntryMax` (the same false case the pre-S1
`Tx.Commit_kv` axiom claimed). Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The
backend: the buffers, bbolt as a key-value contract, the locks and the views".
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

/-- `b.Put(key, value)` in the write transaction (a key of `1..MaxKeySize` bytes): for a value of
at most `MaxValueSize`, `nil` and the entry set (bbolt copies the key and keeps the value); for a
larger one, an error (`ErrValueTooLarge`: bbolt checks the size before anything else) and the
contents unchanged (2026-10-13, unit 5: the backend's `unsafePut` then calls `lg.Fatal`). The
handle must be at the bucket's current generation (`G n = g`: not a handle of a deleted bucket). -/
abbrev bbolt.Bucket.Put_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData) (key value : GoSlice) (kb vb : GoString) (dk : DFrac),
  G n = g → S.lookup n = some m → 0 < kb.length → kb.length ≤ backend.maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g ∗ key ↦*{dk} kb ∗ value ↦*□ vb }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      ((⌜vb.length ≤ backend.maxValueSize ∧ err = GoInterface.nil⌝ ∗
          ownWTxG tx γ D (S.insert n (m.insert kb vb)) G) ∨
       (⌜backend.maxValueSize < vb.length ∧ err ≠ GoInterface.nil⌝ ∗ ownWTxG tx γ D S G)) }}

end spec

end EtcdGrove
end Perennial
