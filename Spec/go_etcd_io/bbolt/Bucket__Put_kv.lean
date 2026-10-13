/-
`Bucket.Put_kv` (bbolt). `b.Put(key, value)` in the write transaction (a key of `1..MaxKeySize` bytes): the entry
set for a value of at most `MaxValueSize`, else an error and nothing changed.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Bucket__Put_kv.lean`. Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.Put(key, value)` in the write transaction (a key of `1..MaxKeySize` bytes): for a value of
at most `MaxValueSize`, `nil` and the entry set (bbolt copies the key and keeps the value); for a
larger one, an error (`ErrValueTooLarge`: bbolt checks the size before anything else) and the
contents unchanged (2026-10-13, unit 5: the backend's `unsafePut` then calls `lg.Fatal`). -/
abbrev bbolt.Bucket.Put_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (b : Loc) (n : GoString) (m : BktData)
    (key value : GoSlice) (kb vb : GoString) (dk : DFrac),
  S.lookup n = some m → 0 < kb.length → kb.length ≤ maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTx tx γ D S ∗ wBkt tx b n ∗ key ↦*{dk} kb ∗ value ↦*□ vb }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      ((⌜vb.length ≤ maxValueSize ∧ err = GoInterface.nil⌝ ∗
          ownWTx tx γ D (S.insert n (m.insert kb vb))) ∨
       (⌜maxValueSize < vb.length ∧ err ≠ GoInterface.nil⌝ ∗ ownWTx tx γ D S)) }}

end spec

end EtcdGrove
end Perennial
