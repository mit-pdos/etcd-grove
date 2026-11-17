/-
`Bucket.ForEach_kvw` (bbolt). `b.ForEach(fn)` in the write transaction: the visitor on each entry of the
bucket's contents now, in key order, stopped by its first error, the transaction's ownership held by the walk.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), as
`Bucket.Cursor_kvw`; an axiom in `Proof/go_etcd_io/bbolt/Bucket__ForEach_kvw.lean` (auth-schema-srv A2,
2026-11-17, the user's choice (B) via etcd-grove-03: `notes/auth-schema-srv-a2-draft.md`). Its Go tests:
`examples/bbolt/foreachkv/foreach_test.go`.
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

/-- `b.ForEach(fn)` on the write transaction's current handle `b` of the bucket `n` (contents `m` now): as
`ForEach_kvr` over the entries `bktEnts m`, the visitor holding half of the transaction's `txLive` and not its
ownership (`ownWTxG`), which the walk keeps and gives back at the end.

Why faithful (bbolt v1.5.0, `bucket.go:585-596`, `cursor.go:32-42`): as `ForEach_kvr`; the write
transaction's cursor reads the materialized nodes, so the walk sees the transaction's own puts and deletes
(`TestOrderWriteTxSeesOwnWrites`; `Cursor_kvw`'s `bktEnts m` of the contents `S` now).
What the visitor must not do ("The provided function must not modify the bucket; this will result in
undefined behavior.", `bucket.go`), and the spec excludes by keeping `ownWTxG` (which `Put_kv`,
`Delete_kv`, `Cursor_kvw`, `Commit_kv`, `CreateBucketIfNotExists_kv`, `DeleteBucket_kv` need):
- delete from the bucket (`TestVisitorDeleteSkips`: deleting the current key skips the next entry);
- put into it (`TestVisitorPutVisited`: a key put after the cursor is walked, or not, by the leaf's
  materialization);
- close the transaction (half of `txLive` only, and no `ownWTxG`). -/
abbrev bbolt.Bucket.ForEach_kvw.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : BktData) (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  G n = g → S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx b n g ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(bktEnts m)[i]? = some e⌝ →
          {{ I i ∗ txLive tx (1 : Qp).half ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes tx k e.1 ∗ txBytes tx v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive tx (1 : Qp).half ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; ownWTxG tx γ D S G ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (bktEnts m).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (bktEnts m).length⌝ ∗ E i err)) }}

end spec

end EtcdGrove
end Perennial
