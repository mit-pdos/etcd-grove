/-
`unsafeForEach` (the backend, `batch_tx.go`). `unsafeForEach(tx, bucket, visitor)` over bbolt's
transaction `tx`, read or write (the walk holds it at a share `q`, all of it for the write transaction, at its view `T`): the visitor on each entry of the bucket in key order (none
if the transaction has no such bucket), stopped by its first error.
Lean-first (no Rocq counterpart); auth-schema-srv A2 (`notes/auth-schema-srv-a2-draft.md` §4); over lean's
bbolt vocabulary and the proved `Bucket.ForEach` since the port (`notes/auth-schema-srv-port-scope.md` §2.B).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `unsafeForEach(tx, bucket, visitor)` on bbolt's transaction `tx` of the database `γd`, held at the
share `q` (all of it for the write transaction, as `Tx.Bucket` asks) at the view `T`: for the caller's
invariant `I` (over the number of entries visited) and error resource `E`, given the visitor's spec on the
`i`-th entry `e` of the bucket in `T`'s contents (bbolt's `ForEach` visitor's: the walk's transaction,
given back at the same view, and the key and value slices valid while `tx` is open), it returns `nil` with
`I` at the bucket's length (an absent bucket: no entry), or the visitor's first error, at entry `i`, with
`E i err`. -/
abbrev backend.unsafeForEach.spec : Prop :=
  ∀ (tx : Loc) (γd : DBNames) (q : Qp) (T : bbolt.TxView) (bk : GoInterface) (bi : BucketInfo)
    (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  (T.rw = true → q = 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      txLive tx γd q T ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(bktEnts (bktOf T.cur bi.name))[i]? = some e⌝ →
          {{ I i ∗ txLive tx γd q T ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes tx γd k e.1 ∗ txBytes tx γd v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive tx γd q T ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (App (Val (@! unsafeForEach)) (Val #tx)) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; txLive tx γd q T ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (bktEnts (bktOf T.cur bi.name)).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (bktEnts (bktOf T.cur bi.name)).length⌝ ∗
          E i err)) }}

end spec

end EtcdGrove
end Perennial
