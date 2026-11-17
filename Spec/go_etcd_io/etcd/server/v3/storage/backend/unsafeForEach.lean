/-
`unsafeForEach` (the backend, `batch_tx.go`). `unsafeForEach(tx, bucket, visitor)` over bbolt's
transaction `tx`, read or write (`FeSide`): the visitor on each entry of the bucket in key order (none
if the transaction has no such bucket), stopped by its first error.
Lean-first (no Rocq counterpart); auth-schema-srv A2 (`notes/auth-schema-srv-a2-draft.md` §4).
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

/-- `unsafeForEach(tx, bucket, visitor)` on the transaction `tx` held as `sd` (`feOwn`): for the
caller's invariant `I` (over the number of entries visited) and error resource `E`, given the visitor's
spec on the `i`-th entry `e` of the bucket in `sd`'s data (bbolt's `ForEach` visitor's: half the
walk's share of `txLive`, the key and value slices valid while `tx` is open), it returns `nil` with
`I` at the bucket's length (an absent bucket: no entry), or the visitor's first error, at entry `i`,
with `E i err`. -/
abbrev backend.unsafeForEach.spec : Prop :=
  ∀ (tx : Loc) (sd : FeSide) (bk : GoInterface) (bi : BucketInfo) (fn : GoFunc)
    (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      feOwn tx sd ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(bktEnts (bktOf sd.data bi.name))[i]? = some e⌝ →
          {{ I i ∗ txLive tx sd.q.half ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes tx k e.1 ∗ txBytes tx v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive tx sd.q.half ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (App (Val (@! unsafeForEach)) (Val #tx)) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; feOwn tx sd ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (bktEnts (bktOf sd.data bi.name)).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (bktEnts (bktOf sd.data bi.name)).length⌝ ∗
          E i err)) }}

end spec

end EtcdGrove
end Perennial
