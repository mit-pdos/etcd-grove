/-
`UnsafeForEach` (the backend). `t.UnsafeForEach(bucket, visitor)` under the lock, the embedded `batchTx`'s
(`batch_tx.go`): the visitor on each entry of the bucket in bbolt's writer's contents (the session's view
`st.S`), in key order, stopped by its first error; in either mode of the lock.
Lean-first (no Rocq counterpart); auth-schema-srv A6 (c) (2026-11-18): the auth realization's batch reader walks the
users' bucket with it (`authBatchTx.UnsafeGetAllUsers`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

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

/-- `t.UnsafeForEach(bucket, visitor)` holding the batch lock (in its mode `c`): `batchTx.UnsafeForEach`'s walk
of the entries of the session's view (`bktOf st.S bi.name`) in key order; the visitor gets the whole write
transaction at its view (some generations `G`), given back at the same view, and slices valid while bbolt's
write transaction `st.tx` is open. -/
abbrev backend.batchTxBuffered.UnsafeForEach.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (c : Bool)
    (bk : GoInterface) (bi : BucketInfo) (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st c ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (G : GoString → Nat) (i : Nat) (e : Ent) (k v : GoSlice),
          ⌜(bktEnts (bktOf st.S bi.name))[i]? = some e⌝ →
          {{ I i ∗ ownWTxG st.tx γ.db st.C st.S G ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes st.tx γ.db k e.1 ∗
              txBytes st.tx γ.db v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; ownWTxG st.tx γ.db st.C st.S G ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; batchLocked γ P b st c ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (bktEnts (bktOf st.S bi.name)).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (bktEnts (bktOf st.S bi.name)).length⌝ ∗
          E i err)) }}

end spec

end EtcdGrove
end Perennial
