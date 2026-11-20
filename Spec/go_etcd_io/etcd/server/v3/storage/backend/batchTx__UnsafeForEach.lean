/-
`batchTx.UnsafeForEach` (`batch_tx.go`). `t.UnsafeForEach(bucket, visitor)` on the writer: the visitor
on each entry of the bucket in bbolt's writer's contents (the session's view `st.S`), in key order,
stopped by its first error.
Lean-first (no Rocq counterpart); auth-schema-srv A2 (`notes/auth-schema-srv-a2-draft.md` §4).
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

/-- `t.UnsafeForEach(bucket, visitor)` holding the batch lock (`btW`): `unsafeForEach` over the write
transaction `st.tx`, whose entries are the session's view's (`bktOf st.S bi.name`); the visitor gets the
whole write transaction at its view (some generations `G`), given back at the same view, and slices valid
while `st.tx` is open. -/
abbrev backend.batchTx.UnsafeForEach.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ btW γ t st ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (G : GoString → Nat) (i : Nat) (e : Ent) (k v : GoSlice),
          ⌜(bktEnts (bktOf st.S bi.name))[i]? = some e⌝ →
          {{ I i ∗ ownWTxG st.tx γ.db st.C st.S G ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes st.tx γ.db k e.1 ∗
              txBytes st.tx γ.db v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; ownWTxG st.tx γ.db st.C st.S G ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (Val (btOf t @!! go.GoType.PointerType batchTx.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; btW γ t st ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (bktEnts (bktOf st.S bi.name)).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (bktEnts (bktOf st.S bi.name)).length⌝ ∗
          E i err)) }}

end spec

end EtcdGrove
end Perennial
