/-
`(*txnOrdering).Commit()` (`client/v3/ordering/kv.go`, etcd-io/etcd#22122). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.InvOrdering

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI go_etcd_io.etcd.client.v3.ordering go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

/-- `txn.Commit()` (`client/v3/ordering/kv.go`, PR #22122):
- Reads `prevRev := txn.getPrevRev()`, builds `opTxn := clientv3.OpTxn(txn.cmps, txn.thenOps, txn.elseOps)`,
  and computes `canRetry := isReadOnly(opTxn)`.
- When `isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = true` (read-only transaction), requires
  persistent `□ P` (as `Commit` may retry on ordering violations when `orderViolationFunc` returns
  `nil`), and guarantees `sint.Z prevRev ≤ sint.Z rev` on any `nil`-error return.
- When `isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = false` (mutable transaction), requires
  only a single linear execution token `P : IProp GF` consumed by `kvDoTxnSpec` — proving in
  separation logic that `txn.KV.Do` is executed **at most once** and never automatically resubmitted. -/
abbrev txnOrdering.Commit.spec : Prop :=
  ∀ (txnp kvp : Loc) (innerTxn : go_etcd_io.etcd.client.v3.Txn)
    (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc)
    (ctx : context.Context) (st : TxnOrderingState)
    (R : w64 → IProp GF) (P : IProp GF)
    (PostOk : Loc → w64 → IProp GF) (PostErr : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      isKvOrdering kvp kv vf ∗
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      kvOrderingHandle kvp R ∗
      (if isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) then □ P else P) ∗
      kvDoTxnSpec kv ctx st.ms st.ts st.es R P PostOk PostErr ∗
      orderViolationSpec vf R PostErr }}
    (App (Val (txnp @!! go.GoType.PointerType txnOrdering.ty @!! go!"Commit")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      kvOrderingHandle kvp R ∗
      if decide (err = GoInterface.nil) then
        ∃ (prevRev rev : w64) (hdr : Loc),
          ⌜resp ≠ null ∧ hdr ≠ null ∧
            (isReadOnlyM (.txn OpFull.txnInit st.ms st.ts st.es) = true → sint.Z prevRev ≤ sint.Z rev)⌝ ∗
          structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ rev ∗
          □ R prevRev ∗ □ R rev ∗ PostOk resp rev
      else
        ⌜resp = null⌝ ∗ PostErr err }}

end spec

end ordering
end EtcdGrove
end Perennial
