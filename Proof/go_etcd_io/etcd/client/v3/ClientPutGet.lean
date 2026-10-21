/-
**`(*Client).Put`/`Get` by the client `New` returns** (item 9, point 7, 2026-10-18): the methods
of `*Client` promoted from its embedded `KV` interface reduce to the `*kv`'s (`kv.Put`/`kv.Get`)
that `New` stores in the `KV` field (`isNewClient`), so `PutThenGet.lean`'s `client_put_own` and
`client_get_own` hold of the calls the adequacy example makes (`cli.Put(ctx, k, v)`,
`cli.Get(ctx, k)`). Lean-first (no Rocq counterpart).

The reduction is the translation's method-set rules `Client.TypeAssumptions.ptr_Put_unfold` and
`ptr_Get_unfold` (a promoted method of an embedded interface is a method resolution on the field's
value), which the Goose configuration emits once the filter names the methods
(`Code/go_etcd_io/etcd/client/v3.toml`: `Client.Put`, `Client.Get`); no translator change.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PutThenGet
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section e2e
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The client's invariant at a log's state** (`putGetInv_alloc`; every log's state is sorted
by key, `mvcc.stateAfter_sorted`): from the client's `etcdKV` at `kvStateOf l` (the bootstrap
log's model, as the server's allocation gives it, `srvBootOut`). -/
theorem putGetInv_alloc_log (γr : ReadNames) (l : mvcc.Log) (key val : GoString)
    (hW : γr.kv.wl.writes (.put (putKeyOp key val))) (Em : CoPset) :
    etcdKV (GF := GF) γr.kv (kvStateOf l) ⊢ |={Em}=> ∃ γf : GName, putGetInv γr γf key val :=
  putGetInv_alloc γr key val (kvStateOf l) (mvcc.stateAfter_sorted l) hW Em

/-- **`cli.Put(ctx, key, val)` by `New`'s client `cl`** (`client_put_own` through the `KV` field):
`nil`, the reply and the put's flag; or an error. -/
theorem client_Put_own (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (γf : GName) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl ep V ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Put" (etcdPutSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        putGetInv γr γf key val ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ (∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E γr F (putKeyOp key val) (fun _ => monoNatLbOwn γf 1) cid mid m) ∗
            monoNatLbOwn γf 1) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc, #Hctx, #Hce, #Hopts, #Hinv, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_put_own api ep E γr γf cid mid ci cd key val sl F) $$ [] as %resp %err Hout
  · iframe #
  iapply HΦ
  iexact Hout

/-- **`cli.Get(ctx, key)` by `New`'s client `cl`, after its put fired** (`client_get_own` through
the `KV` field): `nil` and a reply whose first key-value's value is `val`; or an error. -/
theorem client_Get_own (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (γf : GName) (c cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl ep V ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Range" (etcdRangeSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
        putGetInv γr γf key val ∗ monoNatLbOwn γf 1 ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            ⌜m.kvs.head?.map EtcdKv.value = some val⌝) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc, #Hctx, #Hce, #Hopts, #Hc, #Hinv, #Hlb, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client_get_own api ep E γr γf c cid mid ci cd key val sl F) $$ [] as %resp %err Hout
  · iframe #
  iapply HΦ
  iexact Hout

end e2e

end client
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.client.putGetInv_alloc_log
#print axioms Perennial.EtcdGrove.client.client_Put_own
#print axioms Perennial.EtcdGrove.client.client_Get_own
