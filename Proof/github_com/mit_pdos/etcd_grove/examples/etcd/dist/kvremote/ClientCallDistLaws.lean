/-
Lean-first (no Rocq counterpart).

**txnlin's client calls across machines, as hypotheses** (`Call_dist`'s, P9): the cross-machine
analogues of `client/v3/ClientCallLaws.lean`'s `client_{Put,Get,Delete,Txn}_st.law` and of txnlin's
`CallsLaws.lean` (`client_List_st.law`, `txn_Commit_st.law`), which `Proof/.../kvremote/CallDist.lean`
(the copies of txnlin's `call*` proofs) takes instead of those. Each is the `_st` law with the
in-process servers' facts (`isNewClient ∗ clientWriteOnce ∗ [∗list] kvRegsAt`, one update per member)
replaced by the cluster view's client facts `kvClientAt cl api eps V Γ` and one update at the
cluster's KV names `Γ.kv`; the write calls for a cluster with auth off (`Γ.auth = false`); the error
arm without `kvErr` (N2's drafts claim nothing of a remote call's error; txnlin's `call*` read only
`err ≠ nil` there).

`CallDistLinked.lean` proves them from N2's drafts (`dist/ClientViewDist.lean`: `KV_Put_dist`,
`KV_Get_dist`, `KV_Delete_dist`, `Txn_Commit_dist`, hypotheses) and the client's `kv.Txn`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Calls

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.server.v3.etcdserver
open EtcdGrove.etcd_dist

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cli.Get(ctx, key)` across machines (`client_Get_st.law` at the view): a read update at `Γ.kv`
or none. -/
abbrev client_Get_dist.law : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opGetModel key [])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu Γ.kv Q)) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => decide (v.key = key)) ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }}

/-- `cli.Get(ctx, listFrom, WithRange(listTo))` across machines (`client_List_st.law` at the
view). -/
abbrev client_List_dist.law : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opGetModel listFrom [withRangeM listTo])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
          optsAt sl [withRangeM listTo] ∗ □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu Γ.kv Q)) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #listFrom)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => inRange listFrom listTo v.key) ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }}

/-- `cli.Put(ctx, key, val)` across machines (`client_Put_st.law` at the view), auth off: an update
at `Γ.kv` fired at most once. -/
abbrev client_Put_dist.law : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
      (sl : GoSlice) (Q : KVState → IProp GF) (hsz : opSizeOk (opPutModel key val [])),
    Γ.auth = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          kvOpAu1 Γ.kv (.put (putKeyOp key val)) Q) }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
          ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ kvRevFits (σ.rev + 1)⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }}

/-- `cli.Delete(ctx, key)` across machines (`client_Delete_st.law` at the view), auth off. -/
abbrev client_Delete_dist.law : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opDeleteModel key [])),
    Γ.auth = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
          kvOpAu1 Γ.kv (.deleteRange (txn.deleteOpOf key [] false)) Q) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
          ⌜m.deleted = W64 ((rangeIn σ.kvs (txn.deleteOpOf key [] false)).length : Int) ∧
            m.hdr.revision =
              W64 ((kvOpStep (.deleteRange (txn.deleteOpOf key [] false)) σ).rev : Int) ∧
            kvRevFits (σ.rev + 1)⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }}

/-- `cli.Txn(ctx)` across machines (`client_Txn_st.law` at the view): the builder, empty, made from
the client's `*kv` `api` (`txnKvIs`, what `Txn_Commit_dist` takes). -/
abbrev client_Txn_dist.law : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ ctxOk ci cd ∗ ctxErrClient ci cd) }}
      (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Txn")) (Val #(GoInterface.ok ci)))
    {{ (t : GoInterface), RET #t; levelTok 0 ∗ (∃ tp : Loc,
        ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
        txnObjAt tp eps ci cd TxnBuild.empty ∗ txnKvIs tp api) }}

/-- `Commit()` of the model's transaction across machines (`txn_Commit_st.law` at the view), auth
off: its update by its kind at `Γ.kv` (`callUpd`). -/
abbrev txn_Commit_dist.law : Prop :=
  ∀ [π : NetProtoGS] (cl api tp : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
      (Q : KVState → IProp GF) (cs : List (linkv.MCmp GoString GoString))
      (t e : List (linkv.MOp GoString GoString)) (hb : b.model = clientTxn cs t e)
      (hne : t ++ e ≠ []) (hsz : txnSizeOk (txnWireOf b.model)),
    Γ.auth = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ txnObjAt tp eps ci cd b ∗ txnKvIs tp api ∗
          callUpd Γ.kv (.txn cs t e) Q) }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
          callRes (.txn cs t e) Q σ ∗
          ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (linkv.txnOf cs t e)).1 ∧
            opRespsRel false ((linkv.txnOf cs t e).branch m.succeeded)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).2.2
              m.resps ∧
            m.hdr.revision = W64 ((if (linkv.MIn.txn cs t e).isWrite then
              (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev : Nat) : Int) ∧
            kvRevFits σ.rev⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }}

end laws

end etcd_txnlin
end EtcdGrove
end Perennial
