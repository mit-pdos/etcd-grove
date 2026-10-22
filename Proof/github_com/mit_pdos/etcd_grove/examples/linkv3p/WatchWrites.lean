/-
**The writers' puts through the cluster's clients** (W4d of `notes/watch-cut-plan.md`,
2026-10-22; watchkv's `Writes.lean` at one server, for clients of the three members). Lean-first
(no Rocq counterpart).

* `memberPut γr x`: a member as a writer's put sees it: etcd's KV registered at its bridge
  (`kvRegsAt`), its KV invariants, its store's empty log certified (`idxCert_nil`), its names the history's (`memberOf`) with the history's KV
  state and workload (`etcdKV` and the updates read only those, `kvOpAu1_congr`).
* `client_Put_hist`: `cli.Put` through a client of the members `ms` (failover, its writes sent at
  most once, D29) with the writer's update at each member (`put_au`, at the history's names): `nil`
  and some member's `putReplied`, or an error (`client_put_any`; linkvtxn's `client_Put_st` keeps
  only the state).
* `wsInvH`: the writers' log's lock invariant (watchkv's `wsInv`), its records' `okFactH`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchHist
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A member as a writer's put sees it** (persistent; see the file header). -/
def memberPut (γr : ReadNames) (x : client.SrvAt GF) : IProp GF :=
  iprop(client.kvRegsAt x ∗ srvKVInvs x.E x.γr ∗ mvcc.idxCert x.E.γ.idx [] ∗
    ⌜v3rpc.memberOf γr.raft γr.kv x.γr ∧ x.γr.kv.st = γr.kv.st ∧ x.γr.kv.wl = γr.kv.wl⌝)

instance memberPut_persistent (γr : ReadNames) (x : client.SrvAt GF) :
    Persistent (memberPut (GF := GF) γr x) := by
  unfold memberPut; infer_instance

/-- An update reads only the KV state's name and the workload. -/
theorem kvOpAu1_congr (γk γk' : KVNames) (hst : γk.st = γk'.st) (hwl : γk.wl = γk'.wl)
    (op : KVOp) (Q : KVState → IProp GF) : kvOpAu1 (GF := GF) γk op Q = kvOpAu1 γk' op Q := by
  unfold kvOpAu1 kvAu1 etcdKV; rw [hst, hwl]

/-- **The writers' log's lock invariant** (watchkv's `wsInv`, its records' `okFactH`). -/
def wsInvH (w : Loc) (γr : ReadNames) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.linkv3p.writes go!"ok" w ↦ sl ∗
    sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗ □ [∗list] p ∈ oks, okFactH γr p)

end defs

section put
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`cli.Put(ctx, key, val)` through a client of the members `ms`** (see the file header). -/
theorem client_Put_hist [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isNewClient cl (ms.map client.SrvAt.addr) V ∗
        client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
        ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.put (client.putKeyOp key val)) Q) }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ ∃ x : client.SrvAt GF,
            ⌜x ∈ ms⌝ ∗ client.putReplied x.E x.γr []
              (txn.putOpOf key val (W64 0) false false false) Q x.cid x.mid m) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hregs, #HF, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hwo : client.writeOnce api (ms.map client.SrvAt.addr) $$ [Hone]
  · iunfold client.clientWriteOnce at Hone
    iunfold client.writeOnce
    iexact Hone
  ihave #Hrr : ([∗list] x ∈ ms, isGrpcRpc x.addr go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpec x.E x.γr x.cid x.mid)) $$ [Hregs]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => client.kvRegsAt (GF := GF) x) fun _ => by
      iintro #H; iunfold client.kvRegsAt at H; icases H with ⟨#H1, -, -, -⟩; iexact H1) $$ Hregs
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_put_any api ms ci cd key val sl Q) $$ [Hau] as %resp %err Hout
  · iframe #
    iexact Hau
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    iexists x
    iframe Hr
    ipureintro; exact hx
  · iright
    ipureintro; exact Herr

end put

end linkv3p
end EtcdGrove
end Perennial
