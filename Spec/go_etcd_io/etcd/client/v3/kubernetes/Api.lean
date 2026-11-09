/-
# etcd's Kubernetes client interface (`client/v3/kubernetes`, batch 1c)

`kubernetes.Client` embeds a `*clientv3.Client` and implements `kubernetes.Interface` (`Get`, `List`,
`Count`, `OptimisticPut`, `OptimisticDelete`) over the client's `KV` field: each is one call of W0's
KV contract (`kvAt`, through `isClient_KV`), so each is the KV contract's shape over the request it
builds: the caller's atomic update over `etcdState γ` (persistent for the reads, exclusive for the
two compare-and-swaps), the reply as the store's own response struct, or an error that settles
nothing.

## Vocabulary

* The requests (pure): `getReqM`, `listReqM`, `countReqM` (ranges), `optPutTxnM`, `optDeleteTxnM`
  (transactions: `If(ModRevision(key) = rev)`, a put or a delete, the get on failure if asked).
* The replies: `getRespM`, `listRespM`, `kubeTxnReply` (the struct's fields against the answer).
* `kubeAt v γ who` (persistent): the `Interface` value `v` meets the contract (`Kube.methods`);
  `kubeClient_kubeAt`: a `*Client` whose `Client` field is `isClient` and whose `Kubernetes` field is
  itself. Kubernetes' store calls through `kc.Kubernetes`.

## Requirement snippets

`examples/specreq/clientv3client/kubernetes.go` (`ReqKubeCAS`, `ReqKubeGetList`); W0's
`clientv3kv/txn.go` (`ReqCASModRevision`) covers the transaction itself.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient
public import GeneratedProof.go_etcd_io.etcd.client.v3.kubernetes
public import Spec.PkgInit.go_etcd_io.etcd.client.v3.kubernetes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Kubernetes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

/-! ## Requests -/

/-- `Get`: `WithRev(rev), WithLimit(1)`. -/
def getReqM (key : GoString) (rev : w64) : RangeReq :=
  (opGetM key [withRevM rev, withLimitM (W64 1)]).rangeReq

/-- `List`: from `start` (the continue key, or the prefix) to the prefix's end, a limit, a
revision. -/
def listReqM (pfx cont : GoString) (lim rev : w64) : RangeReq :=
  (opGetM (if cont = [] then pfx else cont)
    [withRangeM (prefixEnd pfx), withLimitM lim, withRevM rev]).rangeReq

/-- `Count`: `WithPrefix(), WithCountOnly()`. -/
def countReqM (pfx : GoString) : RangeReq :=
  (opGetM pfx [withPrefixM, withCountOnlyM]).rangeReq

/-- `If(Compare(ModRevision(key), "=", rev))`. -/
def modRevCmp (key : GoString) (rev : w64) : EtcdModel.Compare :=
  { result := cmpEqual, target := cmpTMod, key := key, rangeEnd := [],
    targetUnion := .modRevision (sint.Z rev) }

/-- `OptimisticPut`'s transaction. -/
def optPutTxnM (key val : GoString) (rev lease : w64) (gof : Bool) : TxnReq :=
  { compare := [modRevCmp key rev], success := [.put (opPutM key val [withLeaseM lease]).putReq],
    failure := if gof then [.range (opGetM key []).rangeReq] else [] }

/-- `OptimisticDelete`'s transaction. -/
def optDeleteTxnM (key : GoString) (rev : w64) (gof : Bool) : TxnReq :=
  { compare := [modRevCmp key rev], success := [.deleteRange (opDeleteM key []).deleteReq],
    failure := if gof then [.range (opGetM key []).rangeReq] else [] }

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The single key-value of a range's answer (`len(Kvs) == 1`), owned, or `nil`. -/
def singleKV (a : RangeAns) (p : Loc) : IProp GF :=
  match a.kvs with
  | [kv] => keyValueOwn p (DFrac.own 1) (KeyValueM.ofKV kv)
  | _ => iprop(⌜p = null⌝)

/-- `Get`'s reply for the answer `res`. -/
def getReply (res : Resp) (r : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface) :
    IProp GF :=
  match res with
  | .ok (.range rev a) => iprop(⌜err = GoInterface.nil ∧ r.Revision' = W64 rev⌝ ∗ singleKV a r.KV')
  | .err e => iprop(⌜err = errVal e⌝)
  | _ => iprop(False)

/-- `List`'s reply. -/
def listReply (res : Resp) (r : go_etcd_io.etcd.client.v3.kubernetes.ListResponse)
    (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.range rev a) => iprop(⌜err = GoInterface.nil ∧ r.Revision' = W64 rev ∧ r.Count' = W64 a.count⌝ ∗
      msgsOwn keyValueOwn r.Kvs' (DFrac.own 1) (a.kvs.map KeyValueM.ofKV))
  | .err e => iprop(⌜err = errVal e⌝)
  | _ => iprop(False)

/-- `Count`'s reply. -/
def countReply (res : Resp) (n : w64) (err : GoInterface) : IProp GF :=
  match res with
  | .ok (.range _ a) => iprop(⌜err = GoInterface.nil ∧ n = W64 a.count⌝)
  | .err e => iprop(⌜err = errVal e ∧ n = W64 0⌝)
  | _ => iprop(False)

/-- A compare-and-swap's reply (`PutResponse`'s or `DeleteResponse`'s fields `KV`, `Succeeded`,
`Revision`): on failure with the get asked, the key's value then (the failure branch's one range). -/
def txnReply (gof : Bool) (res : Resp) (kvp : Loc) (succ : Bool) (rv : w64) (err : GoInterface) :
    IProp GF :=
  match res with
  | .ok (.txn rev ok rs) => iprop(⌜err = GoInterface.nil ∧ succ = ok ∧ rv = W64 rev⌝ ∗
      if gof && !ok then (∃ rev' a, ⌜rs = [.range rev' a]⌝ ∗ singleKV a kvp) else ⌜kvp = null⌝)
  | .err e => iprop(⌜err = errVal e⌝)
  | _ => iprop(False)

/-- The update of a call (persistent if `rep`). -/
def kubeAU (γ : Cluster) (who : Principal) (rq : Req) (rep : Bool)
    (Q : State → State → Resp → IProp GF) : IProp GF :=
  iprop(□?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who rq σ σ' res⌝ ∗ etcdState γ σ', COMM Q σ σ' res }>)

/-- **The `Interface` value `v` meets the Kubernetes contract** (persistent). -/
opaque kubeAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- `Get` (`m s`: the method `s` of the receiver). -/
def Kube.GetTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (key : GoString) (o : go_etcd_io.etcd.client.v3.kubernetes.GetOptions)
     (Q : State → State → Resp → IProp GF),
    {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ kubeAU γ who (.range (getReqM key o.Revision')) true Q }}
      (App (App (App (Val (m go!"Get")) (Val #ctx)) (Val #key)) (Val #o))
    {{ (r : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface), RET (PairV #r #err);
        (∃ σ σ' res, Q σ σ' res ∗ getReply res r err) ∨ indefCall err }}

/-- `List` (`m s`: the method `s` of the receiver). -/
def Kube.ListTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀(ctx : GoInterface) (pfx : GoString) (o : go_etcd_io.etcd.client.v3.kubernetes.ListOptions)
     (Q : State → State → Resp → IProp GF),
    {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
        kubeAU γ who (.range (listReqM pfx o.Continue' o.Limit' o.Revision')) true Q }}
      (App (App (App (Val (m go!"List")) (Val #ctx)) (Val #pfx)) (Val #o))
    {{ (r : go_etcd_io.etcd.client.v3.kubernetes.ListResponse) (err : GoInterface), RET (PairV #r #err);
        (∃ σ σ' res, Q σ σ' res ∗ listReply res r err) ∨ indefCall err }}

/-- `Count` (`m s`: the method `s` of the receiver). -/
def Kube.CountTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀(ctx : GoInterface) (pfx : GoString) (o : go_etcd_io.etcd.client.v3.kubernetes.CountOptions)
     (Q : State → State → Resp → IProp GF),
    {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ kubeAU γ who (.range (countReqM pfx)) true Q }}
      (App (App (App (Val (m go!"Count")) (Val #ctx)) (Val #pfx)) (Val #o))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        (∃ σ σ' res, Q σ σ' res ∗ countReply res n err) ∨ (⌜n = W64 0⌝ ∗ indefCall err) }}

/-- `OptimisticPut` (`m s`: the method `s` of the receiver). -/
def Kube.OptimisticPutTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀(ctx : GoInterface) (key : GoString) (vsl : GoSlice) (v : GoString) (rev : w64)
     (o : go_etcd_io.etcd.client.v3.kubernetes.PutOptions) (Q : State → State → Resp → IProp GF),
    {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ vsl ↦*□ v ∗
        kubeAU γ who (.txn (optPutTxnM key v rev o.LeaseID' o.GetOnFailure')) false Q }}
      (App (App (App (App (App (Val (m go!"OptimisticPut")) (Val #ctx)) (Val #key)) (Val #vsl))
        (Val #rev)) (Val #o))
    {{ (r : go_etcd_io.etcd.client.v3.kubernetes.PutResponse) (err : GoInterface), RET (PairV #r #err);
        (∃ σ σ' res, Q σ σ' res ∗ txnReply o.GetOnFailure' res r.KV' r.Succeeded' r.Revision' err) ∨
        indefCall err }}

/-- `OptimisticDelete` (`m s`: the method `s` of the receiver). -/
def Kube.OptimisticDeleteTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀(ctx : GoInterface) (key : GoString) (rev : w64)
     (o : go_etcd_io.etcd.client.v3.kubernetes.DeleteOptions) (Q : State → State → Resp → IProp GF),
    {{ P ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
        kubeAU γ who (.txn (optDeleteTxnM key rev o.GetOnFailure')) false Q }}
      (App (App (App (App (Val (m go!"OptimisticDelete")) (Val #ctx)) (Val #key)) (Val #rev)) (Val #o))
    {{ (r : go_etcd_io.etcd.client.v3.kubernetes.DeleteResponse) (err : GoInterface), RET (PairV #r #err);
        (∃ σ σ' res, Q σ σ' res ∗ txnReply o.GetOnFailure' res r.KV' r.Succeeded' r.Revision' err) ∨
        indefCall err }}

/-- **The Kubernetes contract.** -/
def Kube.methods (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  Kube.GetTriple m P γ who ∧
  Kube.ListTriple m P γ who ∧
  Kube.CountTriple m P γ who ∧
  Kube.OptimisticPutTriple m P γ who ∧
  Kube.OptimisticDeleteTriple m P γ who

/-! ## Laws -/

def kubeAt_persistent.spec : Prop := ∀ v γ who, Persistent (kubeAt (GF := GF) v γ who)

/-- The bundle's triples. -/
def kubeAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Kube.methods (fun s => v @!! go_etcd_io.etcd.client.v3.kubernetes.Interface.ty @!! s)
    (kubeAt (GF := GF) v γ who) γ who

/-- **A `*Client` built by `New`**, once its `clientv3.Client` is frozen: its `Kubernetes` field (the
client itself) meets the contract. -/
def kubeClient_kubeAt.spec : Prop := ∀ (kc c : Loc) (γ : Cluster) (who : Principal),
  kc ↦□ ({ Client' := c,
           Kubernetes' := interface.mkOk
             (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #kc } :
         go_etcd_io.etcd.client.v3.kubernetes.Client) ∗ isClient (GF := GF) c γ who ⊢
    kubeAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #kc)
      γ who

end res

end Kubernetes
end EtcdGrove
end Perennial
