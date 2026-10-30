/-
**`cli.Put` through a `New`'s client to authkv's member, auth on** (`notes/authkv-main-plan.md`,
S5; 2026-10-29). Lean-first (no Rocq counterpart).

`(*Client).Put` calls its `KV` field's `Put`. With the field a `*kv` over the client's connection
(`clientTokAt`, what `New` gives), that is `client.client_put_on` at the member's `Put` registered
with etcd's spec with auth on. E3zc left the `*Client` wrappers for the auth-on calls undone
(`notes/decisions.md`, "E3zc of the auth plan", "Not yet"). This is the one `SetUp` needs, kept
in authkv until the client package has them.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ResultsOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`cli.Put(ctx, key, val)` through a client whose `KV` is a `*kv` over `conn`** (`clientTokAt`'s
parts) to a member with auth on: `client_put_on` through the `*Client` method. -/
theorem client_Put_on (cl api conn : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn [addr] ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗
        mvcc.idxCert E.γ.idx F ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        □ kvOpAu1 ρ.rd.kv (.put (putKeyOp key val)) Q }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
            putReplied E ρ.rd F (putKeyOp key val) Q cid mid m ∗
            ∃ md, ⌜clientAttemptMd conn (GoInterface.ok ci) md⌝ ∗
              v3rpc.writeGrantOn s E ρ (auth.mdTokenOf md) (irrPut (putKeyOp key val))) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hreg, #HF, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  imod srvReqLogLb_nil (GF := GF) ρ.raft with #H0
  wp_apply (client_put_on api conn addr s E ρ cid mid ci cd key val sl Q F) $$ [] as %resp %err Hout
  · iframe #
    ileft
    imodintro
    unfold clientOpAuOn
    iexists []
    iframe H0
    unfold kvOpAu1
    iapply kvAu1_G $$ Hau
  iapply HΦ
  icases Hout with (⟨%Herr, Hr⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexact Hr
  · iright
    isplitl
    · ipureintro; exact Herr.1
    · iexact Hke

end proof

end authkv
end EtcdGrove
end Perennial
