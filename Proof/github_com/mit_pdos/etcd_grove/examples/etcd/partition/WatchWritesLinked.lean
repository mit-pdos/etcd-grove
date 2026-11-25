/-
`client_Put_km`, over the client's linked results, moved out of `WatchWrites.lean` (2026-11-18)
so that `memberPut` and `wsInvH`, which specs name, import no linked result (CLAUDE.md, "Import
tiers"). See `WatchWrites.lean`'s header.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.WatchWrites
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.WatchWritesLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section put
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`cli.Put(ctx, key, val)` through a client of the members `ms`** (see the file header). -/
theorem client_Put_km [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF)
    (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key val : GoString)
    (sl : GoSlice) (Q : KVState → IProp GF) (hsz : opSizeOk (opPutModel key val [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        isNewClient cl (ms.map client.SrvAt.addr) V ∗
        client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
        ([∗list] x ∈ ms, memberPut γk x) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu1 γk (.put (client.putKeyOp key val)) Q }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
          ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ σ.compacted = 0 ∧ 1 ≤ σ.rev ∧
            σ.rev + 4 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hcl, #Hone, #Hms, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  ihave #Hregs : ([∗list] x ∈ ms, client.kvRegsAt x) $$ [Hms]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => memberPut (GF := GF) γk x) fun _ => by
      iintro #H; iunfold memberPut at H; icases H with ⟨#H1, -⟩; iexact H1) $$ Hms
  ihave #HF : ([∗list] x ∈ ms, srvApi.kvLogLb x.E.γs []) $$ [Hms]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => memberPut (GF := GF) γk x) fun _ => by
      iintro #H; iunfold memberPut at H; icases H with ⟨-, #H1, -⟩; iexact H1) $$ Hms
  have hau := client.bigAndL_of_sep ms (kvOpAu1 (GF := GF) γk (.put (client.putKeyOp key val)) Q)
    (fun y : client.SrvAt GF => memberPut γk y)
    (fun y : client.SrvAt GF => kvOpAu1 y.γr.kv (.put (client.putKeyOp key val)) Q)
    (fun y _ => by
      iintro ⟨Hk, #Hm⟩
      iunfold memberPut at Hm
      icases Hm with ⟨-, -, %h⟩
      rw [client.kvOpAu1_names y.γr.kv γk h]
      iexact Hk)
  ihave Hau := hau $$ [Hau Hms]
  · iframe Hau; iframe #
  wp_apply (client.client_Put_rep cl ms V ci cd key val sl Q hsz) $$ [$Hlt Hau] as %resp %err ⟨Hlt, Hout⟩
  · iframe #; iexact Hau
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, Hr⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iunfold client.putReplied at Hr
    icases Hr with ⟨%hm, %y, %y', %l, %skip, %Hp, -, -, -, -, ⟨%ltq, -, HQ⟩⟩
    obtain ⟨-, hrev, -, -, -, -, hlen, hb⟩ := Hp
    iexists m, kvStateOf y.log ltq
    iframe Hm HQ
    ipureintro
    refine ⟨?_, kvStateOf_compacted _, ?_, ?_⟩
    · rw [hrev, client.kvStateOf_rev_succ _ hlen]
    · rw [kvStateOf_rev]; omega
    · rw [kvStateOf_rev]; omega
  · iright
    ipureintro; exact Herr

theorem client_Put_km_law_holds : client_Put_km.law (GF := GF) (hG := hG) :=
  client_Put_km

end put

end etcd_partition
end EtcdGrove
end Perennial
