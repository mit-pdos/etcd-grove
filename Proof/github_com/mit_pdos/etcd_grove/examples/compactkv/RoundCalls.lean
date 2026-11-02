/-
**`compactkv`'s get of a round's key** (the client's `kv.Compact`, 2026-11-01): `cli.Get(ctx, k)`
after round `i`'s put fired returns, if `nil`, a reply whose first key-value's value is the
round's (`client_get_end_to_end` at `getAu_round`, then `client_get_value`; as `client_Get_own`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.Rounds
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
  client

section e2e
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`cli.Get(ctx, k)` by `New`'s client `cl`, after round `i`'s put fired** (see the file
header): `nil` and a reply whose first key-value's value is `val`, at a revision at least a lower
bound `r` of the rounds' state's (the read-side law, 2026-11-02, `roundsInv_revLb`); or an error. -/
theorem client_Get_round (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString) (i : Nat)
    (k : GoString) (hk : keys[i]? = some k) (r : Nat) (c cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (F : mvcc.Log)
    (hsz : opSizeOk (opGetModel k [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        kvRegsAt (⟨ep, E, γr, cid, mid⟩ : SrvAt GF) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
        roundsInv γr γf γl γv keys val ∗ monoNatLbOwn γf (i + 1) ∗ monoNatLbOwn γv r ∗
        mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            ⌜m.kvs.head?.map EtcdKv.value = some val ∧ (r : Int) ≤ sint.Z m.hdr.revision⌝) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc0, #Hctx, #Hce, #Hopts, #Hc, #Hinv, #Hlb, #Hrlb, #HF⟩ HΦ
  ihave #Hrpc := kvRegs_one ep E γr cid mid $$ Hrpc0
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  ihave #Hau := getAu_round γr γf γl γv keys val i k hk r $$ [Hinv Hlb Hrlb]
  · iframe #
  wp_apply (client_get_end_to_end api [ep] E γr c cid mid ci cd k sl
    (fun σ => iprop(⌜(mvcc.findKey k σ.kvs).map EtcdKv.value = some val ∧ r ≤ σ.rev⌝)) F hsz)
    $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, #Hq⟩ | %Herr)
  · ileft
    ihave Hv := client_get_value_rev E γr c cid mid k F _ m $$ Hq
    icases Hv with ⟨%σ, %Hσ, %Hval, %Hrev⟩
    isplitr
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    refine ⟨by rw [Hval, Hσ.1], by rw [Hrev]; exact_mod_cast Hσ.2⟩
  · iright
    ipureintro; exact Herr

/-- **`cli.Get(ctx, k)` by `New`'s client `cl`, after a lower bound `r` of the rounds' state**
(C3's watch side, 2026-11-02): `nil` and a reply at a revision at least `r`; or an error. -/
theorem client_Get_rev (cl : Loc) (ep : GoString) (V : WEnv GF) (E : apply.AEnv GF)
    (γr : ReadNames) (γf γl γv : GName) (keys : List GoString) (val : GoString) (k : GoString)
    (r : Nat) (c cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (F : mvcc.Log)
    (hsz : opSizeOk (opGetModel k [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        kvRegsAt (⟨ep, E, γr, cid, mid⟩ : SrvAt GF) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr c ∗
        roundsInv γr γf γl γv keys val ∗ monoNatLbOwn γv r ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
            ⌜(r : Int) ≤ sint.Z m.hdr.revision⌝) ∨
          ⌜err ≠ GoInterface.nil ∧ resp = null⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc0, #Hctx, #Hce, #Hopts, #Hc, #Hinv, #Hrlb, #HF⟩ HΦ
  ihave #Hrpc := kvRegs_one ep E γr cid mid $$ Hrpc0
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  ihave #Hau := getRevAu_round γr γf γl γv keys val r $$ [Hinv Hrlb]
  · iframe #
  wp_apply (client_get_end_to_end api [ep] E γr c cid mid ci cd k sl
    (fun σ => iprop(⌜r ≤ σ.rev⌝)) F hsz) $$ [] as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, #Hq⟩ | %Herr)
  · ileft
    ihave Hv := client_get_value_rev E γr c cid mid k F _ m $$ Hq
    icases Hv with ⟨%σ, %Hσ, %Hval, %Hrev⟩
    isplitr
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    rw [Hrev]; exact_mod_cast Hσ
  · iright
    ipureintro; exact Herr

end e2e

end compactkv
end EtcdGrove
end Perennial
