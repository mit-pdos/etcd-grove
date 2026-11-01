/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Compact.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Compact
public import Spec.go_etcd_io.etcd.client.v3.OpCompact
public import Spec.go_etcd_io.etcd.client.v3.CompactOp__toRequest
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Compact
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem kv.Compact.wp_proof
    (wp_OpCompact : OpCompact.spec (GF := GF) (hG := hG))
    (wp_toRequest : CompactOp.toRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Compact : retryKVClient.Compact.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Compact.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd rev Hr1 Hcmp
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hrv⟩
  iunfold isKv at Hkv
  icases Hkv with ⟨%ms, #Hkv⟩
  iunfold isKvOf at Hkv
  icases Hkv with ⟨#Hobj, #Hregs, -, %Hm⟩
  obtain ⟨Hns, -, -⟩ := Hm
  iunfold kvObjAt at Hobj
  icases Hobj with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, %Hsc⟩
  -- the members' spec of `Compact`: each member has reached `rev`, in compaction mode
  have hmem : ∀ k (x : SrvAt GF), ms[k]? = some x →
      (iprop(□ kvRevLb γ rev) : IProp GF) ⊢ kvRevLb x.γr.kv rev := fun k x hk =>
    intuitionistically_elim.trans
      (kvRevLb_same γ x.γr.kv (kvSame_symm (Hns x (List.mem_of_getElem? hk))) rev)
  ihave #HC := (BigSepL.bigSepL_intro (Φ := fun _ (x : SrvAt GF) => kvRevLb x.γr.kv rev) hmem) $$ Hrv
  ihave #HR := (BigAndL.bigAndL_intro (Φ := fun _ (x : SrvAt GF) => kvRevLb x.γr.kv rev) hmem) $$ Hrv
  wp_auto
  wp_apply wp_OpCompact rev $$ []
  wp_apply wp_toRequest _ $$ [] as %p ⟨%req, Hreq, %Hrq⟩
  obtain ⟨hrv, hph, hun⟩ := Hrq
  simp only at hrv hph
  ihave Hrun : reqPre conn go!"/etcdserverpb.KV/Compact" (ms.map SrvAt.addr) vs
      (attemptPre conn (GoInterface.ok ci) (GrpcSpec.md (kvCompactSpec ms))
        ⟨req.Revision', req.Physical'⟩ (fun _ => iprop(True))) $$ []
  · iapply reqPre_box
    imodintro
    inext
    rw [hrv, hph]
    iapply (attemptPre_md (Req := pbCompactionRequest) (Rep := pbCompactionResponse) conn
      (GoInterface.ok ci) (kvCompactSpec ms) ⟨rev, false⟩ (fun _ => iprop(True)))
    unfold kvCompactSpec
    iapply (anySpec_intro ms (fun x => etcdCompactSpec x.E x.γr x.cid x.mid) ⟨rev, false⟩
      (fun _ => iprop(True)) (fun x => kvRevLb x.γr.kv rev) (fun x => kvRevLb x.γr.kv rev)
      (fun x hx => by
        iintro ⟨#Hx, -⟩
        unfold etcdCompactSpec
        isplitr
        · ipureintro
          refine ⟨Hr1, rfl, ?_⟩
          rw [(Hns x hx).2.2.2.2.2]; exact Hcmp
        iframe Hx
        iintro %m -
        itrivial))
    iframe HC HR
  wp_apply wp_retry_Compact rkv conn (ms.map SrvAt.addr) (GrpcSpec.md (kvCompactSpec ms))
      (fun _ => iprop(True)) ci cd p req sl vs $$ [Hreq Hrun] as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    isplitl []
    · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcCompact ms) $$ Hregs
    ipureintro; exact hun
  iunfold compactCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, -⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    ileft
    isplitl []
    · ipureintro; rfl
    iexists m
    iexact Hm
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      ihave #Hcl' := Hclw $$ Hcl
      iapply HΦ
      iright
      unfold kvErr
      iframe #
      ipureintro
      exact ⟨⟨(Herr'.2 (by simp)).1, rfl⟩, (Herr'.2 (by simp)).2⟩

end proof

end EtcdGrove
end Perennial
