/-
Lean-first (no Rocq counterpart).

The proof of `kubernetes.Client.OptimisticDelete`: the builder from the client's `*kv`
(`kv.Txn`, as linkvtxn's `client_Txn_st`), its comparison, delete and get, then `Commit` as
linkvtxn's `txn_Commit_st` (the transaction `clientTxn`, linkv's on the wire), and the response's
fields (`failure_resps`, `kvFromTxnResponse`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__OptimisticDelete
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.kvFromTxnResponse
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Proof.go_etcd_io.etcd.client.v3.TxnPlain

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

theorem Client.OptimisticDelete.wp_proof
    (wp_OpDelete : OpDelete.spec (GF := GF) (hG := hG)) (wp_OpGet : OpGet.spec (GF := GF) (hG := hG))
    (wp_ModRevision : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (wp_Compare : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (wp_kvFromTxnResponse : kvFromTxnResponse.spec (GF := GF) (hG := hG)) :
    Client.OptimisticDelete.spec (GF := GF) (hG := hG) := by
  intro _ _ kc ms V ci cd key rev opts Q
  wp_start as ⟨#Hcl, #Hone, #Hregs, #Hctx, #Hce, Hau⟩
  wp_auto
  ihave #Hnil0 := optsAt_nil (GF := GF)
  wp_apply wp_OpDelete key slice.nil [] $$ [] as %op #Hop
  · iframe #
    ipureintro
    simp [opDeletePanics, opGetPanics, opFold, opDeleteModel, OpFull.deletePanics,
      OpFull.deleteInit, OpFull.newOp, OpModel.zero]
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  ipersist Hsl2
  wp_auto
  generalize hsl2 : slice.mk sl2 _ _ = tsl
  ihave #Hops : opsAt tsl [opDeleteModel key []] $$ []
  · iunfold opsAt
    iexists _
    iframe Hsl2
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %o %m %Ho %Hm
    rcases i with _ | i
    · cases Ho; cases Hm; iexact Hop
    · simp at Ho
  wp_apply wp_ModRevision key as %c0 #Hc0
  wp_apply wp_Compare c0 _ go!"=" .eq _ (.num rev) $$ [] as %c1 #Hc1
  · iframe #
    ipureintro
    exact ⟨rfl, ⟨rev, Or.inl rfl, rfl⟩⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl3 ⟨Hsl3, -⟩
  ipersist Hsl3
  wp_auto
  generalize hsl3 : slice.mk sl3 _ _ = csl
  ihave #Hcmps : cmpsAt csl [compareM (cmpKeyM .mod key) .eq (.num rev)] $$ []
  · iunfold cmpsAt
    iexists _
    iframe Hsl3
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %c %m %Hc %Hm
    rcases i with _ | i
    · cases Hc; cases Hm; iexact Hc1
    · simp at Hc
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hwo := client.clientWriteOnce_api kc.Client' api _ $$ [Hkvf Hone]
  · iframe #
  wp_auto
  wp_apply (client.v3.kv.wp_Txn api (ms.map client.SrvAt.addr) ci cd) as %t ⟨%tp, %Ht, Hobj, #Hkt⟩
  · iframe #
  subst Ht
  ihave Htwo : client.txnWriteOnce tp (ms.map client.SrvAt.addr) $$ []
  · iunfold client.txnWriteOnce
    iunfold client.writeOnce at Hwo
    iexact Hwo
  (try wp_auto)
  wp_apply (client.v3.txn.wp_If tp (ms.map client.SrvAt.addr) ci cd TxnBuild.empty csl
      [compareM (cmpKeyM .mod key) .eq (.num rev)]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; simp [TxnBuild.empty]
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Then_plain tp (ms.map client.SrvAt.addr) ci cd _ tsl
      [opDeleteModel key []] [.delete (opDeleteModel key [])]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  (try wp_auto)
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  cases hg : opts.GetOnFailure'
  · -- no `GetOnFailure`: no else branch
    ihave Hobj : txnObjAt (GF := GF) tp (ms.map client.SrvAt.addr) ci cd
        ⟨clientTxn [.mod key rev] [.del key] [], true, true, false⟩ $$ [Hobj]
    · iExactEq Hobj
      simp [TxnModel.empty, clientTxn, linkv.cmpOf, compareM, cmpKeyM, clientTOp]
    (try wp_auto)
    wp_apply (txn_Commit_st tp ms ci cd ⟨clientTxn [.mod key rev] [.del key] [], true, true, false⟩
        Q [.mod key rev] [.del key] [] rfl (by simp)) $$ [Hobj Hau Htwo]
      as %resp %err Hout
    · iframe #
      iframe
      done
    icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | ⟨%Herr, #Hke⟩)
    · subst Herr
      obtain ⟨hok, -, hrev, hb⟩ := Hσ
      iunfold txnRespMsg at Hm
      icases Hm with ⟨%Hnn, %h, %rsl, %ps, #Hh, #Hhf, #Hsucc, #Hrs, #Hrsl, #Hms⟩
      iunfold hdrFull at Hhf
      icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
      wp_auto
      rw [hg]
      wp_auto
      iapply HΦ
      ileft
      isplitl []
      · ipureintro; rfl
      iexists σ
      isplitl [HQ]
      · iExactEq HQ
        simp [callRes, linkv.MIn.isWrite, linkv.MOp.isWrite]
      isplitl []
      · ipureintro
        exact ⟨hok, hrev, hb⟩
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      ipureintro; first | rfl | trivial
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => ?_
      wp_auto
      iapply HΦ
      iright
      iunfold kvErr at Hke
      icases Hke with ⟨%Hce, #Hse, #Hcl⟩
      iframe Hse Hcl
      isplitl []
      · ipureintro; exact Herr
      ipureintro; exact Hce
  · -- `GetOnFailure`: the else branch gets the key
    (try wp_auto)
    ihave #Hnil := optsAt_nil (GF := GF)
    wp_apply wp_OpGet key slice.nil [] $$ [] as %op2 #Hop2
    · iframe #
      ipureintro
      unfold opGetPanics opFold OpFull.newOp; simp
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl4 ⟨Hsl4, -⟩
    ipersist Hsl4
    wp_auto
    generalize hsl4 : slice.mk sl4 _ _ = esl
    ihave #Heops : opsAt esl [opGetModel key []] $$ []
    · iunfold opsAt
      iexists _
      iframe Hsl4
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %o %m %Ho %Hm
      rcases i with _ | i
      · cases Ho; cases Hm; iexact Hop2
      · simp at Ho
    wp_apply (client.v3.txn.wp_Else_plain tp (ms.map client.SrvAt.addr) ci cd _ esl
        [opGetModel key []] [.get (opGetModel key [])]) $$ [Hobj] as Hobj
    · iframe #
      iframe Hobj
      ipureintro; exact ⟨rfl, rfl⟩
    (try wp_auto)
    ihave Hobj : txnObjAt (GF := GF) tp (ms.map client.SrvAt.addr) ci cd
        ⟨clientTxn [.mod key rev] [.del key] [.get key], true, true, true⟩ $$ [Hobj]
    · iExactEq Hobj
      simp [TxnModel.empty, clientTxn, linkv.cmpOf, compareM, cmpKeyM, clientTOp]
    (try wp_auto)
    wp_apply (txn_Commit_st tp ms ci cd
        ⟨clientTxn [.mod key rev] [.del key] [.get key], true, true, true⟩
        Q [.mod key rev] [.del key] [.get key] rfl (by simp)) $$ [Hobj Hau Htwo]
      as %resp %err Hout
    · iframe #
      iframe
    icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | ⟨%Herr, #Hke⟩)
    · subst Herr
      obtain ⟨hok, hrel, hrev, hb⟩ := Hσ
      iunfold txnRespMsg at Hm
      icases Hm with ⟨%Hnn, %h, %rsl, %ps, #Hh, #Hhf, #Hsucc, #Hrs, #Hrsl, #Hms⟩
      iunfold hdrFull at Hhf
      icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
      wp_auto
      rw [hg]
      wp_auto
      cases hs : m.succeeded
      · -- the comparison failed: the else branch's get
        rw [hs] at hrel hok
        obtain ⟨rv, more, count, hresps⟩ := failure_resps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int))
          [.mod key rev] [.del key] key m.resps hok.symm hrel
        ihave ⟨%Hpl, #Hmall⟩ := opRespsMsg_getElem ps m.resps $$ Hms
        rw [hresps] at Hpl
        obtain ⟨p0, rfl⟩ : ∃ p0, ps = [p0] := by
          match ps, Hpl with
          | [p0], _ => exact ⟨p0, rfl⟩
        ihave #Hp0 := Hmall $$ %0 %p0 %(OpRespM.range rv (σ.kvs.filter fun v => decide (v.key = key))
          more count) %rfl %(by rw [hresps]; rfl)
        ihave %Hrsll := ownSlice_len _ _ _ $$ Hrsl
        simp only [Bool.not_false]
        wp_auto
        · have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len := by
            have := Hrsll.1
            simp at this
            constructor <;> word
          simp only [Hbnd0, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hrsl] as -
          · iframe Hrsl; ipureintro; rfl
          wp_apply wp_kvFromTxnResponse p0 rv _ more count $$ [] as %kv #Hkv
          · iframe #
          wp_auto
          iapply HΦ
          ileft
          isplitl []
          · ipureintro; rfl
          iexists σ
          isplitl [HQ]
          · iExactEq HQ
            simp [callRes, linkv.MIn.isWrite, linkv.MOp.isWrite]
          isplitl []
          · ipureintro
            exact ⟨hok, hrev, hb⟩
          simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
          iexact Hkv
      · -- the comparison held: no `KV`
        wp_auto
        iapply HΦ
        ileft
        isplitl []
        · ipureintro; rfl
        iexists σ
        isplitl [HQ]
        · iExactEq HQ
          simp [callRes, linkv.MIn.isWrite, linkv.MOp.isWrite]
        isplitl []
        · ipureintro
          exact ⟨(hok.symm.trans hs).symm, hrev, hb⟩
        simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        ipureintro; first | rfl | trivial
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => ?_
      wp_auto
      iapply HΦ
      iright
      iunfold kvErr at Hke
      icases Hke with ⟨%Hce, #Hse, #Hcl⟩
      iframe Hse Hcl
      isplitl []
      · ipureintro; exact Herr
      ipureintro; exact Hce

end proof

end kubernetes
end EtcdGrove
end Perennial
