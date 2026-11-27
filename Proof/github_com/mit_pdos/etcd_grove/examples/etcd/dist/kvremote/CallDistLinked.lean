/-
Lean-first (no Rocq counterpart).

**`Call` across machines, linked over N2's drafts** (P9): the laws of `ClientCallDistLaws.lean` proved
from the drafts (`dist/ClientViewDist.lean`: `KV_Put_dist`, `KV_Get_dist`, `KV_Delete_dist`,
`Txn_Commit_dist`, hypotheses `svc`'s) and the client's `kv.Txn` (`cl.Put` is `(*Client).Put`
through the embedded `KV`, the field `kvClientAt` names, as `client_Put_kv`); then `Call_dist_holds`:
`Call_dist.spec` from the drafts, `Call_dist.wp_proof` at those laws and txnlin's linked helpers.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.ClientCallDistLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVDeleteDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.CallDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Link
public import Spec.go_etcd_io.etcd.client.v3.kv__Txn
public import Proof.go_etcd_io.etcd.client.v3.KeyOps
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client go_etcd_io.etcd.api.v3
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

theorem client_Put_dist_law_holds (hPut : KV_Put_dist.spec (GF := GF) (hG := hG)) : client_Put_dist.law (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ ci cd key val sl Q hsz hauth
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (hPut cl api eps V Γ ci cd key val sl [] Q hauth) $$ [Hlt Hau] as %resp %err ⟨Hlt, Hout⟩
  · iframe Hlt
    iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      unfold opPutModel OpFull.putPanics opFold OpFull.putInit OpFull.newOp OpModel.zero
      simp
    isplitl [Hau]
    · iunfold kvOpAu1 at Hau
      iunfold kvAu1 at Hau
      iExactEq Hau; rfl
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs, -⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro; exact ⟨Hs.1, Hs.2.2.1⟩
  · iright
    ipureintro; exact Herr.1

/-- A get at revision `0` reads the current state's key-values. -/
theorem at_readRev_zero_kvs (σ : KVState) : (σ.at (σ.readRev (W64 0))).kvs = σ.kvs := by
  rw [show σ.readRev (W64 0) = σ.rev by simp [KVState.readRev], KVState.at_rev]
  rfl

theorem client_Get_dist_law_holds (hGet : KV_Get_dist.spec (GF := GF) (hG := hG)) : client_Get_dist.law (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ ci cd key sl Q hsz
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hopts' := optsAt_res sl [] iprop(True) $$ Hopts
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (hGet cl api eps V Γ ci cd key sl [] iprop(True) Q) $$ [Hlt]
    as %resp %err ⟨Hlt, -, Hout⟩
  · iframe Hlt
    iframe #
    isplitl []
    · itrivial
    isplitl []
    · rw [show (opGetModel key []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opGetPanics opFold OpFull.newOp; simp
    isplitl []
    · imodintro
      icases Hau with (%h | #h)
      · ileft; ipureintro; exact h
      · iright
        isplitl []
        · ipureintro; rfl
        iunfold kvReadAu at h
        iunfold kvAu at h
        iexact h
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro
    obtain ⟨-, hsel, -, hrev, hb, -⟩ := Hs
    rw [at_readRev_zero_kvs] at hsel
    exact ⟨(srvRangeOk_getKey key _ _ _ hsel).1, hrev, hb⟩
  · iright
    ipureintro; exact Herr.1

theorem client_List_dist_law_holds (hGet : KV_Get_dist.spec (GF := GF) (hG := hG)) : client_List_dist.law (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ ci cd sl Q hsz
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, #Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  ihave #Hopts' := optsAt_res sl [withRangeM listTo] iprop(True) $$ Hopts
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (hGet cl api eps V Γ ci cd listFrom sl [withRangeM listTo] iprop(True) Q) $$ [Hlt]
    as %resp %err ⟨Hlt, -, Hout⟩
  · iframe Hlt
    iframe #
    isplitl []
    · itrivial
    isplitl []
    · rw [show (opGetModel listFrom [withRangeM listTo]).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      first
        | rfl
        | (refine ⟨?_, rfl⟩; simp [opGetPanics, op_simps])
    isplitl []
    · imodintro
      icases Hau with (%h | #h)
      · ileft; ipureintro; exact h
      · iright
        isplitl []
        · ipureintro; rfl
        iunfold kvReadAu at h
        iunfold kvAu at h
        iexact h
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro
    obtain ⟨-, hsel, -, hrev, hb, -⟩ := Hs
    rw [show OpModel.zero.rev = W64 0 from rfl, at_readRev_zero_kvs] at hsel
    exact ⟨(srvRangeOk_list _ _ _ hsel).1, hrev, hb⟩
  · iright
    ipureintro; exact Herr.1

theorem client_Delete_dist_law_holds (hDel : KV_Delete_dist.spec (GF := GF) (hG := hG)) : client_Delete_dist.law (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ ci cd key sl Q hsz hauth
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce, #Hopts, Hau⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨-, -, #Hkvf, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Delete_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (hDel cl api eps V Γ ci cd key sl [] Q hauth) $$ [Hlt Hau] as %resp %err ⟨Hlt, Hout⟩
  · iframe Hlt
    iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, ?_⟩
      · simp [op_simps, opDeletePanics, opGetPanics, OpFull.deletePanics]
      · simp [op_simps, deleteWireOf, txn.deleteOpOf]
    isplitl [Hau]
    · iunfold kvOpAu1 at Hau
      iunfold kvAu1 at Hau
      iExactEq Hau; rfl
    ipureintro; exact hsz
  iapply HΦ
  iframe Hlt
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro
    obtain ⟨hdel, -, hrev, hb, -⟩ := Hs
    exact ⟨hdel, hrev, hb⟩
  · iright
    ipureintro; exact Herr.1

theorem client_Txn_dist_law_holds (wp_Txn : kv.Txn.spec (GF := GF) (hG := hG)) : client_Txn_dist.law (GF := GF) (hG := hG) := by
  intro π cl api eps V Γ ci cd
  iintro %Φ ⟨#Pc, Hlt, #Hkc, #Hctx, #Hce⟩ HΦ
  ihave #Hkc' := Hkc
  iunfold kvClientAt at Hkc'
  icases Hkc' with ⟨#Hcl, -, #Hkvf, -⟩
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api', #Hkvf', #Hkv⟩, -⟩
  ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hkvf Hkvf'
  have hapi : api' = api := by
    have h := ((interface_mkOk_inj _ _ _ _).1 Hag).2
    exact (go.intoVal_inj h).symm
  subst hapi
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Txn_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (wp_Txn api' eps ci cd) as %t ⟨%tp, %Ht, Hobj, #Hkt⟩
  · iframe #
  iapply HΦ
  iframe Hlt
  iexists tp
  iframe Hobj Hkt
  ipureintro; exact Ht

theorem txn_Commit_dist_law_holds (hCommit : Txn_Commit_dist.spec (GF := GF) (hG := hG)) : txn_Commit_dist.law (GF := GF) (hG := hG) := by
  intro π cl api tp eps V Γ ci cd b Q cs t e hb hne hsz hauth
  iintro %Φ ⟨#Pc, Hlt, #Hkc, Hobj, #Hkt, Hau⟩ HΦ
  have hw : txnWireOf b.model = linkv.txnOf cs t e := by rw [hb, txnWireOf_clientTxn]
  have hp : TxnModel.plain b.model := by rw [hb]; exact clientTxn_plain cs t e
  have hin : txnModelIn (txnWireOf b.model) := by rw [hw]; exact txnModelIn_txnOf cs t e
  have hro := txnReadonly_txnOf cs t e
  have hser := txnSerializable_txnOf cs t e hne
  wp_apply (hCommit cl api tp eps V Γ ci cd b Q hauth) $$ [Hlt Hobj Hau]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe Hlt Hobj
    iframe #
    isplitl []
    · ipureintro; exact ⟨hp, hin⟩
    isplitl [Hau]; rotate_left
    · ipureintro; exact hsz
    unfold callUpd
    rw [hw]
    cases hwr : (linkv.MIn.txn cs t e).isWrite
    · simp only [hwr, Bool.not_false] at hro
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hau with (%h | #h)
      · ileft; ipureintro; exact ⟨hro, h⟩
      · iright; ileft
        isplitl []
        · ipureintro; exact ⟨hro, hser⟩
        iunfold kvReadAu at h
        iunfold kvAu at h
        iexact h
    · simp only [hwr, Bool.not_true] at hro
      simp only [↓reduceIte]
      iright; iright
      isplitl []
      · ipureintro; exact ⟨hro, linkv.txnPlain_txnOf cs t e, txnNoZeroEnd_txnOf cs t e⟩
      iunfold kvOpAu1 at Hau
      iunfold kvAu1 at Hau
      iExactEq Hau; rfl
  iapply HΦ
  iframe Hlt
  rw [hw]
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hs, -⟩ | %Herr)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    obtain ⟨hok, hrel, hrev, hb', -, -⟩ := Hs
    iexists m, σ
    iframe Hm
    unfold callRes
    cases hwr : (linkv.MIn.txn cs t e).isWrite
    · simp only [hwr, Bool.not_false] at hro
      simp only [hro, hser, Bool.false_eq_true, ↓reduceIte] at hrev ⊢
      iframe HQ
      ipureintro; exact ⟨hok, hrel, hrev, hb'⟩
    · simp only [hwr, Bool.not_true] at hro
      simp only [hro, Bool.false_eq_true, ↓reduceIte] at hrev ⊢
      iframe HQ
      ipureintro
      refine ⟨hok, hrel, ?_, hb'⟩
      rw [hrev, kvOpStep_txnOf_eq]
      rfl
  · iright
    ipureintro; exact Herr.1

end laws

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [NaInvG GF]

/-- **`Call` across machines, over N2's drafts**: `Call_dist.spec` from `KV_Put_dist`,
`KV_Get_dist`, `KV_Delete_dist` and `Txn_Commit_dist` at `svc` (`Get_dist` serves both the get and
the list), the laws above, and txnlin's and the client's linked helpers. -/
theorem Call_dist_holds (hPut : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], KV_Put_dist.spec (GF := GF) (hG := hG))
    (hGet : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], KV_Get_dist.spec (GF := GF) (hG := hG))
    (hDel : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], KV_Delete_dist.spec (GF := GF) (hG := hG))
    (hCommit : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], Txn_Commit_dist.spec (GF := GF) (hG := hG)) :
    Call_dist.spec (GF := GF) (hG := hG) :=
  Call_dist.wp_proof context.wp_WithTimeoutBackground context.wp_ErrAny wp_vrOf wp_kvsFrom
    wp_withKVs v3.wp_WithRange wp_cmpsFor wp_opsOf wp_thenOf wp_elseOf wp_txnRes wp_withRes
    client.v3.txn.wp_If client.v3.txn.wp_Then client.v3.txn.wp_Else
    (client_Get_dist_law_holds hGet) (client_List_dist_law_holds hGet)
    (client_Put_dist_law_holds hPut) (client_Delete_dist_law_holds hDel)
    (client_Txn_dist_law_holds client.v3.kv.wp_Txn) (txn_Commit_dist_law_holds hCommit)

end linked

end etcd_txnlin
end EtcdGrove
end Perennial
