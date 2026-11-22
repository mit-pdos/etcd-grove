/-
Proof of `Spec/.../schema/membershipBackend__MustDeleteMemberFromBackend.lean`: `BackendMemberKey`, the
backend's `BatchTx`, `LockInsideApply` (the caller's critical-section contract: its hook's triple, then
its update), `UnsafeDelete(Members, key)`, `UnsafePut(MembersRemoved, key, "removed")` (both into hook
buckets: nothing the readers see changes) and the deferred `Unlock`, which gives the part back idle.
Lean-first. Until 2026-11-22 (prove-ps2-members) a trust-boundary axiom (names-only; D43 M5b′, 2026-10-26).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustDeleteMemberFromBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.BackendMemberKey
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MemberBkts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.membershipBackend.MustDeleteMemberFromBackend.wp_proof
    (hKey : schema.BackendMemberKey.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.membershipBackend.MustDeleteMemberFromBackend.spec (GF := GF) (hG := hG) := by
  intro mb lg d P f Pre Q Post S bk id W hS hbm hbmr hm hmr
  wp_start as ⟨#Hbe, #Hlgf, %Hlg, #Hhk, %Hf, Hcs, Hwt, Hrt, #HB, Hrb⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bm, #HM, -⟩, -, ⟨%bmr, #HMR, -⟩, -⟩
  ihave #Hbm := schema.members_isBucket hID hName hSafe bm $$ [$Hpkg $HM]
  ihave #Hbmr := schema.membersRemoved_isBucket hID hName hSafe bmr $$ [$Hpkg $HMR]
  icases backend.isBackend_b d.γB d.P W P d.be $$ HB with ⟨%t', %rt, %db, %lg', -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  -- the two buckets' parameters
  have hRBm : d.P.RB mvcc.membersBI.name = true := schema.kb_RB d _ (by decide)
  have hRBr : d.P.RB mvcc.membersRemovedBI.name = true := schema.kb_RB d _ (by decide)
  have hSBm : d.P.SB mvcc.membersBI.name = false := schema.kb_SB d _ (by decide)
  have hSBr : d.P.SB mvcc.membersRemovedBI.name = false := schema.kb_SB d _ (by decide)
  have hHBm : d.P.HB mvcc.membersBI.name = true := schema.kb_HB d _ (by decide)
  have hHBr : d.P.HB mvcc.membersRemovedBI.name = true := schema.kb_HB d _ (by decide)
  have hne : mvcc.membersBI.name ≠ mvcc.membersRemovedBI.name := by decide
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `mkey := BackendMemberKey(id)`
  wp_apply (hKey id) $$ [$Hpkg] as %ks Hks
  ipersist Hks
  (try wp_auto)
  wp_apply (hBT d.γB d.P W P d.be) $$ [$Hbpkg $HB] as %t #Ht
  (try wp_auto)
  -- `LockInsideApply()`: the hook's triple from the caller's contract
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨Hpre, Hrun, Hcl⟩
  have hrun : mvcc.api.hookRun (GF := GF) P f Pre Q =
      iprop(□ {{ P ∗ Pre }} (App (Val #f) (Val #())) {{ RET #(); Q }}) := by
    unfold mvcc.api.hookRun; exact if_neg Hf
  rw [hrun]
  iunfold apply.bkRT at Hrt
  icases Hrt with ⟨Hrd, Ho⟩
  wp_apply (hLI d.γB d.P W P d.be t backend.rdOpen DFrac.discard f Pre Q)
    $$ [$Hbpkg $HB $Ht $Ho $Hhk $Hpre Hrun] as ⟨%st, Hl, %Hfree, HW, HQ, Ho, -⟩
  · iright
    iframe Hrun
    ipureintro; exact Hf
  ihave HPP := Hcl $$ HQ
  imod HPP with ⟨HP, HPost⟩
  (try wp_auto)
  have hlim := HPw.2.2.1
  have hp0 := Hfree.2.1
  -- `UnsafeDelete(Members, mkey)`
  icases schema.rbPart_focus d.γB S bk mvcc.membersBI.name (hS _ (Or.inl rfl)) $$ Hrb
    with ⟨Hm, Hback⟩
  icases backend.batchLocked_rbPart d.γB d.P d.be st (· = mvcc.membersBI.name) bk $$ [$Hl $Hm]
    with ⟨Hl, Hm, %Hag⟩
  have hSm : st.S.lookup mvcc.membersBI.name = bk.lookup mvcc.membersBI.name := by
    have h := Hag _ rfl
    rw [backend.rbData_lookup, hRBm] at h
    simpa using h
  ihave Hm : backend.rbPut d.γB d.P mvcc.membersBI.name st.S $$ [Hm]
  · rw [schema.rbPut_tracked _ _ _ _ hRBm]
    iapply (backend.rbPart_congr _ _ (backend.rbData d.P st.S) bk (fun n hn => Hag n hn)).2 $$ Hm
  ihave Hdlp := backend.dlPut_other (GF := GF) d.γB d.P mvcc.membersBI.name hSBm
  have hDel' := hDel d.γB d.P W P d.be t st bm mvcc.membersBI ks (types.idStr id) DFrac.discard true
    hm (by omega) (schema.kb_hk d _ _ (by decide))
    (fun h => by unfold backend.fkKey at h; exact absurd h.1 (by decide))
    (fun h => absurd h (by rw [hSBm]; decide)) false false (_hkc := by decide)
  simp only [↓reduceIte] at hDel'
  wp_apply hDel' $$ [$Hbpkg $HB $Ht $Hl $Hbm $Hks $Hm $Hdlp] as ⟨Hl, -, Hm, -⟩
  -- the part of `members`, at the entry deleted
  have hl1 : ∀ n, n = mvcc.membersBI.name →
      (backend.rbData d.P (st.del mvcc.membersBI (types.idStr id) false).S).lookup n =
        (bk.insert mvcc.membersBI.name
          (((bk.lookup mvcc.membersBI.name).getD ∅).delete (types.idStr id))).lookup n := by
    intro n hn
    subst hn
    rw [backend.rbData_lookup, if_pos hRBm]
    show (st.S.insert _ ((backend.bktOf st.S _).delete _)).lookup _ = _
    rw [GMap.lookup_insert, GMap.lookup_insert]
    unfold backend.bktOf
    rw [hSm]
  ihave Hm : backend.rbPart d.γB (· = mvcc.membersBI.name) (bk.insert mvcc.membersBI.name
      (((bk.lookup mvcc.membersBI.name).getD ∅).delete (types.idStr id))) $$ [Hm]
  · iapply (backend.rbPart_congr _ _ _ _ hl1).1
    rw [← schema.rbPut_tracked (GF := GF) d.γB d.P mvcc.membersBI.name _ hRBm]
    iExactEq Hm
    rfl
  ihave Hrb := Hback $$ %(((bk.lookup mvcc.membersBI.name).getD ∅).delete (types.idStr id)) Hm
  -- `UnsafePut(MembersRemoved, mkey, []byte("removed"))`
  (try wp_auto)
  wp_apply wp_string_to_bytes (go!"removed" : GoString) as %vs ⟨Hvs, -⟩
  ipersist Hvs
  (try wp_auto)
  let st1 := st.del mvcc.membersBI (types.idStr id) false
  let bk1 := bk.insert mvcc.membersBI.name
    (((bk.lookup mvcc.membersBI.name).getD ∅).delete (types.idStr id))
  have hp1 : sint.Z st1.pend = sint.Z st.pend + 1 := by
    show sint.Z (st.pend + W64 1) = _; word
  icases schema.rbPart_focus d.γB S bk1 mvcc.membersRemovedBI.name (hS _ (Or.inr rfl)) $$ Hrb
    with ⟨Hr, Hback2⟩
  icases backend.batchLocked_rbPart d.γB d.P d.be st1 (· = mvcc.membersRemovedBI.name) bk1 $$ [$Hl $Hr]
    with ⟨Hl, Hr, %Hag2⟩
  have hSr : st1.S.lookup mvcc.membersRemovedBI.name = bk1.lookup mvcc.membersRemovedBI.name := by
    have h := Hag2 _ rfl
    rw [backend.rbData_lookup, hRBr] at h
    simpa using h
  ihave Hr : backend.rbPut d.γB d.P mvcc.membersRemovedBI.name st1.S $$ [Hr]
  · rw [schema.rbPut_tracked _ _ _ _ hRBr]
    iapply (backend.rbPart_congr _ _ (backend.rbData d.P st1.S) bk1 (fun n hn => Hag2 n hn)).2 $$ Hr
  ihave Hhkp := backend.hkPut_of_not_HK (GF := GF) d.γB d.P mvcc.membersRemovedBI.name (types.idStr id)
    st1.S (schema.kb_HK d _ _ (by decide))
  ihave Hfkp := backend.fkPut_other (GF := GF) d.γB mvcc.membersRemovedBI.name (types.idStr id)
    (fun h => by unfold backend.fkKey at h; exact absurd h.1 (by decide))
  have hlen0 : 0 < (types.idStr id).length := by
    have := types.hexNatF_ne_nil (id.toNat + 1) id.toNat (by omega)
    unfold types.idStr
    exact List.length_pos_iff.mpr this
  have hlen1 : (types.idStr id).length ≤ backend.maxKeySize := by
    have := types.idStr_length id
    unfold backend.maxKeySize; omega
  wp_apply (hUP d.γB d.P W P d.be t st1 bmr mvcc.membersRemovedBI ks vs (types.idStr id)
      (go!"removed" : GoString) hmr hlen0 hlen1 (by omega) (fun h => absurd h (by rw [hSBr]; decide))
      (fun h => by unfold backend.fkKey at h; exact absurd h.1 (by decide)) false false
      (_hkc := by decide))
    $$ [$Hbpkg $HB $Ht $Hl $Hbmr $Hks $Hvs $Hhkp $Hr $Hfkp] as ⟨Hl, -, Hr, -⟩
  -- the part of `members_removed`, at the entry put
  let st2 := st1.put mvcc.membersRemovedBI (types.idStr id) (go!"removed" : GoString) false false
  have hl2 : ∀ n, n = mvcc.membersRemovedBI.name →
      (backend.rbData d.P st2.S).lookup n =
        (bk1.insert mvcc.membersRemovedBI.name
          (((bk1.lookup mvcc.membersRemovedBI.name).getD ∅).insert (types.idStr id)
            (go!"removed" : GoString))).lookup n := by
    intro n hn
    subst hn
    rw [backend.rbData_lookup, if_pos hRBr]
    show (st1.S.insert _ ((backend.bktOf st1.S _).insert _ _)).lookup _ = _
    rw [GMap.lookup_insert, GMap.lookup_insert]
    unfold backend.bktOf
    rw [hSr]
  ihave Hr : backend.rbPart d.γB (· = mvcc.membersRemovedBI.name) (bk1.insert mvcc.membersRemovedBI.name
      (((bk1.lookup mvcc.membersRemovedBI.name).getD ∅).insert (types.idStr id)
        (go!"removed" : GoString))) $$ [Hr]
  · iapply (backend.rbPart_congr _ _ _ _ hl2).1
    rw [← schema.rbPut_tracked (GF := GF) d.γB d.P mvcc.membersRemovedBI.name _ hRBr]
    iExactEq Hr
    rfl
  ihave Hrb := Hback2 $$ %(((bk1.lookup mvcc.membersRemovedBI.name).getD ∅).insert (types.idStr id)
    (go!"removed" : GoString)) Hr
  (try wp_auto)
  -- the deferred `Unlock()`: both writes into hook buckets, nothing the readers see changed
  have hvs : backend.viewSame d.P st2 :=
    mvcc.viewSame_putHB HPw hHBr hmr (mvcc.viewSame_del hHBm (backend.viewSame_of_freeOk Hfree))
  have hroom : sint.Z st2.pend + d.P.hookMax < 2 ^ 58 := by
    have h2 := HPw.2.2.2.1
    have : sint.Z st2.pend = sint.Z st.pend + 2 := by
      show sint.Z (st.pend + W64 1 + W64 1) = _; word
    omega
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin d.γB d.P _ hvs
  iunfold apply.bkWT at Hwt
  wp_apply (backend.batchTxBuffered.Unlock.spec_free hUL d.γB d.P W P d.be t st2 Post S _
      Hfree.2.2.2.2.1 hroom) $$ [$Hbpkg $HB $Ht $Hl $Hwt $Hrb HW HP HPost] as ⟨HPost, Hrb⟩
  · ileft; iframe HW HP HPost Hth; ipureintro; exact Hnw
  (try wp_auto)
  iapply HΦ
  iframe HPost
  isplitl [Hrd Ho]
  · iunfold apply.bkRT; iframe Hrd Ho
  iExactEq Hrb
  rfl

end proof

end EtcdGrove
end Perennial
