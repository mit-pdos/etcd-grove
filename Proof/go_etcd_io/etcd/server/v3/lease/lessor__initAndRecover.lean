/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__initAndRecover.lean`. Lean-first (no Rocq
counterpart); the lease-expiry plan's S1 (2026-11-04).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__initAndRecover
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Init
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateLeaseBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.container.heap.Init_
public import Proof.go_etcd_io.etcd.server.v3.lease.QueueLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.initAndRecover.wp_proof
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hCLB : schema.UnsafeCreateLeaseBucket.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hGA : schema.MustUnsafeGetAllLeases.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hLen : lease.LeaseQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG))
    (hInit : heap.Init_.spec (GF := GF) (hG := hG))
    (hNI : lease.LeaseExpiredNotifier.Init.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG)) :
    lease.lessor.initAndRecover.spec (GF := GF) (hG := hG) := by
  intro lp lm np h hx mt γB P W Pk be qo S r recs hS hLp hrecs
  wp_start as ⟨Hb, Hlm, HM, #Hmt, Hnp, Hnot, Hh, Hhq, #HB, Ho, Htoks, Hrb⟩
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨-, -, -, #Hfor, -⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hspkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bk, #HL, -⟩⟩
  ihave #Hbk := mvcc.lease_isBucket hID hName hSafe bk $$ [$Hspkg $HL]
  icases backend.isBackend_b γB P W Pk be $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  obtain ⟨hhas, hRB, hhk⟩ := hLp
  wp_auto
  wp_apply (hBT γB P W Pk be) $$ [$HB] as %t #Ht
  (try wp_auto)
  wp_apply (hLO γB P W Pk be t qo) $$ [$HB $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  (try wp_auto)
  -- the lease bucket's part apart from the rest
  have hsplit : ∀ n, S n ↔ (n = mvcc.leaseName ∨ (S n ∧ n ≠ mvcc.leaseName)) := by
    intro n; by_cases hn : n = mvcc.leaseName
    · subst hn; exact ⟨fun _ => Or.inl rfl, fun _ => hS⟩
    · exact ⟨fun h => Or.inr ⟨h, hn⟩, fun h => h.elim (fun e => absurd e hn) And.left⟩
  ihave Hrb := (backend.rbPart_set γB S _ r hsplit).1 $$ Hrb
  icases (backend.rbPart_split γB (· = mvcc.leaseName) (fun n => S n ∧ n ≠ mvcc.leaseName) r
    (fun n h1 h2 => h2.2 h1)).1 $$ Hrb with ⟨HrbL, HrbR⟩
  icases backend.batchLocked_rbPart γB P be st (· = mvcc.leaseName) r $$ [$Hl $HrbL]
    with ⟨Hl, HrbL, %Hag⟩
  have hagL : (backend.rbData P st.S).lookup mvcc.leaseName = r.lookup mvcc.leaseName := Hag _ rfl
  have hrp : backend.rbPut (GF := GF) γB P mvcc.leaseBI.name st.S =
      backend.rbPart γB (· = mvcc.leaseName) (backend.rbData P st.S) := by
    unfold backend.rbPut; rw [show mvcc.leaseBI.name = mvcc.leaseName from rfl, hRB]; rfl
  ihave HrbL : backend.rbPut γB P mvcc.leaseBI.name st.S $$ [HrbL]
  · rw [hrp]
    iapply (backend.rbPart_congr γB _ (backend.rbData P st.S) r (fun n hn => Hag n hn)).2 $$ HrbL
  have hlim := HPw.2.2.1
  have hpend : sint.Z st.pend + 1 < 2 ^ 58 := by have := Hfree.2.1; omega
  -- `UnsafeCreateLeaseBucket(tx)`: the bucket present
  wp_apply (hCLB ⟨go.GoType.PointerType backend.batchTxBuffered.ty, #t⟩
      iprop(backend.batchLocked γB P be st ∗ backend.rbPut γB P mvcc.leaseBI.name st.S)
      iprop(backend.batchLocked γB P be (st.create mvcc.leaseBI) ∗
        backend.rbPut γB P mvcc.leaseBI.name (st.create mvcc.leaseBI).S))
    $$ [Hl HrbL] as ⟨Hl, HrbL⟩
  · iframe Hl HrbL
    iintro !> %b0 %Φ' !> ⟨⟨Hl, HrbL⟩, #HL0⟩ HΦ'
    icombine HL HL0 gives %Hb0
    subst Hb0
    wp_apply (hCB γB P W Pk be t st bk mvcc.leaseBI hhas (by decide) (by decide) hpend)
      $$ [$HB $Ht $Hl $Hbk $HrbL] as ⟨Hl, HrbL⟩
    iapply HΦ'; iframe
  (try wp_auto)
  -- the bucket's contents: the part's
  have hSr : st.S.lookup mvcc.leaseName = r.lookup mvcc.leaseName := by
    rw [← hagL, backend.rbData_lookup, hRB]; rfl
  have hS1 : (st.create mvcc.leaseBI).S.lookup mvcc.leaseName =
      some ((r.lookup mvcc.leaseName).getD ∅) := by
    show (if st.S.lookup mvcc.leaseName = none then st.S.insert mvcc.leaseName ∅ else st.S).lookup
      mvcc.leaseName = _
    rw [← hSr]
    rcases hc : st.S.lookup mvcc.leaseName with _ | b
    · simp
    · simp [hc]
  have hbk1 : backend.bktOf (st.create mvcc.leaseBI).S mvcc.leaseBI.name =
      (r.lookup mvcc.leaseName).getD ∅ := by
    unfold backend.bktOf; rw [show mvcc.leaseBI.name = mvcc.leaseName from rfl, hS1]; rfl
  -- `MustUnsafeGetAllLeases(tx)`: the records
  wp_apply (hGA γB P W Pk be t (st.create mvcc.leaseBI) bk mvcc.leaseBI recs
      (by rw [hbk1]; exact hrecs)) $$ [$HB $Ht $Hl $HL $Hbk] as %s ⟨Hl, %ps, Hs, %Hps, Hlps⟩
  (try wp_auto)
  -- the part back, at the bucket present
  have hr1 : ∀ n, n = mvcc.leaseName →
      (backend.rbData P (st.create mvcc.leaseBI).S).lookup n =
        (r.insert mvcc.leaseName ((r.lookup mvcc.leaseName).getD ∅)).lookup n := by
    rintro n rfl
    rw [backend.rbData_lookup, hRB, GMap.lookup_insert]; exact hS1
  ihave HrbL : backend.rbPart γB (· = mvcc.leaseName)
      (r.insert mvcc.leaseName ((r.lookup mvcc.leaseName).getD ∅)) $$ [HrbL]
  · ihave HrbL : backend.rbPart γB (· = mvcc.leaseName)
        (backend.rbData P (st.create mvcc.leaseBI).S) $$ [HrbL]
    · have hrp' : backend.rbPut (GF := GF) γB P mvcc.leaseBI.name (st.create mvcc.leaseBI).S =
          backend.rbPart γB (· = mvcc.leaseName) (backend.rbData P (st.create mvcc.leaseBI).S) := by
        unfold backend.rbPut; rw [show mvcc.leaseBI.name = mvcc.leaseName from rfl, hRB]; rfl
      rw [← hrp']; iExactEq HrbL; rfl
    iapply (backend.rbPart_congr γB _ _ _ hr1).1 $$ HrbL
  ihave HrbR : backend.rbPart γB (fun n => S n ∧ n ≠ mvcc.leaseName)
      (r.insert mvcc.leaseName ((r.lookup mvcc.leaseName).getD ∅)) $$ [HrbR]
  · iapply (backend.rbPart_congr γB _ _ _ (fun n hn => by
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hn.2)])).1 $$ HrbR
  ihave Hrb := (backend.rbPart_split γB (· = mvcc.leaseName) (fun n => S n ∧ n ≠ mvcc.leaseName) _
    (fun n h1 h2 => h2.2 h1)).2 $$ [$HrbL $HrbR]
  ihave Hrb := (backend.rbPart_set γB S _ _ hsplit).2 $$ Hrb
  -- `tx.Unlock()`: nothing the readers see changed; the part idle
  icases (ownToks_add 1 1 γB.wb).1 $$ Htoks with ⟨Hwb1, Hwb2⟩
  ihave Hwb1 : backend.wbTok γB $$ [Hwb1]
  · iunfold backend.wbTok; iexact Hwb1
  ihave Hwb2 : backend.wbTok γB $$ [Hwb2]
  · iunfold backend.wbTok; iexact Hwb2
  have hvs := mvcc.viewSame_create mvcc.leaseBI (backend.viewSame_of_freeOk Hfree)
  have hroom : sint.Z (st.create mvcc.leaseBI).pend + P.hookMax < 2 ^ 58 := by
    have h1 := HPw.2.2.1
    have h2 := HPw.2.2.2.1
    have h3 := Hfree.2.1
    have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
    show sint.Z (st.pend + W64 1) + P.hookMax < 2 ^ 58
    omega
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin γB P _ hvs
  wp_apply (hUL γB P W Pk be t (st.create mvcc.leaseBI) iprop(True) S
      (r.insert mvcc.leaseName ((r.lookup mvcc.leaseName).getD ∅)) Hfree.2.2.2.2 hroom)
    $$ [$HB $Ht $Hl $Hwb1 $Hrb HW HPk] as ⟨-, Hrb⟩
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  -- the loop: one lease per record
  ihave Hlps : iprop([∗list] p; x ∈ ps.drop 0; recs.drop 0,
      ∃ v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease, p ↦ v ∗
        ⌜v.ID' = x.1 ∧ v.TTL' = x.2.1 ∧ v.RemainingTTL' = x.2.2⌝) $$ [Hlps]
  · simp only [List.drop_zero]; iexact Hlps
  ihave %Hslen := ownSlice_len s _ _ $$ Hs
  imod preceipt_zero (GF := GF) with #Hr0
  ihave IH : iprop(∃ (n : w64) (lv : Loc) (ls : List Loc),
      "Hi" ∷ i_ptr ↦ n ∗ "Hlpb" ∷ lpb_ptr ↦ lv ∗ "HM" ∷ lm ↦$ recMap ((recs.take (sint.nat n)).zip ls) ∗
      "Hrl" ∷ ([∗list] p ∈ (recs.take (sint.nat n)).zip ls, recLease mt p.1 p.2) ∗
      "#Hr" ∷ ⧖ (sint.nat n) ∗
      "Hlps" ∷ ([∗list] p; x ∈ ps.drop (sint.nat n); recs.drop (sint.nat n),
        ∃ v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease, p ↦ v ∗
          ⌜v.ID' = x.1 ∧ v.TTL' = x.2.1 ∧ v.RemainingTTL' = x.2.2⌝) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.len ∧ ls.length = sint.nat n⌝)
      $$ [i lpb HM Hlps]
  · iexists W64 0, _, []
    have h0 : sint.nat (W64 0) = 0 := by word
    rw [h0]
    simp only [List.take_zero, List.zip_nil_left, recMapFrom, List.foldl_nil]
    iframe i lpb HM Hlps Hr0
    isplitr
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by rw [Hslen.1]; word
    have Hlt' : sint.nat n < recs.length := by rw [← Hps]; exact Hlt
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self]
    have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hb1 : 0 ≤ sint.Z (n + W64 1) ∧ sint.Z (n + W64 1) ≤ sint.Z s.len := by
      constructor <;> word
    wp_apply wp_load_slice_index s (sint.Z n) ps (DFrac.own 1) (ps[sint.nat n]'Hlt) Hn.1
      $$ [Hs] as Hs
    · iframe; ipureintro
      rw [show (sint.Z n).toNat = sint.nat n by word]; exact List.getElem?_eq_getElem Hlt
    rw [List.drop_eq_getElem_cons Hlt, List.drop_eq_getElem_cons Hlt']
    icases Hlps with ⟨⟨%v, Hv, %Hvx⟩, Hlps⟩
    iStructNamedPrefix Hv "p"
    (try wp_auto)
    -- `if lpb.TTL < le.minLeaseTTL { lpb.TTL = le.minLeaseTTL }`
    wp_join iprop(le_ptr ↦ lp ∗ lpb_ptr ↦ (ps[sint.nat n]'Hlt) ∗
        structFieldRef go_etcd_io.etcd.server.v3.lease.leasepb.Lease go!"TTL" (ps[sint.nat n]'Hlt) ↦
          grantTTL mt v.TTL') with [le Hlpb pTTL] as ⟨le, Hlpb, pTTL⟩
    · (try wp_auto)
      unfold grantTTL; rw [if_pos (by assumption)]
      iframe le Hlpb
      iexact pTTL
    · unfold grantTTL; rw [if_neg (by assumption)]
      iframe le Hlpb
      iexact pTTL
    wp_apply +noauto wp_map_make1 (K := LeaseItem) (V := Unit) as %sm Hsm
    wp_raise_receipt Hr
    wp_apply chan.wp_make1 (V := Unit) as %c %γc ⟨#Hch, -, Hown⟩
    (try wp_auto)
    irename «$r0» => Hl
    generalize «$r0_ptr» = l at *
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
    iStructNamedPrefix Hl "l"
    wp_apply (wp_mapInsert LeaseID.ty lm _ v.ID' l) $$ HM as HM
    wp_for_post
    iframe
    iexists n + W64 1, _, ls ++ [l]
    have htk : recs.take (sint.nat n + 1) = recs.take (sint.nat n) ++ [recs[sint.nat n]'Hlt'] :=
      List.take_succ_eq_append_getElem Hlt'
    have hlen : (recs.take (sint.nat n)).length = ls.length := by
      rw [List.length_take, Hn.2.2]; omega
    have hz : (recs.take (sint.nat n + 1)).zip (ls ++ [l]) =
        (recs.take (sint.nat n)).zip ls ++ [(recs[sint.nat n]'Hlt', l)] := by
      rw [htk, List.zip_append hlen]; rfl
    rw [h1, hz]
    have hM : recMap ((recs.take (sint.nat n)).zip ls ++ [(recs[sint.nat n]'Hlt', l)]) =
        (recMap ((recs.take (sint.nat n)).zip ls)).insert v.ID' l := by
      simp only [recMapFrom, List.foldl_append, List.foldl_cons, List.foldl_nil, Hvx.1]
    rw [hM]
    iframe Hi HM Hr Hlpb Hlps
    isplitl [Hrl lID lttl lremainingTTL lexpiryMu lexpiry lmu litemSet lrevokec Hsm Hch Hown]
    · iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
      iframe Hrl
      iunfold recLease
      simp only [← Hvx.1, ← Hvx.2.1, ← Hvx.2.2]
      iframe lID lttl lremainingTTL lexpiryMu lexpiry lmu
      isplitr
      · ipureintro; exact Hnn
      isplitl [litemSet Hsm]
      · iexists sm; iframe
      iexists c; iframe lrevokec
      iunfold revokeCloser
      iexists γc; iframe Hch Hown
    ipureintro
    refine ⟨hb1.1, hb1.2, by simp [Hn.2.2]⟩
  · have hnl : sint.nat n = recs.length := by rw [← Hps, Hslen.1]; word
    rw [hnl, List.take_of_length_le (Nat.le_refl _)]
    (try wp_auto)
    -- `le.leaseExpiredNotifier.Init()`
    wp_apply (hNI np) $$ [$Hnot] as Hnot
    -- `heap.Init(&le.leaseCheckpointHeap)`
    ihave #Hheap : isPkgInit (PROP := IProp GF) pkg_id.container.heap $$ []
    · iPkgInit
    ihave #Hiface := queue_heapIface hLen hLess hSwap hPush (lF go!"leaseCheckpointHeap" lp)
      $$ Hpkg
    wp_apply (hInit (Loc × w64) (interface.mk (go.GoType.PointerType LeaseQueue.ty)
        #(lF go!"leaseCheckpointHeap" lp)) (queueHeap (lF go!"leaseCheckpointHeap" lp)) queueElem hx)
      $$ [$Hheap $Hiface Hh Hhq] as ⟨%ys, Hys, -⟩
    · iunfold queueHeap; iexists h; iframe
    iunfold queueHeap at Hys
    icases Hys with ⟨%h', Hh, Hhq⟩
    -- `le.b.ForceCommit()`
    ihave #Hcr := backend.commitReq_true (GF := GF) γB P Pk be
    wp_apply (hFC γB P W Pk be qo iprop(True) iprop(True)) $$ [$HB $Ho $Hwb2 $Hcr] as ⟨Ho, -⟩
    iapply HΦ
    iexists ls, h', ys
    iframe
    isplitr
    · ipureintro; rw [Hn.2.2, hnl]
    rw [← hnl]; iexact Hr

end proof

end EtcdGrove
end Perennial
