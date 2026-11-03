/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkLeaseRenew.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseRenew
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheckLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 4000000 in
theorem EtcdServer.checkLeaseRenew.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hK : lease.Lease.Keys.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkLeaseRenew.spec (GF := GF) (hG := hG) := by
  intro s E γl ctx cd id n m
  wp_start as ⟨#Hau, #Hlb, #Hlr, #Hpub, #Hmlb, #Hctx, HRD, #Hpool, Htok, %Hbound⟩
  ihave ⟨%st, %cca, #Has, #Hreq, #Hreqb, #Hcca, #HLb⟩ := leaseCheckSetup s E n $$ [$Hau $Hlb $Hpub]
  iunfold isAuthStoreLeaseLb at HLb
  icases HLb with ⟨%ai, %Hai, #HEn, #HRev, #HAdm, #HPut, -⟩
  iunfold srvLessorRd at Hlr
  icases Hlr with ⟨%lp, #Hlf, #Hinv⟩
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave #Hap : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave ⟨⟨%eUE, #HUE, #HUEe⟩, ⟨%eOR, #HOR, #HORe⟩⟩ := leaseCheckErrs $$ Hap
  subst Hai
  (try wp_auto)
  -- `rev := s.AuthStore().Revision()`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HRev as %rev #Hrev
  (try wp_auto)
  -- `if !s.AuthStore().IsAuthEnabled() { return nil }`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HEn $$ [$HRD] as %b ⟨HRD, #Hen⟩
  (try wp_auto)
  cases b with
  | false =>
    (try wp_auto)
    iapply HΦ
    iframe HRD Htok
    isplitl []
    · iapply applyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    ileft; iexact Hen
  | true =>
  (try wp_auto)
  -- `authInfo, err := s.AuthInfoFromCtx(ctx)`
  wp_apply (hAI s _ E.RD E.authMode cca ctx cd) $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hb⟩
  · iframe #
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD Htok Herr
    iintro %h; cases h
  (try wp_auto)
  iunfold authInfoOpt at Ha
  icases Ha with (%Han | ⟨%user, %rev', #Hai0⟩)
  · -- `if authInfo == nil { return auth.ErrUserEmpty }`
    subst Han
    (try wp_auto)
    iapply HΦ
    iframe HRD Htok HUEe
    iintro %h; cases h
  ihave #Hp := authInfoIs_pointsto a user rev' $$ Hai0
  ihave #Hib := infoBoundM_of_ctxBound E.authOn s E _ a user rev' $$ [Hb Hai0]
  · iframe Hai0; iintro %h; iapply Hb $$ %h
  iunfold authInfoIs at Hai0
  icases Hai0 with ⟨%Hann, -, -⟩
  simp only [Hann, decide_false]
  (try wp_auto)
  -- `if s.AuthStore().IsAdminPermitted(authInfo) == nil { return nil }`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HAdm $$ [$Hp $HRD] as %err2 ⟨-, HRD, #Herr2, #Hv⟩
  (try wp_auto)
  rcases err2 with e2 | _
  rotate_left
  · (try wp_auto)
    iapply HΦ
    iframe HRD Htok
    isplitl []
    · iapply applyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    iright
    iexists _
    iframe Hib
    ileft; iexact Hv
  -- `l := s.lessor.Lookup(leaseID)`, a reader of the lessor at the lower bound `m`, its slot
  -- borrowed from the pool for the call (the lease-src plan), its later stripped by the next steps
  iapply fupd_wp
  imod lease.lessorRdPool_borrow γl ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htok]
    with ⟨Hrdo, Hback⟩
  · iframe #; iframe
  imodintro
  (try wp_auto)
  iunfold lease.lessorRdOf at Hrdo
  icases Hrdo with ⟨%lp', #Hpin', Hrd⟩
  ihave #Hinv' := Hinv
  iunfold lease.lessorInv at Hinv'
  icases Hinv' with ⟨-, #Hpin, -, -⟩
  ihave %Heq := lease.lessorPin_agree γl lp lp' $$ [$Hpin $Hpin']
  subst Heq
  (try wp_auto)
  wp_apply (hLk lp γl id m none) $$ [$Hrd] as %l ⟨Hrd, Hl, -⟩
  · iframe Hinv Hmlb
    rw [lease.lookupView_none]; itrivial
  -- the slot back, for the token
  iapply fupd_wp
  imod Hback $$ [Hrd] with Htok
  · iunfold lease.lessorRdOf; iexists lp; iframe Hpin Hrd
  imodintro
  icases Hl with (⟨%Hnull, #Habs⟩ | ⟨#Hlo, #Hlive⟩)
  · -- no lease of `id` at an index no earlier than `m`
    subst Hnull
    (try wp_auto)
    -- `if rev != s.AuthStore().Revision() { return auth.ErrAuthOldRevision }`
    wp_apply (hAS s _) as -
    · iframe #
    (try wp_auto)
    wp_apply HRev as %rev2 -
    (try wp_auto)
    wp_if_destruct
    · iapply HΦ
      iframe HRD Htok
      isplitl []
      · iapply applyErrIs_nil
      iintro %_
      iunfold leaseCheckFrom
      iright
      iexists _
      iframe Hib
      iright
      iunfold leaseKeysVerdictFrom
      ileft; iexact Habs
    · iapply HΦ
      iframe HRD Htok
      iframe HORe
      iintro %h; cases h
  -- `for _, key := range l.Keys() { ... s.AuthStore().IsPutPermitted(authInfo, []byte(key)) ... }`
  ihave #Hlo' := Hlo
  iunfold lease.isLeaseObj at Hlo'
  icases Hlo' with ⟨%Hnn, -, -, -⟩
  simp only [Hnn, decide_false, Bool.not_false]
  (try wp_auto)
  wp_apply (hK γl l id (.reader m)) $$ [Htok] as %sl %ks ⟨Hks, Hpre, Hpost, %Hnd⟩
  · iframe Hlo; rw [lease.keysPre_reader]; iframe Htok Hlive; ipureintro; exact Hbound
  ihave Hpre : iprop(lease.leaseLiveFrom γl m id l ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝)
    $$ [Hpre]
  · rw [← lease.keysPre_reader]; iexact Hpre
  icases Hpre with ⟨-, Htok, -⟩
  ihave #Hkf : lease.leaseKeysFrom γl m id l ks $$ [Hpost]
  · rw [← lease.keysPost_reader]; iexact Hpost
  ihave %Hshort := lease.leaseKeysFrom_short γl m id l ks $$ Hkf
  ihave %Hsll := ownSlice_len _ _ _ $$ Hks
  iunfold permCheck2Lb at HPut
  ihave IH : iprop(∃ (j : w64) (k : GoString),
      "i" ∷ i_ptr ↦ j ∗ "key" ∷ key_ptr ↦ k ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ ∗
      "#Hcls" ∷ [∗list] k ∈ ks.take (sint.nat j),
        auth.permVerdictFrom E.authMode n ⟨user, rev'⟩ k [] .write GoInterface.nil) $$ [i key]
  · iexists W64 0, _
    iframe i key
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for IH
  wp_if_destruct
  · have hjl : (sint.Z j).toNat < ks.length := by unfold sint.nat at Hsll; word
    obtain ⟨kx, Hkx⟩ : ∃ kx, ks[(sint.Z j).toNat]? = some kx := ⟨_, List.getElem?_eq_getElem hjl⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) _ _ kx Hj.1 $$ [Hks] as Hks
    · iframe; ipureintro; exact Hkx
    wp_apply wp_string_to_bytes kx as %bsl ⟨Hb, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    wp_apply (hAS s _) as -
    · iframe #
    (try wp_auto)
    wp_apply HPut $$ [$Hp $Hb $HRD] as %err3 ⟨-, -, HRD, #Herr3, #Hv3⟩
    · ipureintro
      have h1 := Hshort kx (List.mem_of_getElem? Hkx)
      rw [Hbl.1] at h1
      have h3 := Hbl.2
      unfold sint.nat at h1
      word
    cases err3 with
    | nil =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, kx
      iframe
      isplitl []
      · ipureintro; constructor <;> word
      · have hsn : sint.nat (j + W64 1) = sint.nat j + 1 := by unfold sint.nat at *; word
        rw [hsn, List.take_add_one, show ks[sint.nat j]? = some kx from Hkx, Option.toList_some]
        iapply BigSepL.bigSepL_snoc.2
        iframe Hcls
        iexact Hv3
    | ok e3 =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe HRD Htok
      iunfold authApplyErrIs at Herr3
      icases Herr3 with ⟨#Herr3, -⟩
      iframe Herr3
      iintro %h; cases h
  have hall : ks.take (sint.nat j) = ks := by
    apply List.take_of_length_le; unfold sint.nat at *; word
  rw [hall] at *
  -- `if rev != s.AuthStore().Revision() { return auth.ErrAuthOldRevision }`
  wp_apply (hAS s _) as -
  · iframe #
  (try wp_auto)
  wp_apply HRev as %rev2 -
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ
    iframe HRD Htok
    isplitl []
    · iapply applyErrIs_nil
    iintro %_
    iunfold leaseCheckFrom
    iright
    iexists _
    iframe Hib
    iright
    iunfold leaseKeysVerdictFrom
    iright
    iexists l
    iunfold leaseOfKeysVerdictFrom
    iexists ks
    iframe Hkf Hcls
  · iapply HΦ
    iframe HRD Htok
    iframe HORe
    iintro %h; cases h

end proof

end EtcdGrove
end Perennial
