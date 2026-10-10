/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Lock.lean`. Lean-first (no Rocq
counterpart).

`tryAcquire`'s owner get lists one key, the smallest create revision (`ownerOp_kvs`): if it is
`myRev`, the mutex holds the lock at the transaction's revision. Otherwise the owner was created
before `myRev` (and after `0`: `etcdState_revs`), so `waitDeletes(myRev - 1)` is called with a
positive bound; its state at `R0` has no key created before `myRev`, and the final `Get(myKey)` at
`R ≥ R0` either misses the key (`ErrSessionExpired`, `etcdAbsent`) or finds it (`lock_final`:
locked, or re-created). On the error paths `Unlock(client.Ctx())`'s result is dropped.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Lock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__tryAcquire
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Unlock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.waitDeletes
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.Lock.wp_proof
    (wp_tryAcquire : Mutex.tryAcquire.spec (GF := GF) (hG := hG))
    (wp_GetResponseRange : ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (wp_Client : Session.Client.spec (GF := GF) (hG := hG))
    (wp_waitDeletes : waitDeletes.spec (GF := GF) (hG := hG))
    (wp_Ctx : Client.Ctx.spec (GF := GF) (hG := hG))
    (wp_Unlock : Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Mutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx st ctx cs lo
  wp_start as ⟨#Hm, Hst, #Hctx, #Hcc, #Hlo⟩
  wp_auto
  wp_apply wp_tryAcquire m s γ client id pfx st ctx cs lo $$ [$Hm $Hst $Hctx $Hlo]
    as %resp %err Hres
  ihave #Hm' := Hm
  iunfold isMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmpfx, %Hpfx, #Hsess, #Hcl⟩
  icases Hres with (⟨%Hne, %key0, Hst⟩ | ⟨%Hnil, %key, %rev, %r, %hdr, Hst, #Hr, #Hacq, %Hp⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact Hne
    iexists _
    iexact Hst
  subst Hnil
  wp_auto
  iunfold acquireResp at Hacq
  icases Hacq with ⟨%s0, %rsl, %ps, %p, %n, #HH, #Hhdr, #Hs0, %Hwf, #HR, #Hrsl, %Hp1, #Hop⟩
  iunfold mutexState at Hst
  icases Hst with ⟨HmyKey, HmyRev, Hmhdr⟩
  ihave %Hlen := ownSlice_len $$ Hrsl
  have Hlen1 : 1 < ps.length := by
    rcases Nat.lt_or_ge 1 ps.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at Hp1
      cases Hp1
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z rsl.len by word)]
  icases ownSlice_elem_acc (sint.Z (W64 1)) p rsl DFrac.discard ps (by word) (by simpa using Hp1)
    $$ Hrsl with ⟨#Hpe, -⟩
  wp_auto
  iunfold txnOpRespAt at Hop
  icases Hop with ⟨%Hpnn, %u, #Hu, %w, %rr, %Hueq, #Hw, %Hrr, #Hrange⟩
  subst Hueq
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_apply wp_GetResponseRange p w rr $$ [$Hpb $Hu $Hw]
  · ipureintro; exact Hpnn
  iunfold rangeRespAt at Hrange
  icases Hrange with ⟨%ksl, %kps, %kvs, #Hksl, #Hkps, #Hkvs, %Hkok, -⟩
  wp_auto
  obtain ⟨ow, rfl, How, Hmin⟩ := ownerOp_kvs pfx key rev s0 kvs Hpfx Hwf.1 Hwf.2 Hkok
  iunfold kvPtrsAt at Hkvs
  icases Hkvs with ⟨%Hkl, #Hkv⟩
  ihave %Hksl := ownSlice_len $$ Hkps
  obtain ⟨kp, rfl⟩ : ∃ kp, kps = [kp] := by
    match kps, Hkl with
    | [kp], _ => exact ⟨kp, rfl⟩
  rw [show decide (ksl.len = W64 0) = false by simp at Hksl; simp; word]
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len by simp at Hksl; word)]
  icases ownSlice_elem_acc (sint.Z (W64 0)) kp ksl DFrac.discard [kp] (by word) (by simp)
    $$ Hkps with ⟨#Hkpe, -⟩
  ihave #Hov := Hkv $$ %0 %kp %ow %rfl %rfl
  iunfold kvValAt at Hov
  icases Hov with ⟨%okeySl, %ovalSl, -, -, #Hocr, -⟩
  wp_auto
  wp_if_destruct
  · -- the owner is `myKey`: locked
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, _, r, hdr
    iframe Hhdr Hr
    isplitl [HmyKey HmyRev Hmhdr]
    · unfold mutexState; iframe
    isplitr
    · ileft
      unfold lockedAt
      iexists s0
      iframe Hs0
      ipureintro
      exact ⟨Hwf.2, Hmin⟩
    ipureintro; exact ⟨Hp.1, Hp.2.1⟩
  ihave %Hrevs := etcdState_revs r pfx s0 $$ Hs0
  have Hlt : sint.Z ow.createRev < sint.Z rev := by
    obtain ⟨v, hv, -, hvc⟩ := Hwf.2
    have h1 := Hmin v hv
    rw [hvc] at h1
    have h2 : sint.Z ow.createRev ≠ sint.Z rev := fun h => Hif (by word)
    omega
  have Hpos := (Hrevs ow How).1
  have Hrev1 : 0 < sint.Z (rev - W64 1) := by word
  wp_apply wp_Client s γ client id $$ [$Hsess]
  wp_apply wp_waitDeletes ctx cs client pfx (rev - W64 1) r $$ [$Hcl $Hctx $Hcc $Hr]
    as %werr Hwd
  · ipureintro; exact ⟨Hpfx, Hrev1⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #Hkvf, -, #Hctxf, #Hcctx, #HKV, -, -, -⟩
  icases Hwd with (%Hwne | ⟨%Hwnil, %R0, %sw, #HR0, #Hsw, %Hw⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, werr = GoInterface.ok e := by
      cases werr with
      | nil => exact absurd rfl Hwne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_apply wp_Ctx client (GoInterface.ok cctx) $$ [$Hctxf]
    ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
    · iapply etcdReached_zero
    wp_apply wp_Unlock m s γ client id pfx ⟨key, rev, st.hdr⟩ cctx ccs (W64 0)
      $$ [$Hm HmyKey HmyRev Hmhdr $Hcctx $H0] as %uerr Hu
    · unfold mutexState; iframe
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact Hwne
    icases Hu with (⟨-, %R, Hst', -⟩ | ⟨-, Hst', -⟩ | ⟨-, Hst'⟩) <;> iexists _ <;> iexact Hst'
  subst Hwnil
  wp_auto
  ihave #Hopts : optsAt (GF := GF) slice.nil ([] : List (OpFull → OpFull)) $$ []
  · iapply optsAt_nil
  iunfold isEtcdKV at HKV
  ihave #HG := HKV $$ %ctx %cs %key %slice.nil %([] : List (OpFull → OpFull)) %R0
  wp_apply HG $$ [] as %gresp %gerr #Hgres
  · iframe Hctx Hopts HR0
    ipureintro
    exact ⟨keyOp_not_panics, (keyOp_t key).1⟩
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_apply wp_Ctx client (GoInterface.ok cctx) $$ [$Hctxf]
    ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
    · iapply etcdReached_zero
    wp_apply wp_Unlock m s γ client id pfx ⟨key, rev, st.hdr⟩ cctx ccs (W64 0)
      $$ [$Hm HmyKey HmyRev Hmhdr $Hcctx $H0] as %uerr Hu
    · unfold mutexState; iframe
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact Hgne
    icases Hu with (⟨-, %R, Hst', -⟩ | ⟨-, Hst', -⟩ | ⟨-, Hst'⟩) <;> iexists _ <;> iexact Hst'
  subst Hgnil
  have HkT : (opGetModel key []).t = W64 1 ∧ (opGetModel key []).key = key ∧
      (opGetModel key []).base.rangeEnd = [] ∧ (opGetModel key []).base.rev = W64 0 ∧
      (opGetModel key []).base.serializable = false := keyOp_t key
  have HRle' : sint.Z R0 ≤ sint.Z R := HRle.1 HkT.2.2.2.2
  have HkP : (opGetModel key []).isPrefixGet pfx = false := keyOp_isPrefixGet pfx key
  rw [ite_eq_right (c := (opGetModel key []).isPrefixGet pfx = true) (by rw [HkP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (opGetModel key []).base.rev = W64 0 ∧
      KeyRangeUnder pfx (opGetModel key []).key (opGetModel key []).base.rangeEnd from
    ⟨HkT.2.2.2.1, by rw [HkT.2.1, HkT.2.2.1]; exact keyRangeUnder_key pfx key Hp.1⟩)]
  icases Hgr with ⟨%s', %gsl, %gps, %gkvs, #Hs', %Hwf', #Hgsl, #Hgps, #Hgkvs, %Hgok⟩
  wp_auto
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, -⟩
  ihave %Hgsl := ownSlice_len $$ Hgps
  obtain ⟨Hkabs, Hkpres⟩ := keyOp_kvs pfx key s' gkvs Hwf' Hgok
  have HlR : sint.Z lo ≤ sint.Z R := by have := Hw.1; omega
  wp_if_destruct
  · -- no key-value: the key is gone, `ErrSessionExpired`
    have Hnil : gkvs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hgl, Hgsl.1, Hif]; rfl
    ihave Hci : (concurrencyInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hci with ⟨-, ⟨%eSE, #HeSE⟩, -⟩
    wp_auto
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr
      iframe HeSE
      ipureintro; intro h; cases h
    iexists ⟨key, rev, st.hdr⟩, R
    isplitl [HmyKey HmyRev Hmhdr]
    · unfold mutexState; iframe
    iframe HRR
    isplitr
    · unfold etcdAbsent
      iexists s'
      iframe Hs'
      ipureintro
      intro v hv hk
      have := Hkpres v hv hk
      rw [Hnil] at this
      cases this
    ipureintro; exact ⟨Hp.1, HlR⟩
  -- the key is present: locked, or re-created
  have Hpres : ∃ v ∈ s', v.key = key := by
    rcases Classical.em (∃ v ∈ s', v.key = key) with h | h
    · exact h
    · have h' : gkvs = [] := Hkabs (fun v hv hk => h ⟨v, hv, hk⟩)
      rw [h'] at Hgl
      exfalso; apply Hif
      have : sint.nat gsl.len = 0 := by rw [← Hgsl.1, Hgl]; rfl
      word
  ihave %Hfin := lock_final pfx key rev r R0 R sw s' Hp.2.2.1 Hp.2.2.2.1 Hw.1 HRle' Hw.2 Hpres
    $$ [$Hsw $Hs']
  iunfold getRespRev at HgRev
  icases HgRev with ⟨%ghdr, #Hgh, %Hghnn, #HghR⟩
  wp_auto
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists key, rev, R, ghdr
  isplitl [HmyKey HmyRev Hmhdr]
  · unfold mutexState; iframe
  isplitr
  · unfold hdrRevAt; iframe HghR; ipureintro; exact Hghnn
  iframe HRR
  isplitr
  · rcases Hfin with Hl | Hrc
    · ileft; unfold lockedAt; iexists s'; iframe Hs'; ipureintro; exact Hl
    · iright; unfold keyRecreated; iexists s'; iframe Hs'; ipureintro; exact Hrc
  ipureintro; exact ⟨Hp.1, HlR⟩

end proof

end concurrency
end EtcdGrove
end Perennial
