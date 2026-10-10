/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__TryLock.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__TryLock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__tryAcquire
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

private theorem len_eq_sint (n : Nat) (x : w64) (h : n = sint.nat x ∧ 0 ≤ sint.Z x) :
    (n : Int) = sint.Z x := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  simp only [sint.nat, sint.Z] at *
  omega

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.TryLock.wp_proof (hTA : Mutex.tryAcquire.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hCl : Session.Client.spec (GF := GF) (hG := hG)) :
    Mutex.TryLock.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx st ctx cs lo
  wp_start as ⟨#Hm, Hst, #Hctx, #Hlo⟩
  wp_auto
  wp_apply hTA m s γ client id pfx st ctx cs lo $$ [$Hm $Hst $Hctx $Hlo] as %resp %err Hr
  icases Hr with (⟨%Hne, %key, Hst⟩ | ⟨%Heq, %key, %rev, %r, %hdr, Hst, #Hr, #Hacq, %Hp⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright; iright
    iframe
    ipureintro; exact Hne
  subst Heq
  wp_auto
  ihave #Hacq' := Hacq
  iunfold acquireResp at Hacq'
  icases Hacq' with ⟨%s0, %rsl, %ps, %p, %n, #HH, #Hhdr, #Hs0, %Hwf, #HR, #Hps, %Hp1, #Hop⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hps
  have hl2 : 2 ≤ ps.length := by
    have := (List.getElem?_eq_some_iff.1 Hp1).1; omega
  have h1 : sint.Z (W64 1) = 1 := by decide
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z rsl.len by
    rw [h1]; have := len_eq_sint _ _ Hlen; omega))]
  wp_apply wp_load_slice_index rsl (sint.Z (W64 1)) ps _ p (by decide) $$ [Hps] as -
  · iframe Hps; ipureintro; exact Hp1
  iunfold txnOpRespAt at Hop
  icases Hop with ⟨%Hpnn, %u, #Hu, %w, %rr, %Huw, #Hw, %Hrrnn, #Hrr⟩
  subst Huw
  ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_apply hGRR p w rr $$ [$Hpbi $Hu $Hw]
  · ipureintro; exact Hpnn
  iunfold rangeRespAt at Hrr
  icases Hrr with ⟨%ksl, %kps, %kvs, #HK, #Hkps, #Hkv, %Hok, -⟩
  ihave #Hm' := Hm
  iunfold isMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmpfx, %Hpfx, #Hsess, #Hcl⟩
  obtain ⟨w0, rfl, hw0, hmin⟩ := ownerOp_kvs pfx key rev s0 kvs Hpfx Hwf.1 Hwf.2 Hok
  iunfold kvPtrsAt at Hkv
  icases Hkv with ⟨%Hkl, #Hkv⟩
  obtain ⟨kp, rfl⟩ : ∃ kp, kps = [kp] := by
    match kps, Hkl with
    | [kp], _ => exact ⟨kp, rfl⟩
  ihave #Hkp := Hkv $$ %0 %kp %w0 %rfl %rfl
  ihave %Hklen := ownSlice_len _ _ _ $$ Hkps
  have hk1 : sint.Z ksl.len = 1 := by
    have := len_eq_sint _ _ Hklen; simp at this; omega
  have hkne : ksl.len ≠ W64 0 := by intro h; rw [h] at hk1; exact absurd hk1 (by decide)
  unfold mutexState
  icases Hst with ⟨Hk, Hrv, Hh⟩
  wp_auto
  rw [decide_eq_false hkne]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len by
    rw [hk1]; decide))]
  wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) [kp] _ kp (by decide) $$ [Hkps] as -
  · iframe Hkps; ipureintro; rfl
  iunfold kvValAt at Hkp
  icases Hkp with ⟨%kks, %kvsl, -, -, #Hcr, -⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, w0.createRev, r, hdr
    iframe
    iframe Hhdr Hr
    isplitr
    · unfold lockedAt
      iexists s0
      iframe Hs0
      ipureintro
      exact ⟨Hwf.2, hmin⟩
    ipureintro
    exact ⟨Hp.1, Hp.2.1⟩
  wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
  iunfold isEtcdMutexClient at Hcl
  icases Hcl with ⟨%kv, %wt, %cctx, %ccs, #HKV, -, -, -, -, -, #HDel, -⟩
  wp_auto
  ihave #Hnil := optsAt_nil (GF := GF)
  iunfold isEtcdDeleteKV at HDel
  wp_apply HDel $$ %ctx %cs %key %slice.nil %([] : List (OpFull → OpFull)) %r [$Hctx $Hnil $Hr] as %dresp %derr #Hd
  · ipureintro
    refine ⟨deleteOp_not_panics key, ?_⟩
    rw [(deleteOp_fields key).1, (deleteOp_fields key).2]
    exact keyRangeUnder_key pfx key Hp.1
  iunfold deleteResult at Hd
  icases Hd with (%Hne | ⟨%Heq, %r', %s', #Hr', %Hd, #Hts⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, derr = GoInterface.ok e := by
      cases derr with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright; iright
    isplitr
    · ipureintro; exact Hne
    iexists ⟨key, rev, st.hdr⟩
    iframe
  subst Heq
  ihave #Habs := deleteTxn_absent pfx key r' s' $$ Hts
  ihave Hci : (concurrencyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨⟨%eL, #HeL⟩, -, -⟩
  wp_auto
  iapply HΦ
  iright; ileft
  isplitr
  · unfold isPkgErr
    iframe HeL
    ipureintro; simp
  iexists key, r'
  unfold MutexSt.released
  iframe
  iframe Hr' Habs
  ipureintro
  exact ⟨Hp.1, by omega⟩

end proof

end concurrency
end EtcdGrove
end Perennial
