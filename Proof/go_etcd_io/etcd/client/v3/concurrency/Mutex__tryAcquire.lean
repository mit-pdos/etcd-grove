/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__tryAcquire.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__tryAcquire
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.WithFirstCreate
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

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The state before a transaction has positive create revisions. -/
private theorem txnStates_pos (pfx : GoString) (r : w64) (s s' : List EtcdKv) (wrote : Bool) :
    txnStates (GF := GF) pfx r s s' wrote ⊢ ⌜∀ v ∈ s, 0 < sint.Z v.createRev⌝ := by
  unfold txnStates
  split
  · iintro ⟨#H1, -⟩
    ihave %H := etcdState_revs _ _ _ $$ H1
    ipureintro; intro v hv; exact (H v hv).1
  · iintro #H1
    ihave %H := etcdState_revs _ _ _ $$ H1
    ipureintro; intro v hv; exact (H v hv).1

private theorem txnStates_true (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' true ⊢ □ etcdState r pfx s' := by
  unfold txnStates
  simp only [↓reduceIte]
  iintro ⟨-, #H⟩
  iexact H

private theorem txnStates_false (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' false ⊢ □ etcdState r pfx s := by
  unfold txnStates
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro #H
  iexact H

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.tryAcquire.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hLe : Session.Lease.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hWL : EtcdGrove.WithLease.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hWFC : EtcdGrove.WithFirstCreate.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG)) :
    Mutex.tryAcquire.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx st ctx cs lo
  wp_start as ⟨#Hm, Hst, #Hctx, #Hlo⟩
  ihave #Hm' := Hm
  iunfold isMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmpfx, %Hpfx, #Hsess, #Hcl⟩
  unfold mutexState
  icases Hst with ⟨Hk, Hrv, Hh⟩
  wp_auto
  wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply hLe s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hfmt $Hargs] as %key ⟨Hargs, %Hkey⟩
  case wf =>
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    exact .cons_string _ _ (.cons_other _ _ _ (by simp [go.string, go_etcd_io.etcd.client.v3.LeaseID.ty])
      (by simp [_root_.Perennial.fmt.IsIntType, go.int, go.int64, go.int32, go.int16, go.int8,
        go.uint, go.uint64, go.uint32, go.uint16, go.uint8, go_etcd_io.etcd.client.v3.LeaseID.ty])
      .nil)
  rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at Hkey
  simp only [List.set_cons_succ, List.set_cons_zero] at Hkey
  have Hpk : pfx <+: key := _root_.Perennial.fmt.SprintfOut.str_x_prefix pfx _ _ Hkey
  (try wp_auto)
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hCR key $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num (W64 0)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  wp_apply hLe s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply hWL id $$ [$Hcv] as %f0 #Hf0
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f0])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  (try wp_auto)
  ihave #Hopts : optsAt (GF := GF) _ [withLeaseM id] $$ []
  · unfold optsAt
    iexists [f0]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
    · simp at Hf
  wp_apply hPut key [] _ [withLeaseM id] $$ [$Hcv $Hopts] as %opPut #HopPut
  · ipureintro; exact putOp_not_panics key id
  (try wp_auto)
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_apply hGet key slice.nil [] $$ [$Hcv $Hnil] as %opKey #HopKey
  · ipureintro; exact keyOp_not_panics
  (try wp_auto)
  wp_apply hWFC $$ [$Hcv] as %slf ⟨#Hslf, -⟩
  (try wp_auto)
  wp_apply hGet pfx slf _ $$ [$Hcv $Hslf] as %opOwn #HopOwn
  · ipureintro; exact ownerOp_not_panics pfx
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opKey, opOwn])
  isplitr
  · ipureintro; rfl
  iintro %slE ⟨HslE, -⟩
  ipersist HslE
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opPut, opOwn])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #HKV, -, -, -, -, #HTxn, -, -⟩
  (try wp_auto)
  iunfold isEtcdTxnKV at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, #HElse, #HCommit, -⟩
  -- `wp_apply_raw`: `wp_apply`'s post-processing fails (unknown free variable) on a
  -- continuation whose premise is `B _` with `B` a local
  wp_apply_raw HIf $$ %TxnBuild.empty %(slice.mk slC (W64 (go.arrayLiteralSize [KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Cmp.ty #c1)])) (W64 (go.arrayLiteralSize [KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Cmp.ty #c1)]))) %([compareM (cmpKeyM .create key) .eq (.num (W64 0))] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opPutModel key [] [withLeaseM id], ownerOp pfx] : List OpFull) %([.put key [] id, .get (ownerOp pfx)] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opPut, opOwn]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopPut
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho
        unfold ownerOp; iexact HopOwn
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      simp only [List.map_cons, List.map_nil, putOp_txnOpOf, ownerOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HElse $$ %_ %_ %([keyOp key, ownerOp pfx] : List OpFull) %([.get (keyOp key), .get (ownerOp pfx)] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opKey, opOwn]
      iframe HslE
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho
        unfold keyOp; iexact HopKey
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho
        unfold ownerOp; iexact HopOwn
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl⟩
      simp only [List.map_cons, List.map_nil, keyOp_txnOpOf, ownerOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := acquireTxn pfx key id, cif := true, cthen := true, celse := true } : TxnBuild) (by rfl) $$ HB
  wp_apply HCommit $$ %({ model := acquireTxn pfx key id, cif := true, cthen := true, celse := true } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact acquireTxn_under pfx key id Hpfx Hpk
  ihave #Hres := txnCommitResultTok_result _ _ _ _ _ $$ Hres
  iunfold txnCommitResult at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Hne
    iexists key
    iframe
  subst Heq
  have hm : ({ model := acquireTxn pfx key id, cif := true, cthen := true, celse := true } :
      TxnBuild).model = acquireTxn pfx key id := rfl
  rw [hm]
  ihave %hpos := txnStates_pos pfx r s0 _ _ $$ Hts
  obtain ⟨Hlo_r0, Hr0, Hrmax, Hwf0⟩ := Hrr
  have Hlo_r := Hlo_r0 rfl
  iunfold txnRespAt at Hresp
  icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, #HR, #Hps, %Hlens, #Hops⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hps
  (try wp_auto)
  cases hok : (runTxn r s0 (acquireTxn pfx key id)).1
  · -- the key existed: no write; `Responses[0]` is the get of the key
    obtain ⟨⟨v, hv, hvk⟩, h1, h2, h3⟩ := acquireTxn_else pfx key id r s0 hok
    have hb : (acquireTxn pfx key id).branch false = [.get (keyOp key), .get (ownerOp pfx)] := rfl
    simp only [h2, h1, hok, hb] at Hlens ⊢
    simp only [h3] at Hlens ⊢
    have hok' : (acquireTxn pfx key id).cmps.all (cmpHolds s0) = false := hok
    simp only [acquireTxn] at hok'
    rw [hok']
    (try wp_auto)
    ihave #Hs := txnStates_false pfx r s0 s0 $$ Hts
    ihave %Hrevs := etcdState_revs r pfx s0 $$ Hs
    obtain ⟨p1, hp1⟩ : ∃ p, ps[1]? = some p :=
      ⟨ps[1]'(by simp at Hlens; omega), List.getElem?_eq_getElem _⟩
    obtain ⟨p0, hp0⟩ : ∃ p, ps[0]? = some p :=
      ⟨ps[0]'(by simp at Hlens; omega), List.getElem?_eq_getElem _⟩
    have h0 : sint.Z (W64 0) = 0 := by decide
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
      rw [h0]; have := len_eq_sint _ _ Hlen; simp at Hlens; omega))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) ps _ p0 (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; exact hp0
    ihave #Hop0 := Hops $$ %0 %p0 %(TxnOp.get (keyOp key)) %(TxnOpResult.range (rangeSel s0 (keyOp key)) (rangeIn s0 (keyOp key)).length) %hp0 %rfl %rfl
    iunfold txnOpRespAt at Hop0
    icases Hop0 with ⟨%Hpnn, %u, #Hu, %w, %rr, %Huw, #Hw, %Hrrnn, #Hrr⟩
    subst Huw
    ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p0 w rr $$ [$Hpbi $Hu $Hw]
    · ipureintro; exact Hpnn
    iunfold rangeRespAt at Hrr
    icases Hrr with ⟨%ksl, %kps, %kvs, #HK, #Hkps, #Hkv, %Hokv, -⟩
    obtain rfl := (keyOp_kvs pfx key s0 kvs Hwf0 Hokv).2 v hv hvk
    iunfold kvPtrsAt at Hkv
    icases Hkv with ⟨%Hkl, #Hkv⟩
    obtain ⟨kp, rfl⟩ : ∃ kp, kps = [kp] := by
      match kps, Hkl with
      | [kp], _ => exact ⟨kp, rfl⟩
    ihave #Hkp := Hkv $$ %0 %kp %v %rfl %rfl
    ihave %Hklen := ownSlice_len _ _ _ $$ Hkps
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len by
      rw [h0]; have := len_eq_sint _ _ Hklen; simp at this; omega))]
    wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) [kp] _ kp (by decide) $$ [Hkps] as -
    · iframe Hkps; ipureintro; rfl
    iunfold kvValAt at Hkp
    icases Hkp with ⟨%kks, %kvsl, -, -, #Hcr, -⟩
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists key, v.createRev, r, hdr
    iframe
    iframe Hr
    obtain ⟨hc0, hc1, hc2, -⟩ := Hrevs v hv
    isplitr
    · unfold acquireResp hdrRevAt
      iexists s0, rsl, ps, p1, (rangeIn s0 (ownerOp pfx)).length
      ihave #Hop1 := Hops $$ %1 %p1 %(TxnOp.get (ownerOp pfx)) %(TxnOpResult.range (rangeSel s0 (ownerOp pfx)) (rangeIn s0 (ownerOp pfx)).length) %hp1 %rfl %rfl
      iframe HH HRev Hs HR Hps Hop1
      ipureintro
      exact ⟨Hhdr, ⟨Hwf0, v, hv, hvk, rfl⟩, hp1⟩
    ipureintro
    exact ⟨Hpk, Hlo_r, hc0, Int.le_trans hc1 hc2, Hrmax⟩
  · -- the key was created at `r`
    obtain ⟨h1, h2, h3, hwf', hk'⟩ := acquireTxn_then pfx key id r s0 Hwf0 Hpk hpos hok
    have hb : (acquireTxn pfx key id).branch true = [.put key [] id, .get (ownerOp pfx)] := rfl
    simp only [h2, h1, hok, hb] at Hlens ⊢
    simp only [h3] at Hlens ⊢
    have hok' : (acquireTxn pfx key id).cmps.all (cmpHolds s0) = true := hok
    simp only [acquireTxn] at hok'
    rw [hok']
    (try wp_auto)
    ihave #Hs := txnStates_true pfx r s0 _ $$ Hts
    obtain ⟨p1, hp1⟩ : ∃ p, ps[1]? = some p :=
      ⟨ps[1]'(by simp at Hlens; omega), List.getElem?_eq_getElem _⟩
    ihave #Hop1 := Hops $$ %1 %p1 %(TxnOp.get (ownerOp pfx)) %(TxnOpResult.range (rangeSel (putKv r key [] id s0) (ownerOp pfx)) (rangeIn (putKv r key [] id s0) (ownerOp pfx)).length) %hp1 %rfl %rfl
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists key, r, r, hdr
    iframe
    iframe Hr
    isplitr
    · unfold acquireResp hdrRevAt
      iexists putKv r key [] id s0, rsl, ps, p1, (rangeIn (putKv r key [] id s0) (ownerOp pfx)).length
      iframe HH HRev Hs HR Hps Hop1
      ipureintro
      exact ⟨Hhdr, ⟨hwf', hk'⟩, hp1⟩
    ipureintro
    exact ⟨Hpk, Hlo_r, Hr0, Int.le_refl _, Hrmax⟩

end proof

end concurrency
end EtcdGrove
end Perennial
