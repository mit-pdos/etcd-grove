/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__acquire.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__acquire
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitSession
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__leaseID
public import Spec.go_etcd_io.etcd.client.v3.LeaseValue
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Perennial.Proof.errors
public import Spec.google_golang_org.grpc.status.FromError
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingGetLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

private theorem len_eq_sint (n : Nat) (x : w64) (h : n = sint.nat x ∧ 0 ≤ sint.Z x) :
    (n : Int) = sint.Z x := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  simp only [sint.nat, sint.Z] at *
  omega

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.acquire.wp_proof
    (hWS : leasingKV.waitSession.spec (GF := GF) (hG := hG))
    (hLV : EtcdGrove.LeaseValue.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hLID : leasingKV.leaseID.spec (GF := GF) (hG := hG))
    (hWL : EtcdGrove.WithLease.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hFE : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    leasingKV.acquire.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key opv o lo
  wp_start as ⟨#Hlkv, Hrd, #Hctx, #Hop, #Hlo, %Ho⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hclf, #Hkvf, #Hpfxf, #Hctxf,
    #Hcancelf, #Hoslf, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #Hctx' : iprop(context.isContextDef ctx cs) $$ [Hctx]
  · iexact Hctx
  unfold context.isContextDef
  iNamed Hctx'
  wp_auto
  ipersist lkv
  ipersist op
  ipersist key
  ipersist ctx
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave HI : iprop("Hrd" ∷ lkvReader lkv γ pfx) $$ [Hrd]
  · iexact Hrd
  wp_for HI
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_apply HErrU as %err0 Herr0
  cases err0 with
  | ok e =>
    try wp_auto
    simp only [intoVal_eq_iff, Bool.false_eq_true, decide_False_any, decide_True_any,
      ite_true, ite_false]
    wp_auto
    rw [if_neg (by simp)]
    icases Herr0 with ⟨#HPD, #Hclosed⟩
    ihave #HErrD := HErr $$ %Broadcast.Done
    wp_apply HErrD $$ [$Hclosed] as %err2 %Herr2
    iapply HΦ
    iframe
    ileft
    ipureintro; exact ⟨Herr2, rfl⟩
  | nil =>
  try wp_auto
  simp only [intoVal_eq_iff, Bool.false_eq_true, decide_False_any, decide_True_any,
    ite_true, ite_false]
  wp_auto
  wp_apply hWS lkv γ pfx ctx cs $$ [$Hpkg $Hlkv $Hrd $Hctx] as %err1 ⟨Hrd, Hws⟩
  icases Hws with (%Hne1 | ⟨%Heq1, Hready⟩)
  · obtain ⟨e1, rfl⟩ : ∃ e, err1 = GoInterface.ok e := by
      cases err1 with
      | nil => exact absurd rfl Hne1
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    ileft
    ipureintro; exact ⟨Hne1, rfl⟩
  subst Heq1
  iunfold sessionReadyQ at Hready
  icases Hready with ⟨#Hsr, #Hlcr⟩
  wp_auto
  wp_apply hLV key $$ [$Hcv] as %lc0 #Hlc0
  try wp_auto
  -- the else-operations: `op`, `OpGet(pfx + key)`
  ihave #Hnil := concurrency.optsAt_nil (GF := GF)
  wp_apply hGet (pfx ++ key) slice.nil [] $$ [$Hcv $Hnil] as %opL #HopL
  · ipureintro; exact concurrency.keyOp_not_panics
  wp_apply wp_slice_literal (l := [opv, opL])
  isplitr
  · ipureintro; rfl
  iintro %slE ⟨HslE, -⟩
  ipersist HslE
  (try wp_auto)
  -- the then-operations: `op`, `OpPut(pfx + key, "", WithLease(leaseID()))`
  wp_apply hLID lkv γ pfx $$ [$Hpkg $Hlkv $Hrd $Hsr] as %id ⟨Hrd, %Hid⟩
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
  wp_apply hPut (pfx ++ key) [] _ [withLeaseM id] $$ [$Hcv $Hopts] as %opP #HopP
  · ipureintro; exact leasePut_not_panics _ id
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opv, opP])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  -- the comparisons
  wp_apply hCR (pfx ++ key) $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num (W64 0)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  wp_apply hCmp lc0 _ go!"=" .eq _ (.num (W64 0)) $$ [$Hcv $Hlc0] as %c2 #Hc2
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1, c2])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  (try wp_auto)
  -- the builder
  iunfold isEtcdTxnKVO at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpecO at HBs
  icases HBs with ⟨#HIf, #HThen, #HElse, #HCommit⟩
  have hlk : key ≠ pfx ++ key := by
    intro h
    have := congrArg List.length h
    simp only [List.length_append] at this
    exact Hpfx (List.length_eq_zero_iff.1 (by omega))
  wp_apply_raw HIf $$ %TxnBuild.empty %_
      %([compareM (cmpKeyM .create (pfx ++ key)) .eq (.num (W64 0)),
         compareM (cmpKeyM .lease key) .eq (.num (W64 0))] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1, c2]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm
        subst Hc Hmm; iexact Hc2
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  have hTops : ([o, opPutModel (pfx ++ key) [] [withLeaseM id]] : List OpFull).map txnOpOf =
      ([.get o, .put (pfx ++ key) [] id] : List TxnOp).map some := by
    simp [Ho.1, leasePut_txnOpOf]
  have hEops : ([o, opGetModel (pfx ++ key) []] : List OpFull).map txnOpOf =
      ([.get o, .get (opGetModel (pfx ++ key) [])] : List TxnOp).map some := by
    simp [Ho.1, keyGet_txnOpOf]
  ihave #HTat := opsAt_leaves (GF := GF) _ _ _ hTops $$ []
  · unfold opsAt
    iexists [opv, opP]
    iframe HslT
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %oo %Hv %Ho'
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho'; subst Hv Ho'; iexact Hop
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hv Ho'
      subst Hv Ho'; iexact HopP
    · simp at Hv
  ihave #HEat := opsAt_leaves (GF := GF) _ _ _ hEops $$ []
  · unfold opsAt
    iexists [opv, opL]
    iframe HslE
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %oo %Hv %Ho'
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho'; subst Hv Ho'; iexact Hop
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hv Ho'
      subst Hv Ho'; iexact HopL
    · simp at Hv
  wp_apply_raw HThen $$ %_ %_ %_ %([.get o, .put (pfx ++ key) [] id] : List TxnOp) [$HB $HTat]
  · ipureintro
    exact ⟨txnOps_leaves _ _ hTops, rfl, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HElse $$ %_ %_ %_ %([.get o, .get (opGetModel (pfx ++ key) [])] : List TxnOp) [$HB $HEat]
  · ipureintro
    exact ⟨txnOps_leaves _ _ hEops, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ (TxnBuild.mk (acquireTxn key (pfx ++ key) id o) true true true) (by rfl) $$ HB
  wp_apply HCommit $$ %_ %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact TxnModel.under_nil _
  iunfold txnCommitResultO at Hres
  icases Hres with (⟨%Hne, %Hce⟩ | ⟨%Heq, Hok⟩)
  · -- an error: `errors.As`, then `status.FromError`
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
    · iPkgInit
    obtain ⟨Hleaf, Htyped⟩ := Hce e rfl
    ihave #Htree := errors.isErrorTree_leaf (GF := GF) e Hleaf Htyped
    wp_apply errors.wp_As (T' := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError)
        (T := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) (· = GoInterface.ok e)
        (GoInterface.ok e) _ _ $$ [$Herrs $Htree $serverErr] as %b %v' Hse
    · ipureintro; rfl
    cases b
    · wp_auto
      ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
      · iPkgInit
      wp_apply hFE (GoInterface.ok e) $$ [$Hst] as %sv %okv #HCode
      (try wp_auto)
      cases okv
      · wp_auto
        wp_for_post
        iframe
      · wp_auto
        wp_apply HCode as %c
        (try wp_auto)
        by_cases hc : c = W32 14
        · subst hc
          simp only [decide_eq_self_any, Bool.not_true]
          wp_auto
          wp_for_post
          iframe
        · simp only [decide_eq_false hc, Bool.not_false]
          wp_auto
          wp_for_post
          iapply HΦ
          iframe
          ileft
          ipureintro; exact ⟨Hne, rfl⟩
    · wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ileft
      ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  have hm : (TxnBuild.mk (acquireTxn key (pfx ++ key) id o) true true true).model =
      acquireTxn key (pfx ++ key) id o := rfl
  rw [hm]
  iunfold txnCommitOk at Hok
  icases Hok with ⟨%r, %s, %hm, %Hrev, Hresp, #Hr, %Hfacts, #Hts⟩
  obtain ⟨Hlo_r0, Hr0, Hrmax, Hwf⟩ := Hfacts
  have Hlo_r := Hlo_r0 (acquireTxn_linearizable _ _ _ _)
  have Hko := Ho.2.1
  rcases acquireTxn_run key (pfx ++ key) id r o s with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- the lease key was created: `Then` ran
    rw [h4]
    simp only [h1, h2, h3, TxnModel.branch, ite_true]
    simp only [acquireTxn]
    iunfold txnRespOwn at Hresp
    icases Hresp with ⟨%hdr, %rsl, %ps, #HH, #Hhdr, HS, #HR, #Hps, Hops⟩
    icases txnOpsRespOwn_len2 $$ Hops with ⟨%p0, %p1, %Hpseq, Hops⟩
    subst Hpseq
    icases txnOpsRespOwn_two $$ Hops with ⟨Hop0, -⟩
    icases (txnOpRespOwn_get p0 o _ _).1 $$ Hop0 with ⟨%Hp0, %w, %rr, #Hw0, #Hrr0, %Hrr, Hrr0o⟩
    icases txnStates_wrote $$ Hts with ⟨#Hs0, #Hs1⟩
    obtain ⟨Hwf', nv, Hnv, Hnvl⟩ := putKv_wf r (pfx ++ key) [] id s Hwf
    ihave %Hrevs := etcdState_revs r [] _ $$ Hs1
    obtain ⟨Hsel, -⟩ := rangeSel_putKv r (pfx ++ key) [] id s o Ho.2.2 (by rw [Hko]; exact hlk)
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    unfold acquireResult
    iexists r, (putKv r (pfx ++ key) [] id s), hdr, hm, rsl, p0, w, rr, [p1], (rangeIn s o).length, true
    rw [Hsel]
    iframe
    iframe #
    isplitr
    · ipureintro; exact ⟨Hrev, Hlo_r, Hr0, Hrmax, Hwf'⟩
    isplitr
    · ipureintro; exact Hp0
    isplitr
    · ipureintro; exact Hrr
    simp only [↓reduceIte]
    iexists id, nv
    iframe #
    ipureintro
    have h := Hrevs nv (kvOf_mem Hnv).1
    exact ⟨Hnv, Hnvl, by omega⟩
  · -- the lease key existed: `Else` ran, read only
    rw [h4]
    simp only [h1, h2, h3, TxnModel.branch, Bool.false_eq_true, ite_false]
    simp only [acquireTxn]
    iunfold txnRespOwn at Hresp
    icases Hresp with ⟨%hdr, %rsl, %ps, #HH, #Hhdr, HS, #HR, #Hps, Hops⟩
    icases txnOpsRespOwn_len2 $$ Hops with ⟨%p0, %p1, %Hpseq, Hops⟩
    subst Hpseq
    icases txnOpsRespOwn_two $$ Hops with ⟨Hop0, Hop1⟩
    icases (txnOpRespOwn_get p1 _ _ _).1 $$ Hop1 with ⟨%Hp1, %w1, %rr1, #Hw1, #Hrr1, %Hrr1n, Hrr1o⟩
    iunfold rangeRespOwn at Hrr1o
    icases Hrr1o with ⟨%h1', Hh1, Hb1⟩
    iunfold rangeBodyOwn at Hb1
    icases Hb1 with ⟨%sl1, %cs1, %more1, Hkvs1, Hsl1, Hcap1, Hcs1, %Hok1, Hmore1, Hcount1⟩
    ihave #Hs := txnStates_read $$ Hts
    ihave %Hrevs := etcdState_revs r [] _ $$ Hs
    ihave %Hlen := ownSlice_len _ _ _ $$ Hps
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z rsl.len by
      simp at Hlen; constructor <;> word))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 1)) [p0, p1] _ p1 (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; rfl
    ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p1 w1 rr1 $$ [$Hpbi $Hw1 $Hrr1]
    · ipureintro; exact Hp1
    try wp_auto
    ihave %Hlen1 := ownSlice_len _ _ _ $$ Hsl1
    icases (txnOpRespOwn_get p0 o _ _).1 $$ Hop0 with ⟨%Hp0, %w, %rr, #Hw0, #Hrr0, %Hrr, Hrr0o⟩
    rcases cs1 with _ | ⟨c, cs1'⟩
    · have hl0 : sint.Z sl1.len = 0 := by
        have := len_eq_sint _ _ Hlen1
        simp only [List.map_nil, List.length_nil] at this; omega
      rw [show decide (sint.Z (W64 0) < sint.Z sl1.len) = false by simp [hl0]]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      unfold acquireResult
      iexists r, s, hdr, hm, rsl, p0, w, rr, [p1], (rangeIn s o).length, false
      iframe
      iframe #
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; exact ⟨⟨Hrev, Hlo_r, Hr0, Hrmax, Hwf⟩, Hp0, Hrr, trivial⟩
    · have hl0 : 0 < sint.Z sl1.len := by
        have := len_eq_sint _ _ Hlen1
        simp only [List.map_cons, List.length_cons] at this; omega
      rw [show decide (sint.Z (W64 0) < sint.Z sl1.len) = true by simp [hl0]]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl1.len by
        constructor <;> word))]
      wp_apply wp_load_slice_index sl1 (sint.Z (W64 0)) _ _ c.p (by decide) $$ [Hsl1] as Hsl1
      · iframe Hsl1; ipureintro; rfl
      icases Hcs1 with ⟨Hc, Hcs1⟩
      iunfold cachedKvOwn at Hc
      icases Hc with ⟨%Hcp, Hck, #Hcks, Hccr, Hcmr, Hcv, Hcval, #Hcvals, Hcl⟩
      wp_auto
      wp_apply hLID lkv γ pfx $$ [$Hpkg $Hlkv $Hrd $Hsr] as %id2 ⟨Hrd, %Hid2⟩
      try wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      unfold acquireResult
      iexists r, s, hdr, hm, rsl, p0, w, rr, [p1], (rangeIn s o).length, _
      iframe
      iframe #
      isplitr
      · ipureintro; exact ⟨Hrev, Hlo_r, Hr0, Hrmax, Hwf⟩
      isplitr
      · ipureintro; exact Hp0
      isplitr
      · ipureintro; exact Hrr
      by_cases hl : c.kv.lease = id2
      · simp only [hl, decide_eq_self_any, decide_True_any, ↓reduceIte]
        have hk := keyGet_kvs (pfx ++ key) s _ Hwf Hok1
        cases hkv : kvOf s (pfx ++ key) with
        | none => rw [hkv] at hk; simp at hk
        | some lv =>
          rw [hkv] at hk
          simp only [List.map_cons, Option.toList_some, List.cons.injEq] at hk
          obtain ⟨hc, -⟩ := hk
          have h := Hrevs lv (kvOf_mem hkv).1
          iexists id2, lv
          iframe #
          ipureintro
          exact ⟨rfl, by rw [← hc, hl], by omega⟩

      · simp only [decide_eq_false hl, Bool.false_eq_true, ↓reduceIte]
        itrivial

end proof

end leasing
end EtcdGrove
end Perennial
