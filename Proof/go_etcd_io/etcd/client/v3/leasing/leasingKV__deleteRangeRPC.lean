/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__deleteRangeRPC.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteRangeRPC
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Cmp__WithRange
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.WithKeysOnly
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__EvictRange
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Delete
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseDeleteRange
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingDeleteLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-- `deleteRangeRPC`'s transaction: the keys-only get and the delete of `[key, e)`, if every lease
key of `[pfx ++ key, pfx ++ e)` was created at or before `m`. -/
def drpcTxn (pfx key e : GoString) (m : w64) : TxnModel :=
  { cmps := [compareM (cmpWithRangeM (pfx ++ e) (cmpKeyM .create (pfx ++ key))) .lt (.num (m + W64 1))],
    thenOps := [.get (opGetModel key [withRangeM e, withKeysOnlyM]), .delete (rangeDeleteOp key e)],
    elseOps := [] }

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.deleteRangeRPC.wp_proof
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCWR : EtcdGrove.Cmp.WithRange.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hWR : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (hWKO : EtcdGrove.WithKeysOnly.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG))
    (hER : leaseCache.EvictRange.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hLD : leaseCache.Delete.spec (GF := GF) (hG := hG))
    (hGRD : EtcdGrove.ResponseOp.GetResponseDeleteRange.spec (GF := GF) (hG := hG)) :
    leasingKV.deleteRangeRPC.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs maxLeaseRev key e lo
  wp_start as ⟨#Hlkv, #Hctx, #Hlo⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, -, #Hkv, #Hp, -, -, -, -, -,
    #HTxn, -, -, -, #Hlc, -⟩
  wp_auto
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hWR e as %f1 #Hf1
  wp_apply hWKO as %f2 #Hf2
  wp_apply wp_slice_literal (l := [f1, f2])
  isplitr
  · ipureintro; rfl
  iintro %slg ⟨Hslg, -⟩
  ipersist Hslg
  ihave #Hoptg : optsAt (GF := GF) _ [withRangeM e, withKeysOnlyM] $$ []
  · unfold optsAt
    iexists [f1, f2]
    iframe Hslg
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg; subst Hf' Hg; iexact Hf1
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg
      subst Hf' Hg; iexact Hf2
    · simp at Hf'
  wp_apply hGet key _ [withRangeM e, withKeysOnlyM] $$ [$Hoptg] as %opG #HopG
  · ipureintro; simp [opGetPanics, opFold, withRangeM, withKeysOnlyM, OpFull.newOp]
  (try wp_auto)
  wp_apply hWR e as %f3 #Hf3
  wp_apply wp_slice_literal (l := [f3])
  isplitr
  · ipureintro; rfl
  iintro %sld ⟨Hsld, -⟩
  ipersist Hsld
  ihave #Hoptd : optsAt (GF := GF) _ [withRangeM e] $$ []
  · unfold optsAt
    iexists [f3]
    iframe Hsld
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg; subst Hf' Hg; iexact Hf3
    · simp at Hf'
  wp_apply hDel key _ [withRangeM e] $$ [$Hoptd] as %opD #HopD
  · ipureintro
    simp [opDeletePanics, opGetPanics, opFold, withRangeM, OpFull.newOp, opDeleteModel,
      OpFull.deleteInit, OpFull.deletePanics, OpModel.zero]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opG, opD])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply hCR (pfx ++ key) as %c0 #Hc0
  wp_apply hCWR c0 _ (pfx ++ e) $$ [$Hc0] as %c1 #Hc1
  (try wp_auto)
  wp_apply hCmp c1 _ go!"<" .lt _ (.num (maxLeaseRev + W64 1)) $$ [$Hc1] as %c2 #Hc2
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpWithRangeM, cmpKeyM, cmpArgOf]
  wp_apply wp_slice_literal (l := [c2])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  (try wp_auto)
  iunfold isEtcdTxnKVO at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpecO at HBs
  icases HBs with ⟨#HIf, #HThen, -, #HCommit⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %_
      %([compareM (cmpWithRangeM (pfx ++ e) (cmpKeyM .create (pfx ++ key))) .lt
          (.num (maxLeaseRev + W64 1))] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c2]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc2
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  have Hg : txnOpOf (opGetModel key [withRangeM e, withKeysOnlyM]) =
      some (.get (opGetModel key [withRangeM e, withKeysOnlyM])) := by
    simp [txnOpOf, opGetModel, opFold, withRangeM, withKeysOnlyM, OpFull.getInit, OpFull.newOp,
      OpModel.zero]
  have Hd : txnOpOf (rangeDeleteOp key e) = some (.delete (rangeDeleteOp key e)) := by
    simp [txnOpOf, rangeDeleteOp, opDeleteModel, opFold, withRangeM, OpFull.deleteInit,
      OpFull.newOp]
  have Hmap : [opGetModel key [withRangeM e, withKeysOnlyM], rangeDeleteOp key e].map txnOpOf =
      ([.get (opGetModel key [withRangeM e, withKeysOnlyM]), .delete (rangeDeleteOp key e)] :
        List TxnOp).map some := by simp [Hg, Hd]
  ihave #HopsT := opsAt_leaves (GF := GF) _ _ _ Hmap $$ []
  · unfold opsAt
    iexists [opG, opD]
    iframe HslT
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %o %Hv %Ho
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopG
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hv Ho
      subst Hv Ho; unfold rangeDeleteOp; iexact HopD
    · simp at Hv
  wp_apply_raw HThen $$ %_ %_ %_
      %([.get (opGetModel key [withRangeM e, withKeysOnlyM]), .delete (rangeDeleteOp key e)] :
        List TxnOp) [$HB]
  · isplitl
    · iexact HopsT
    · ipureintro
      exact ⟨txnOps_leaves _ _ Hmap, rfl, rfl⟩
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ (TxnBuild.mk (drpcTxn pfx key e maxLeaseRev) true true false) (by rfl) $$ HB
  wp_apply_raw HCommit $$ %_ %lo [$HB $Hlo]
  · ipureintro; exact TxnModel.under_nil _
  inext
  iintro %resp %err Hres
  iunfold txnCommitResultO at Hres
  icases Hres with (⟨%Hne, -⟩ | ⟨%Heq, Hok⟩)
  · obtain ⟨g, rfl⟩ : ∃ g, err = GoInterface.ok g := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok g => exact ⟨g, rfl⟩
    (try wp_auto)
    ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
    wp_apply hER (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) key e (fun _ => iprop(True))
      $$ [$Hlc $Hpeek] as -
    · iintro %st %tm HX
      imod leasingX_step lkv γ st (st.evictRange key e tm) $$ HX with ⟨HX, -⟩
      imodintro; iframe
    (try wp_auto)
    iapply HΦ
    ileft; ipureintro; rfl
  subst Heq
  iunfold txnCommitOk at Hok
  icases Hok with ⟨%r, %s, %hm, %Hhm, Hresp, #Hr, %Hfacts, #Hts⟩
  iunfold txnRespOwn at Hresp
  icases Hresp with ⟨%hdr, %rsl, %ps, #HH, #Hhdr, HSucc, #HR, #Hps, Hops⟩
  have hmod : (TxnBuild.mk (drpcTxn pfx key e maxLeaseRev) true true false).model =
      drpcTxn pfx key e maxLeaseRev := rfl
  simp only [hmod] at Hfacts ⊢
  obtain ⟨Hlin, Hr0, Hrmax, Hwf⟩ := Hfacts
  have Hlor : sint.Z lo ≤ sint.Z r :=
    Hlin (by simp [drpcTxn, TxnModel.linearizable, TxnOp.linearizable])
  cases hok : (runTxn r s (drpcTxn pfx key e maxLeaseRev)).1
  · have hrun : runTxn r s (drpcTxn pfx key e maxLeaseRev) =
        (false, s, []) := by
      have h : (drpcTxn pfx key e maxLeaseRev).cmps.all (cmpHolds s) = false := hok
      simp only [runTxn]; rw [h]; simp [TxnModel.branch, drpcTxn, runOps]
    simp only [hrun]
    (try wp_auto)
    iapply HΦ
    ileft; ipureintro; rfl
  · have hrun : runTxn r s (drpcTxn pfx key e maxLeaseRev) =
        (true, s.filter (fun v => !inRange (rangeDeleteOp key e).key (rangeDeleteOp key e).base.rangeEnd v.key),
          [.range (rangeSel s (opGetModel key [withRangeM e, withKeysOnlyM]))
              (rangeIn s (opGetModel key [withRangeM e, withKeysOnlyM])).length,
            .delete (rangeIn s (rangeDeleteOp key e)).length]) := by
      have h : (drpcTxn pfx key e maxLeaseRev).cmps.all (cmpHolds s) = true := hok
      simp only [runTxn]; rw [h]
      simp only [TxnModel.branch, drpcTxn, ite_true, runOps_getDelete]
    have hb : (drpcTxn pfx key e maxLeaseRev).branch true =
        [.get (opGetModel key [withRangeM e, withKeysOnlyM]), .delete (rangeDeleteOp key e)] := rfl
    simp only [hrun, hb, txnWrote_getDelete]
    rcases ps with _ | ⟨p0, _ | ⟨p1, ps⟩⟩
    · simp only [txnOpsRespOwn]; iexfalso; iexact Hops
    · simp only [txnOpsRespOwn]; iexfalso; icases Hops with ⟨-, Hf⟩; iexact Hf
    simp only [txnOpsRespOwn, txnOpRespOwn, rangeRespOwn, rangeBodyOwn]
    icases Hops with ⟨⟨%Hp0, %w0, %rr, #Hu0, #Hw0, %Hrr, ⟨%rh, Hrh, %ksl, %cs, %more, Hksl, Hkps,
      Hkcap, Hcs, %Hkok, Hmore, Hcount⟩⟩, ⟨%Hp1, %w1, %dr, %dh, #Hu1, #Hw1, %Hdr, Hdh, #Hdel⟩, -⟩
    imod (DFractional.dfractional_persist (Φ := fun dq => iprop([∗list] c ∈ cs, cachedKvOwn (GF := GF) c dq))
      (DFrac.own 1)) $$ Hcs with #Hcs
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hps
    have h0 : sint.Z (W64 0) = 0 := by decide
    have hrl : 2 ≤ sint.Z rsl.len := by
      obtain ⟨h1, h2⟩ := Hrlen; simp at h1; word
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
      rw [h0]; omega))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) _ _ p0 (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; rfl
    ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p0 w0 rr $$ [$Hpbi $Hu0 $Hw0]
    · ipureintro; exact Hp0
    ihave %Hklen := ownSlice_len _ _ _ $$ Hkps
    (try wp_auto)
    ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
    ihave IH : iprop(∃ (n : w64) (kp : Loc),
        "i" ∷ i_ptr ↦ n ∗ "kv" ∷ kv_ptr ↦ kp ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (cs.length : Int)⌝) $$ [i kv]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < cs.length := by
        obtain ⟨h1, h2⟩ := Hklen; simp at h1; word
      obtain ⟨c, Hci⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hpi : (cs.map CachedKv.p)[sint.nat n]? = some c.p := by simp [Hci]
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksl.len := ⟨Hn.1, by assumption⟩
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index ksl (sint.Z n) _ _ c.p Hn.1 $$ [Hkps] as Hkps
      · iframe; ipureintro; exact Hpi
      ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ c => cachedKvOwn (GF := GF) c DFrac.discard) Hci) $$ Hcs
      iunfold cachedKvOwn at Hc
      icases Hc with ⟨%Hcp, #HK, #Hks, -⟩
      (try wp_auto)
      wp_apply wp_bytes_to_string c.keySl c.kv.key DFrac.discard $$ [$Hks] as -
      (try wp_auto)
      wp_apply hLD (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) c.kv.key hdr hm
          (fun _ => iprop(True)) $$ [$Hlc $Hpeek $Hhdr] as -
      · iintro %st %h' HX
        imod leasingX_step lkv γ st (st.modify c.kv.key (fun en => en.del h' hm)) $$ HX with ⟨HX, -⟩
        imodintro; iframe
      wp_for_post
      iframe
      iexists n + W64 1, c.p
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z rsl.len by
      constructor <;> word))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 1)) _ _ p1 (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; rfl
    wp_apply hGRD p1 w1 dr $$ [$Hpbi $Hu1 $Hw1]
    · ipureintro; exact Hp1
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    unfold deleteCommitted
    iexists r, s, hdr, hm, (rangeIn s (rangeDeleteOp key e)).length
    iframe
    iframe #
    ipureintro
    exact ⟨⟨Hdr, Hhm, rfl⟩, Hlor, Hr0, Hrmax, Hwf⟩

end proof

end leasing
end EtcdGrove
end Perennial
