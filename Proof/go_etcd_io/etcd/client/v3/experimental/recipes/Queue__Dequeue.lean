/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Queue__Dequeue.lean`. Lean-first (no
Rocq counterpart). The recursion (`More`, a lost claim) is Löb induction (`iloeb`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Queue__Dequeue
public import Spec.go_etcd_io.etcd.client.v3.WithFirstRev
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.claimFirstKey
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.WaitPrefixEvents
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.deleteRevKey
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem Queue.Dequeue.wp_proof (hWFR : EtcdGrove.WithFirstRev.spec (GF := GF) (hG := hG))
    (hCFK : claimFirstKey.spec (GF := GF) (hG := hG))
    (hWPE : WaitPrefixEvents.spec (GF := GF) (hG := hG))
    (hDRK : deleteRevKey.spec (GF := GF) (hG := hG)) :
    Queue.Dequeue.spec (GF := GF) (hG := hG) := by
  intro q client kp lo
  iloeb as IH
  wp_start as ⟨#Hcc, #Hq, #Hlo, %Hlo0⟩
  ihave #Hq' := Hq
  iunfold isQueue at Hq'
  icases Hq' with ⟨#Hqc, #Hqx, #Hqk, %Hkp, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  ihave #Hkv' := Hkv
  iunfold isRecipesKV at Hkv'
  icases Hkv' with ⟨#HGet, -, -, -⟩
  wp_auto
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hWFR $$ [$Hcv] as %osl ⟨#Hosl, -⟩
  (try wp_auto)
  ihave #Hopts := optsAt_res osl _ iprop(True) $$ Hosl
  iunfold isEtcdKVTodo at HGet
  ihave #HG := HGet $$ %kp %osl %(withTopM (W64 3) (W64 1)) %iprop(True) %lo
  obtain ⟨Ht, Hk, He, Hrev, Hser, -, -, Hl, Hc, -, Hf1, Hf2, Hf3, Hf4⟩ := firstRevOp_fields kp Hkp
  wp_apply HG $$ [] as %gresp %gerr ⟨-, #Hgres, #Hmore⟩
  · iframe Hopts Hlo
    ipureintro
    exact ⟨firstRevOp_not_panics, Ht⟩
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact Hgne
  subst Hgnil
  have HRle' : sint.Z lo ≤ sint.Z R := HRle.1 Hser
  have HkP : (firstRevOp kp).isPrefixGet kp = false := by
    simp [OpFull.isPrefixGet, Hl, Hkp]
  rw [ite_eq_right (c := (firstRevOp kp).isPrefixGet kp = true) (by rw [HkP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (firstRevOp kp).base.rev = W64 0 ∧
      KeyRangeUnder kp (firstRevOp kp).key (firstRevOp kp).base.rangeEnd from
    ⟨Hrev, by rw [Hk, He]; exact keyRangeUnder_prefix kp Hkp⟩)]
  icases Hgr with ⟨%s0, %gsl, %gps, %gkvs, #Hs0, %Hwf0, #Hgsl, #Hgps, #Hgkvs, %Hgok⟩
  -- the `More` flag, on the same state
  iunfold getRespMore at Hmore
  icases Hmore with (%Hmne | ⟨%R', %more, #HgRev', #HMore, Hm⟩)
  · exact absurd rfl Hmne
  ihave %HRR' := getRespRev_agree gresp R R' $$ [$HgRev $HgRev']
  subst HRR'
  rw [ite_eq_left (show (firstRevOp kp).base.rev = W64 0 ∧
      KeyRangeUnder kp (firstRevOp kp).key (firstRevOp kp).base.rangeEnd from
    ⟨Hrev, by rw [Hk, He]; exact keyRangeUnder_prefix kp Hkp⟩)]
  icases Hm with ⟨%s0', #Hs0', %Hmv⟩
  ihave %Hs00 := etcdState_agree R kp s0 s0' $$ [$Hs0 $Hs0']
  subst Hs00
  have Hmem := prefixGet_sel_mem kp (firstRevOp kp) s0 Hkp Hk He Hf1 Hf2 Hf3 Hf4
  obtain ⟨Hlen1, -, Hfirst, Hall⟩ := firstRevOp_kvs kp Hkp _ gkvs Hgok
  ihave %Hrevs := etcdState_revs R kp s0 $$ Hs0
  have Hgsub : ∀ v ∈ gkvs, v ∈ s0 ∧ kp <+: v.key := by
    intro v hv
    match gkvs, Hlen1, Hfirst, hv with
    | [w], _, Hfirst, hv =>
      have := List.mem_singleton.1 hv; subst this
      exact (Hmem v).1 (Hfirst v rfl).1
  -- `claimFirstKey(client.KV, resp.Kvs)`, knowing etcd reached `R`
  wp_auto
  wp_apply hCFK kv kp gsl gps gkvs R $$ [$Hpkg $Hkv $HRR $Hgps $Hgkvs] as %p %cerr Hcres
  · ipureintro
    intro v hv
    obtain ⟨h1, h2⟩ := Hgsub v hv
    exact ⟨h2, by have := Hrevs v h1; omega⟩
  icases Hcres with (⟨%Hcnil, %n, #Hcb, Hcase⟩ | %Hcne)
  rotate_left
  · obtain ⟨Hcne, rfl⟩ := Hcne
    obtain ⟨e, rfl⟩ : ∃ e, cerr = GoInterface.ok e := by
      cases cerr with
      | nil => exact absurd rfl Hcne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact Hcne
  subst Hcnil
  -- the claim's outcome: no item (each gone; a claimed item at a nil pointer counts as gone), or
  -- the get's one item, claimed by this call
  ihave Hcase2 : iprop((⌜p = null⌝ ∗ claimedBefore kp R gkvs gkvs.length) ∨
      (⌜p ≠ null⌝ ∗ ∃ (v : EtcdKv) (r : w64), ⌜gkvs = [v]⌝ ∗ kvValAt p v ∗ etcdReached r ∗
        revKeyDeleted kp v.key v.modRev r ∗ etcdRevToken r ∗ ⌜sint.Z R ≤ sint.Z r⌝)) $$ [Hcase]
  · icases Hcase with (%Hnull | ⟨%v, %r, %Hpv, #Hpkv, #Hr, #Hdel, Htok, %HRr⟩)
    · obtain ⟨rfl, rfl⟩ := Hnull
      ileft
      iframe Hcb
      ipureintro; rfl
    · obtain ⟨Hpn, Hvn⟩ := Hpv
      have hn0 : n = 0 := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 Hvn
        omega
      subst hn0
      have Hgv : gkvs = [v] := by
        match gkvs, Hlen1, Hvn with
        | [w], _, Hvn => simp at Hvn; subst Hvn; rfl
      subst Hgv
      by_cases hp : p = null
      · ileft
        isplitr
        · ipureintro; exact hp
        unfold claimedBefore
        isplitr
        · ipureintro; simp
        imodintro
        iintro %j %w ⟨%Hj, %Hw⟩
        have hj : j = 0 := by simp at Hj; omega
        subst hj
        simp at Hw; subst Hw
        iexists r
        iframe Hr
        isplitl
        · iunfold revKeyDeleted at Hdel
          icases Hdel with ⟨%sd, %sd', -, #Hsd', %Hd⟩
          unfold revKeyGone
          iexists sd'
          iframe Hsd'
          ipureintro
          intro x hx hxk; exact absurd hxk (Hd.2.2 x hx)
        ipureintro; exact HRr
      · iright
        isplitr
        · ipureintro; exact hp
        iexists v, r
        iframe Hpkv Hr Hdel Htok
        ipureintro; exact ⟨rfl, HRr⟩
  wp_auto
  wp_if_destruct
  · -- no item claimed
    icases Hcase2 with (⟨-, #Hcb2⟩ | ⟨%Hpn, -⟩)
    rotate_left
    · exact absurd rfl Hpn
    wp_if_destruct
    · -- not `More`: the get listed every item; wait for a put from `R`
      have Hsel1 := more_limit1 _ _ false Hl Hc Hmv rfl
      have Hsub : ∀ w ∈ s0, kp <+: w.key → w ∈ gkvs :=
        fun w hw hwk => Hall Hsel1 w ((Hmem w).2 ⟨hw, hwk⟩)
      ihave ⟨%rd, #Hrd, %HRrd, #Hdrained⟩ := drained_intro kp kp R gkvs s0 Hlen1 Hsub $$ [$HRR $Hcb2]
      iunfold getRespRev at HgRev
      icases HgRev with ⟨%hdr, #Hhdr, %Hhdrnn, #HhRev⟩
      wp_auto
      wp_apply wp_slice_literal (l := [evPut])
      isplitr
      · ipureintro; rfl
      iintro %slT ⟨HslT, -⟩
      ipersist HslT
      (try wp_auto)
      wp_apply hWPE client kp kp R _ [evPut] evPut $$ [$Hpkg $Hcc $Hcl $HslT]
        as %ev %werr ⟨%Hwnil, #Hwev⟩
      · ipureintro
        exact ⟨rfl, List.prefix_refl kp, by omega⟩
      subst Hwnil
      ihave ⟨%e, %v, %se, #Hev, #Hvkv, #Her, #Hse, %Hp⟩ := waitedEvent_put kp _ R ev $$ Hwev
      obtain ⟨Hvse, Hwfe, Hvk, Hvm, HRe, Hin⟩ := Hp
      obtain ⟨-, -, Hwk⟩ := prefixWatchOp_fields kp R
      obtain ⟨Hwk1, Hwk2⟩ := Hwk Hkp
      rw [Hwk1, Hwk2, inRange_prefix kp e.key Hkp] at Hin
      ihave %Hrevse := etcdState_revs e.rev kp se $$ Hse
      have Hepos : 0 < sint.Z e.rev := by
        have := Hrevse v Hvse; rw [Hvm] at this; omega
      iunfold eventAt at Hev
      icases Hev with ⟨%ekeySl, #HeT, #HeKv, #HeK, #HeKs, #HeM⟩
      wp_auto
      wp_apply wp_bytes_to_string ekeySl e.key DFrac.discard $$ [$HeKs] as -
      (try wp_auto)
      wp_apply hDRK kv kp e.key e.rev rd $$ [$Hpkg $Hkv $Hrd] as %ok %derr Hdres
      · ipureintro; exact ⟨Hin, Hepos⟩
      icases Hdres with (⟨%Hdnil, %r, #Hr, %Hrr, Hc⟩ | %Hdne)
      rotate_left
      · obtain ⟨Hdne, rfl⟩ := Hdne
        obtain ⟨e', rfl⟩ : ∃ e', derr = GoInterface.ok e' := by
          cases derr with
          | nil => exact absurd rfl Hdne
          | ok e' => exact ⟨e', rfl⟩
        wp_auto
        iapply HΦ
        iright
        ipureintro; exact Hdne
      subst Hdnil
      cases ok
      · -- claimed by another dequeuer: retry
        wp_auto
        rw [method_unfold (t := go.GoType.PointerType Queue.ty) (m := go!"Dequeue")]
        wp_apply IH $$ [$Hpkg $Hcc $Hq $Hlo] as %v' %err' Hres
        · ipureintro; exact Hlo0
        (try wp_auto)
        iapply HΦ
        iexact Hres
      · -- claimed by this call
        simp only [↓reduceIte]
        icases Hc with ⟨#Hdel, Htok⟩
        rw [← Hvk, ← Hvm]
        ihave Hdq := dequeuedAt_intro kp kp v v.modRev r se Hvse (Hvk ▸ Hin) $$ [$Hse $Hdel $Htok]
        ihave %Hmlt := dequeuedAt_modRev_lt kp kp v r $$ Hdq
        ihave #Hord := dequeueOrder_wait kp kp modRevLe v R rd r s0 (by rw [Hvm]; exact HRe)
          Hrr.1 (by rw [Hvm] at Hmlt; omega) $$ [$Hs0 $Hdrained]
        iunfold kvValAt at Hvkv
        icases Hvkv with ⟨%keySl, %valSl, -, -, -, -, -, #HV, #HVs, -⟩
        wp_auto
        wp_apply wp_bytes_to_string valSl v.value DFrac.discard $$ [$HVs] as -
        (try wp_auto)
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists v, r
        iframe Hr Hdq Hord
        ipureintro; exact ⟨rfl, by omega⟩
    · -- `More`: retry
      rw [method_unfold (t := go.GoType.PointerType Queue.ty) (m := go!"Dequeue")]
      wp_apply IH $$ [$Hpkg $Hcc $Hq $Hlo] as %v %err Hres
      · ipureintro; exact Hlo0
      (try wp_auto)
      iapply HΦ
      iexact Hres
  · -- the get path: the get's item, claimed by this call
    icases Hcase2 with (⟨%Hpn, -⟩ | ⟨-, %v, %r, %Hgv, #Hpkv, #Hr, #Hdel, Htok, %HRr⟩)
    · exact absurd Hpn Hif
    obtain ⟨Hvsel, Hvmin⟩ := Hfirst v Hgv
    obtain ⟨Hv0, Hvk⟩ := (Hmem v).1 Hvsel
    ihave Hdq := dequeuedAt_intro kp kp v R r s0 Hv0 Hvk $$ [$Hs0 $Hdel $Htok]
    ihave %Hne := dequeuedAt_ne kp kp v R r s0 Hv0 $$ [$Hs0 $Hdq]
    have Hlt : sint.Z R < sint.Z r := by
      have : sint.Z R ≠ sint.Z r := fun h => Hne (by word)
      omega
    ihave #Hord := dequeueOrder_get kp kp modRevLe v R r s0 Hv0
      (fun w hw hwk => Hvmin w ((Hmem w).2 ⟨hw, hwk⟩)) Hlt $$ Hs0
    iunfold kvValAt at Hpkv
    icases Hpkv with ⟨%keySl, %valSl, -, -, -, -, -, #HV, #HVs, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string valSl v.value DFrac.discard $$ [$HVs] as -
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists v, r
    iframe Hr Hdq Hord
    ipureintro; exact ⟨rfl, by omega⟩
