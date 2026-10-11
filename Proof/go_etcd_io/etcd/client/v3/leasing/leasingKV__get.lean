/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__get.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__get
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__readySession
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__acquire
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__monitorLease
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Get
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__MayAcquire
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Add
public import Spec.go_etcd_io.etcd.client.v3.OpResponse__Get
public import Spec.go_etcd_io.etcd.client.v3.Op__IsSerializable
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingGetLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.get.wp_proof
    (hRG : EtcdGrove.OpResponse.Get.spec (GF := GF) (hG := hG))
    (hRS : leasingKV.readySession.spec (GF := GF) (hG := hG))
    (hCG : leaseCache.Get.spec (GF := GF) (hG := hG))
    (hSer : EtcdGrove.Op.IsSerializable.spec (GF := GF) (hG := hG))
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hMA : leaseCache.MayAcquire.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hAcq : leasingKV.acquire.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hAdd : leaseCache.Add.spec (GF := GF) (hG := hG))
    (hML : leasingKV.monitorLease.spec (GF := GF) (hG := hG)) :
    leasingKV.get.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs opv o lo q
  wp_start as ⟨#Hlkv, Hrd, Hslot, #Hctx, #Hop, #Hlo, %Ho, Hopen, Htok⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hclf, #Hkvf, #Hpfxf, #Hctxf,
    #Hcancelf, #Hoslf, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  wp_auto
  ipersist lkv
  ipersist op
  ipersist ctx
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ipersist «do»
  iunfold isEtcdDoKV at HDo
  wp_apply hRS lkv γ pfx $$ [$Hpkg $Hlkv $Hrd] as %b ⟨Hrd, Hb⟩
  cases b
  · -- the session is not ready: the client's `Do`
    wp_auto
    wp_apply HDo $$ %ctx %cs %opv %o %lo [$Hctx $Hop $Hlo] as %r %err #Hres
    · ipureintro; exact Ho
    try wp_auto
    wp_apply hRG $$ [$Hcv $r] as r
    try wp_auto
    iapply HΦ
    iframe
    unfold getOutcome
    ileft
    iframe
    iframe #
  -- the session is ready: the cache
  simp only [Bool.not_true]
  wp_auto
  ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
  wp_apply hCG (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) ctx cs opv o
    $$ [$Hpkg $Hcache $Hrd $Hpeek $Hctx $Hop] as %ret %ok ⟨Hrd, Hres⟩
  icases Hres with (⟨%Hbad, %Hret, %Hok⟩ | ⟨%Hbad, %Hok, %Hret⟩ |
    ⟨⟨%Hbad, %Hok⟩, %st, %e, #Hseen, %He, #Hfacts, Hfresh⟩)
  · -- not a get the cache serves: the client's `Do`
    subst Hret Hok
    wp_auto
    wp_apply HDo $$ %ctx %cs %opv %o %lo [$Hctx $Hop $Hlo] as %r %err #Hres
    · ipureintro; exact Ho
    try wp_auto
    wp_apply hRG $$ [$Hcv $r] as r
    try wp_auto
    iapply HΦ
    iframe
    unfold getOutcome
    ileft
    iframe
    iframe #
  · subst Hret Hok
    wp_auto
    ihave #Hop' := Hop
    iunfold opFullAt at Hop'
    icases Hop' with ⟨#HopAt, #HopKey, -⟩
    wp_apply hSer $$ [$Hcv $op $HopAt] as op
    cases hser : o.base.serializable
    · wp_auto
      wp_apply hKey $$ [$Hcv $op $Hop] as %ksl ⟨op, #Hk⟩
      wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
      try wp_auto
      ipersist key
      wp_apply hMA (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key
        $$ [$Hpkg $Hcache $Hrd $Hpeek] as %mb ⟨Hrd, %st, #Hseen, %Hmb⟩
      cases mb
      · wp_auto
        wp_apply HDo $$ %ctx %cs %opv %o %lo [$Hctx $Hop $Hlo] as %r %err #Hres
        · ipureintro; exact Ho
        try wp_auto
        wp_apply hRG $$ [$Hcv $resp] as resp
        try wp_auto
        iapply HΦ
        iframe
        unfold getOutcome
        ileft
        iframe
        iframe #
      · wp_auto
        ihave #Hnil := concurrency.optsAt_nil (GF := GF)
        wp_apply hGet o.key slice.nil [] $$ [$Hcv $Hnil] as %opK #HopK
        · ipureintro; exact concurrency.keyOp_not_panics
        obtain ⟨-, hkk, hke, -, -⟩ := keyGet_fields o.key
        wp_apply hAcq lkv γ pfx ctx cs o.key opK (opGetModel o.key []) lo
          $$ [$Hpkg $Hlkv $Hrd $Hctx $HopK $Hlo] as %resp %err ⟨Hrd, Hacq⟩
        · ipureintro; exact ⟨keyGet_txnOpOf _, hkk, hke⟩
        icases Hacq with (⟨%Hne, %Hresp⟩ | ⟨%Heq, Hacq⟩)
        · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
            cases err with
            | nil => exact absurd rfl Hne
            | ok e => exact ⟨e, rfl⟩
          subst Hresp
          wp_auto
          iapply HΦ
          iframe
          unfold getOutcome
          iright; iright; iright; iright
          iframe
          ipureintro; exact ⟨Hne, rfl⟩
        subst Heq
        unfold acquireResult
        icases Hacq with ⟨%r, %s, %hdr, %hm, %rsl, %p0, %w, %rr, %ps, %n, %ok, %Hf, #Hr, #Hs, #HH,
          #Hhdr, HS, #HR, #Hps, %Hp0, #Hw0, #Hrr0, %Hrr, Hrro, Hokf⟩
        ihave %Hlen := ownSlice_len _ _ _ $$ Hps
        iunfold rangeRespOwn at Hrro
        icases Hrro with ⟨%h0, Hh0, Hbody⟩
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
          simp at Hlen; constructor <;> word))]
        wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) (p0 :: ps) _ p0 (by decide) $$ [Hps] as -
        · iframe Hps; ipureintro; rfl
        ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
        · iPkgInit
        wp_apply hGRR p0 w rr $$ [$Hpbi $Hw0 $Hrr0]
        · ipureintro; exact Hp0
        try wp_auto
        obtain ⟨Hrev, Hlo_r, Hr0, Hrmax, Hwf⟩ := Hf
        have hg : opGetModel o.key [] = OpFull.getInit o.key := rfl
        cases ok
        · -- not acquired: the transaction's get
          wp_auto
          iapply HΦ
          iframe
          unfold getOutcome
          iright; iright; iright; ileft
          iframe
          isplitr
          · ipureintro; rfl
          unfold getNotAcquired
          iexists r, s, hdr, hm, n
          rw [← hg]
          iframe
          iframe #
          ipureintro; exact ⟨Hrr, Hrev, Hlo_r, Hwf⟩
        -- acquired: cache the response
        simp only [↓reduceIte]
        icases Hokf with ⟨%id, %lv, %Hlv, #Hready, #Hsr⟩
        iunfold rangeBodyOwn at Hbody
        icases Hbody with ⟨%sl, %cs1, %more, Hkvs, Hsl, Hcap, Hcs, %Hok, Hmore, Hcount⟩
        let e0 : LeaseEntry := LeaseEntry.mk null hm.revision null rr hdr hm sl cs1 more
          (W64 (n : Int)) id (kvOf s o.key)
        have he0 : e0.rev = e0.hm.revision ∧ e0.acq = e0.kv := ⟨rfl, (keyGet_head o.key s cs1 Hwf Hok).symm⟩
        ihave HrespOwn : respOwn (GF := GF) e0 (DFrac.own 1) $$ [Hh0 Hkvs Hsl Hcap Hcs Hmore Hcount]
        · unfold respOwn
          iframe
          iframe #
          ipureintro; exact Hrr
        ihave #Hfacts : entryFacts (GF := GF) pfx o.key e0 $$ []
        · unfold entryFacts
          iexists s
          have he : e0.rev = r := Hrev
          rw [he]
          iframe #
          ipureintro
          exact ⟨Hwf, rfl, lv, Hlv.1, Hlv.2.1, Hlv.2.2⟩
        ihave Hstep : iprop(∀ (st : LeaseCacheSt) (li : Loc) (ch : GoChan),
            leasingX lkv γ st 1 ={⊤}=∗
              leasingX lkv γ (st.add o.key { e0 with li := li, waitc := ch }) 1 ∗ True) $$ []
        · iintro %st %li %ch HX
          imod (leasingX_stepF (GF := GF) lkv γ (fun st => st.add o.key { e0 with li := li, waitc := ch }))
            $$ %st HX with ⟨HX, -⟩
          imodintro
          iframe
        wp_auto
        wp_apply hAdd (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key e0 opv o
          (fun _ => iprop(True)) $$ [$Hpkg $Hcache $Hpeek $Hready $HrespOwn $Hfacts $Hop $Hstep]
          as %ret ⟨%st1, -, -, Hfresh⟩
        · ipureintro; exact he0
        ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
        · iPkgInit
        try wp_auto
        wp_apply wp_leasingWg_Add lkv γ q Hbound $$ [$Hsync $Hwg $Hwginv $Hopen $Htok] as ⟨Hrun, Hopen⟩
        ipersist resp
        ipersist key
        try wp_auto
        ihave #Hhdr' := Hhdr
        iunfold hdrFull at Hhdr'
        icases Hhdr' with ⟨%Hhnn, -, -, #HRev, -, -⟩
        wp_apply wp_fork_tok_self $$ [Hrun Hslot] as Htok
        · try wp_auto
          wp_apply wp_with_defer as %defer defer
          try wp_auto
          wp_apply hML lkv γ pfx ctx cs o.key hm.revision $$ [$Hpkg $Hlkv $Hslot $Hsr $Hctx]
          · ipureintro; rw [Hrev]; constructor <;> omega
          try wp_auto
          wp_apply wp_leasingWg_Done lkv γ $$ [$Hsync $Hwg $Hwginv $Hrun] as Htok
          try wp_auto
          iexact Htok
        try wp_auto
        iapply HΦ
        iframe
        unfold getOutcome
        iright; iright; ileft
        isplitr
        · ipureintro; rfl
        unfold getAcquired
        iexists e0
        have he : e0.rev = r := Hrev
        rw [he]
        iframe
        iframe #
        ipureintro
        exact ⟨he0.2.symm, Hrev.symm, Hlo_r⟩
    · wp_auto
      wp_apply HDo $$ %ctx %cs %opv %o %lo [$Hctx $Hop $Hlo] as %r %err #Hres
      · ipureintro; exact Ho
      try wp_auto
      wp_apply hRG $$ [$Hcv $r] as r
      try wp_auto
      iapply HΦ
      iframe
      unfold getOutcome
      ileft
      iframe
      iframe #
  · iunfold freshGetResp at Hfresh
    icases Hfresh with ⟨%Hnn, Hfresh⟩
    rw [decide_eq_false Hnn]
    wp_auto
    iapply HΦ
    iframe
    unfold getOutcome
    iright; ileft
    isplitr
    · ipureintro; rfl
    iframe
    unfold getCached freshGetResp
    iexists st, e
    iframe
    iframe #
    ipureintro; exact ⟨He, Hnn⟩

end proof

end leasing
end EtcdGrove
end Perennial
