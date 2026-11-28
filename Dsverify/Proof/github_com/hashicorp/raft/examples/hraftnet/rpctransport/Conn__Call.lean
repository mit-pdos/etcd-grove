/-
The proof of `rpctransport.Conn.Call`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__Call
public import Net.Proof.net.rpc.ClientGhost
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__get
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__drop
public import Net.Spec.net.rpc.Client__Go
public import Perennial.Spec.time.After

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.Call.wp_proof
    (wp_get : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.get.spec (GF := GF) (hG := hG))
    (wp_drop : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.drop.spec (GF := GF) (hG := hG))
    (wp_Go : net.rpc.Client.Go.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.Call.spec (GF := GF) (hG := hG) := by
  intro p W a sm svc M S args reply Φm Rargs D Θ C d R
  wp_start as ⟨#Hc, %Hsv, %Hsm, #Hset, HR, Hw, HD, #Hdec⟩
  ihave #Henv := dialEnv_of_pkg $$ Hpkg
  iunfold dialEnv at Henv
  icases Henv with ⟨-, -, #Htime, -⟩
  wp_auto
  wp_apply wp_get $$ [$Hc] as %c Hcl
  wp_if_destruct
  · simp only [CallNotSent]
    wp_auto
    iapply HΦ
    iright; ileft
    iframe HR HD
    ipureintro; rfl
  ihave Henc := Hw $$ HR
  icases Hcl with (%Hn | #Hcl)
  · exfalso; exact Hif Hn
  ihave #Hcl0 := Hcl
  iunfold net.rpc.isClient at Hcl0
  icases Hcl0 with ⟨%γ, #HclN⟩
  ihave #HclN' := HclN
  iunfold net.rpc.isClientN at HclN'
  iunfold net.rpc.clientAt at HclN'
  icases HclN' with ⟨%cc, %t, %cn, %la, %ra, -, -, -, -, #Hrpc, -, -, -⟩
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := Loc) (W64 1)) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Loc) ch γc (.Buffered []) (.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, Haw⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Option Nat) with ⟨%γt, Hγt⟩
  let K : Loc → IProp GF := fun v => iprop(∃ (o : Option Nat) (err : GoInterface),
    net.rpc.callFields v sm args reply ch ∗ net.rpc.ticket γt o ∗
    structFieldRef net.rpc.Call go!"Error" v ↦ err ∗ net.rpc.callPost γ.conn o Φm Θ D err)
  imod future_alloc_promise γf ch K [] $$ Hfut Haw with ⟨Hful, Haw⟩
  ihave %Hcapf := isChan_cap_agree ch γc γf.chanName $$ [Hch Hfut]
  · iframe Hch; iunfold isFuture at Hfut; icases Hfut with ⟨$, -⟩
  have hcap : γf.chanName.chanCap = W64 1 := Hcapf ▸ Hcap
  ihave %Hchn := isChan_not_null $$ Hch
  wp_apply wp_Go c W a γ sm svc M S args reply ch γt γf K Φm Rargs D Θ C
      $$ [$HclN $Hset $Henc $HD $Hdec $Hγt Hful] as %pc ⟨#Hf, %o, #Ho, Hres⟩
  · isplitr
    · ipureintro; exact Hsv
    isplitr
    · ipureintro; exact ⟨Hchn, by rw [hcap]; decide⟩
    isplitr
    · ipureintro; exact Hsm
    iunfold net.rpc.callDone
    iframe Hfut Hful
    iintro %pc %o %err Hf Ht He Hp
    iexists o, err
    iframe Hf Ht He Hp
  ihave #Hf' := Hf
  iunfold net.rpc.callFields at Hf'
  icases Hf' with ⟨-, -, -, #Hdn⟩
  wp_auto_lc 2
  irename Hlc1 => Hlc3
  irename Hlc2 => Hlc4
  wp_apply (lc := 2) (time.After.spec_pkgInit wp_After _) as %tch %γtm #Htch
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the answer
    dsimp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γf.chanName
    isplitr
    · ipureintro; rfl
    ihave #Hisch : isChan ch γf.chanName Loc $$ [Hfut]
    · unfold isFuture; icases Hfut with ⟨$, -⟩
    iframe Hisch
    iapply future_await_au γf ch _ _ $$ Hfut [$Hlc2 $Hlc3 $Hlc4 $Haw]
    inext
    iintro %v %P %pre %post %Hsplit HK -
    have hP : P = K := by
      rcases pre with _ | ⟨x, pre⟩
      · simp at Hsplit; exact Hsplit.1.symm
      · simp at Hsplit
    subst hP
    icases HK with ⟨%o', %err, #Hfv, #Hov, Herr, Hpost⟩
    iunfold net.rpc.ticket at Ho
    iunfold net.rpc.ticket at Hov
    ihave %Hoo := ghostMapElem_agree () γt _ _ o o' $$ Ho Hov
    subst Hoo
    iunfold net.rpc.callPost at Hpost
    iunfold net.rpc.sendRes at Hres
    wp_auto
    icases Hpost with (⟨%Hnil, #Hsent, HΦ1⟩ | ⟨%msg, ⟨%Hmsg, %Herrm⟩, -, -, -⟩ |
      ⟨⟨%Hne, %Hns⟩, -, -⟩)
    · subst Hnil
      icases Hres with (HR | ⟨-, Hun⟩)
      · simp only [CallOK]
        wp_auto
        iapply HΦ
        ileft
        iframe HR HΦ1
        ipureintro; rfl
      · ihave Hfls : (|={⊤}=> False : IProp GF) $$ [Hlc1 Hun]
        · iapply net.rpc.unsent_reqSent W a cn γ.conn o $$ [$Hrpc $Hlc1 $Hun $Hsent]
        imod Hfls with %Hfls
        exact Hfls.elim
    · subst Herrm
      have hne : net.rpc.serverErr msg ≠ interface.nil := net.rpc.serverErr_ne_nil msg
      (try wp_auto)
      wp_apply wp_drop $$ [$Hc $Hcl]
      simp only [CallFailed]
      wp_auto
      iapply HΦ
      iright; iright
      ipureintro; rfl
    · rcases err with ei | _
      rotate_left
      · exfalso; exact Hne rfl
      (try wp_auto)
      wp_apply wp_drop $$ [$Hc $Hcl]
      simp only [CallFailed]
      wp_auto
      iapply HΦ
      iright; iright
      ipureintro; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the timeout
    dsimp only [chan.blockingClausePre]
    ihave #Htch_chan := is_bag_is_chan _ _ _ $$ Htch
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γtm
    isplitr
    · ipureintro; rfl
    iframe Htch_chan
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %v -
    wp_auto
    wp_apply wp_drop $$ [$Hc $Hcl]
    simp only [CallFailed]
    wp_auto
    iapply HΦ
    iright; iright
    ipureintro; rfl
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
