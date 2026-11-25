/- Lean-first (no Rocq counterpart).

# `callOn`'s proof

The workers' wait group is `sync.tokJoin`'s (as net/rpc's `ServeCodec`: each `Add(1)` deposits the
caller's thread token, the worker's deferred `Done` gives one back), with no lending. Each worker
takes 8 credits; each of its calls one (`randomArgs`), made with `Call` or with `Go` and a receive on
its `Done` channel (the steps of `Client.Call`'s proof), its outcome checked (`check`, `EchoCall.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.callOn
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.randomArgs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.EchoCall
public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Go
public import Net.Proof.net.rpc.ClientGhost
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

def wkN : Namespace := nroot.@"rpcdriver.workers"

theorem isChan_cap_agree' (ch : Loc) (γ1 γ2 : ChanNames) :
    isChan (GF := GF) ch γ1 Loc ∗ isChan ch γ2 Loc ⊢ ⌜γ1.chanCap = γ2.chanCap⌝ := by
  rw [isChan_unseal]
  unfold isChanDef
  iintro ⟨⟨%m1, #Hc1, -⟩, ⟨%m2, #Hc2, -⟩⟩
  icombine Hc1 Hc2 gives %H
  ipureintro; exact H

/-- A call's outcome as `Client.Call.spec` gives it, as `check` takes it. -/
theorem echo_outcome (pa pr : Loc) (id : w64) (dsl : GoSlice) (data : List w8)
    (fail : GoString) (err : GoInterface) :
    ((⌜err = interface.nil⌝ ∗ echoRargs (GF := GF) pa id dsl data fail ∗
        ∃ rep, echoTheta pr id data fail rep true) ∨
      (∃ msg : GoString, ⌜msg ≠ [] ∧ err = net.rpc.serverErr msg⌝ ∗ net.rpc.errMsg err msg ∗
        echoRargs pa id dsl data fail ∗ (∃ rep, echoPhi id data fail rep msg) ∗ echoD pr) ∨
      (⌜err ≠ interface.nil ∧ net.rpc.notServerErr err⌝ ∗ models_lab.errAny err ∗ True)) ⊢
    callOutcome pa pr id dsl data fail err := by
  iintro H
  iunfold callOutcome
  icases H with (⟨%He, HR, %rep, HT⟩ | ⟨%msg, ⟨%Hm, %He⟩, -, HR, ⟨%rep, HP⟩, -⟩ | ⟨%He, -, -⟩)
  · ileft
    iunfold echoRargs at HR
    icases HR with ⟨Ha, Hd⟩
    iunfold echoTheta at HT
    simp only [↓reduceIte]
    icases HT with ⟨%hf, %dsl', Hr, Hd'⟩
    iframe Ha Hd
    isplitr
    · ipureintro; exact ⟨He, hf⟩
    iexists dsl'; iframe
  · iright; ileft
    iunfold echoRargs at HR
    icases HR with ⟨Ha, -⟩
    iunfold echoPhi at HP
    icases HP with %HP
    iexists msg
    iframe Ha
    ipureintro
    refine ⟨He, ?_⟩
    rcases HP with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨hs, -⟩
    · exact absurd hm Hm
    · exact .inl hm
    · exact .inr hs
  · iright; iright; ipureintro; exact He

theorem callOn.wp_proof (L : CodecLaws (GF := GF))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_randomArgs : randomArgs.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
    (wp_Go : net.rpc.Client.Go.spec (GF := GF) (hG := hG)) :
    callOn.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids W a hSS
  wp_start as ⟨%Hb, #Hf, #Hstr, #Hcl, #Hset, #Hctr, Hcred, Htok⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iunfold isCtr at Hctr; icases Hctr with ⟨#H, -⟩; iexact H
  ihave #Hf' := Hf
  iunfold drvFacts at Hf'
  icases Hf' with ⟨-, %fr, #Hrg, #Hrf⟩
  try wp_auto
  -- the variables the workers read (captured by their closure, never written after): shared
  ipersist ids
  ipersist c
  irename wg => Hwg0
  icases typedPointsto_not_null_dup _ _ _ $$ Hwg0 with ⟨Hwg0, %Hwgnn⟩
  imod sync.init_WaitGroup (wkN.@"wg") wg_ptr $$ Hwg0 with ⟨%γwg, #Hiswg, Hctr0, Hwait⟩
  ihave #Hlaw := sync.tokJoin.lendLaw_false (GF := GF) wkN
  imod sync.tokJoin.init wkN iprop(False) wg_ptr γwg ⊤ Hb $$ [$Hiswg $Hctr0 $Hwait $Hlaw] with Hadd
  wp_apply wp_below (W64 4) as %w0 %Hw0
  have hw0 : uint.Z w0 < 4 := Hw0.2 (by decide)
  try wp_auto
  have hN : uint.nat (W64 1 + w0) ≤ 4 := by word
  ihave Hcred : ownToks γb (8 * uint.nat (W64 1 + w0) + (32 - 8 * uint.nat (W64 1 + w0))) $$ [Hcred]
  · rw [show 8 * uint.nat (W64 1 + w0) + (32 - 8 * uint.nat (W64 1 + w0)) = 32 by omega]
    iexact Hcred
  icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, -⟩
  ihave IH : iprop(∃ (w : w64) (n : Nat) (Pw : IProp GF), "w" ∷ w_ptr ↦ w ∗
      "Hadd" ∷ sync.tokJoin.ownAdder wkN iprop(False) wg_ptr n Pw ∗ "Htok" ∷ threadTok ∗
      "Hcred" ∷ ownToks γb (8 * (uint.nat (W64 1 + w0) - uint.nat w)) ∗
      "%Hw" ∷ ⌜uint.nat w ≤ uint.nat (W64 1 + w0)⌝) $$ [w Hadd Htok Hcred]
  · iexists W64 0, 0, iprop(True)
    iframe w Hadd Htok
    rw [show uint.nat (W64 0) = 0 by rfl, Nat.sub_zero]
    iframe Hcred
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · -- a worker
    have hw : uint.nat w < uint.nat (W64 1 + w0) := by word
    rw [show 8 * (uint.nat (W64 1 + w0) - uint.nat w) =
      8 * (uint.nat (W64 1 + w0) - uint.nat (w + W64 1)) + 8 by
        rw [show uint.nat (w + W64 1) = uint.nat w + 1 by word]; omega]
    icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, H8⟩
    try wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Add iprop(True) wkN iprop(False) wg_ptr n Pw)
      $$ [$Hsync $Hadd $Htok] as ⟨Hadd, Hdone⟩
    wp_bind (Fork _)
    iapply wp_fork_tok_self $$ [Hdone H8]
    · inext
      try wp_auto
      wp_apply wp_with_defer as %defer Hdefer
      try wp_auto
      wp_apply wp_below (W64 9) as %k0 %Hk0
      have hk0 : uint.Z k0 < 9 := Hk0.2 (by decide)
      try wp_auto
      ihave H8 : ownToks γb (uint.nat k0 + (8 - uint.nat k0)) $$ [H8]
      · rw [show uint.nat k0 + (8 - uint.nat k0) = 8 by word]
        iexact H8
      icases ownToks_add_1 _ _ γb $$ H8 with ⟨H8, -⟩
      ihave JH : iprop(∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
          "H8" ∷ ownToks γb (uint.nat k0 - uint.nat i) ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat k0⌝) $$ [i H8]
      · iexists W64 0
        iframe i
        rw [show uint.nat (W64 0) = 0 by rfl, Nat.sub_zero]
        iframe H8
        ipureintro; omega
      wp_for JH
      wp_if_destruct
      · have hi : uint.nat i < uint.nat k0 := by word
        rw [show uint.nat k0 - uint.nat i = (uint.nat k0 - uint.nat (i + W64 1)) + 1 by
          rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word]; omega]
        icases ownToks_add_1 _ _ γb $$ H8 with ⟨H8, H1⟩
        try wp_auto
        wp_apply wp_randomArgs γid γb ids $$ [$Hf $Hctr $H1]
          as %pa ⟨%id, %dsl, %data, %fail, Ha, Hd, %Hlen, %Hfail, Hidt⟩
        try wp_auto
        irename «$r0» => Hr
        generalize «$r0_ptr» = pr at *
        ihave Henc := echo_enc L γid pa id dsl data fail Hlen Hfail $$ [$Ha $Hd $Hidt]
        ihave #Hdec := echo_dec (GF := GF) L pr id data fail
        wp_apply wp_below (W64 2) as %b -
        wp_if_destruct
        · -- `Call`
          wp_apply (wp_Call c W a go!"Svc.Echo" go!"Svc" go!"Echo" (echoSvc γid)
              (ptrIface service.Args.ty pa) (ptrIface service.Reply.ty pr)
              (echoPhi id data fail) (echoRargs pa id dsl data fail) (echoD pr)
              (echoTheta pr id data fail) drvCodec) $$ [Henc Hr]
            as %err Hres
          · iframe Hcl Hset Henc Hdec
            isplitr
            · ipureintro; exact ⟨rfl, hSS, by simp [ptrIface, interface.mkOk]⟩
            isplitr
            · ipureintro; decide
            unfold echoD; rw [show service.Reply.mk (W64 0) slice.nil (W64 0) = zero_val service.Reply from rfl]; iexact Hr
          try wp_auto
          wp_apply wp_check pa pr id dsl data fail err $$ [Hres]
          · iframe Hf Hstr
            iapply echo_outcome
            icases Hres with (⟨%He, HR, HT⟩ | ⟨%msg, %Hm, #Hem, HR, HP, HD⟩ |
              ⟨%He, #Ha, Hrest⟩)
            · ileft; iframe HR HT; ipureintro; exact He
            · iright; ileft; iexists msg; iframe Hem HR HP HD; ipureintro; exact Hm
            · iright; iright; iframe Ha; ipureintro; exact He
          wp_bind (App (Val #fr) (Val _))
          iapply wp_wand $$ (Hrf $$ %go!"concurrent-calls")
          iintro %v %Hv
          subst Hv
          try wp_auto
          wp_for_post
          iframe
          iexists i + W64 1
          iframe
          ipureintro; word
        · -- `Go`, then the receive on its `Done` channel (`Client.Call`'s proof's steps)
          ihave #Hcl0 := Hcl
          iunfold net.rpc.isClient at Hcl0
          icases Hcl0 with ⟨%γ, #HclN⟩
          ihave #HclN' := HclN
          iunfold net.rpc.isClientN at HclN'
          iunfold net.rpc.clientAt at HclN'
          icases HclN' with ⟨%cc, %t, %cn, %la, %ra, -, -, -, -, #Hrpc, -, -, -⟩
          wp_apply (chan.wp_make2 (V := Loc) (W64 1)) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
          · ipureintro; decide
          imod start_future (V := Loc) ch γc (.Buffered []) (.inr rfl) $$ Hch Hoc
            with ⟨%γf, #Hfut, Haw⟩
          imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Option Nat) with ⟨%γt, Hγt⟩
          let K : Loc → IProp GF := fun v => iprop(∃ (o : Option Nat) (err : GoInterface),
            net.rpc.callFields v go!"Svc.Echo" (ptrIface service.Args.ty pa)
              (ptrIface service.Reply.ty pr) ch ∗ net.rpc.ticket γt o ∗
            structFieldRef net.rpc.Call go!"Error" v ↦ err ∗
            net.rpc.callPost γ.conn o (echoPhi id data fail) (echoTheta pr id data fail) (echoD pr) err)
          imod future_alloc_promise γf ch K [] $$ Hfut Haw with ⟨Hful, Haw⟩
          ihave %Hcapf := isChan_cap_agree' ch γc γf.chanName $$ [Hch Hfut]
          · iframe Hch; iunfold isFuture at Hfut; icases Hfut with ⟨$, -⟩
          have hcap : γf.chanName.chanCap = W64 1 := Hcapf ▸ Hcap
          ihave %Hchn := isChan_not_null $$ Hch
          wp_apply wp_Go c W a γ go!"Svc.Echo" go!"Svc" go!"Echo" (echoSvc γid)
              (ptrIface service.Args.ty pa) (ptrIface service.Reply.ty pr) ch γt γf K
              (echoPhi id data fail) (echoRargs pa id dsl data fail) (echoD pr)
              (echoTheta pr id data fail) drvCodec
              $$ [Henc Hr Hγt Hful] as %pc ⟨#Hcf, %o, #Ho, Hsr⟩
          · iframe HclN Hset Henc Hdec Hγt
            isplitr
            · ipureintro; exact ⟨rfl, hSS, by simp [ptrIface, interface.mkOk]⟩
            isplitr
            · ipureintro; exact ⟨Hchn, by rw [hcap]; decide⟩
            isplitr
            · ipureintro; decide
            isplitl [Hr]
            · unfold echoD; rw [show service.Reply.mk (W64 0) slice.nil (W64 0) = zero_val service.Reply from rfl]; iexact Hr
            iunfold net.rpc.callDone
            iframe Hfut Hful
            iintro %pc' %o' %err' Hf' Ht' He' Hp'
            iexists o', err'
            iframe Hf' Ht' He' Hp'
          ihave #Hcf' := Hcf
          iunfold net.rpc.callFields at Hcf'
          icases Hcf' with ⟨-, -, -, #Hdn⟩
          try wp_auto
          rw [List.nil_append]
          wp_apply (lc := 1) (wp_future_await (V := Loc) γf ch [K]) $$ [$Hfut $Haw]
            as %v %P %pre %post ⟨%Hsplit, HK, -⟩
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
          try wp_auto
          ihave Hout : (|={⊤}=> callOutcome (GF := GF) pa pr id dsl data fail err) $$ [Hpost Hsr Hlc1]
          · iunfold net.rpc.callPost at Hpost
            iunfold net.rpc.sendRes at Hsr
            iapply fupd_mono (echo_outcome pa pr id dsl data fail err)
            icases Hpost with (⟨%Hnil, #Hsent, HT⟩ | ⟨%msg, ⟨%Hmsg, %Herrm⟩, #Hsent, HP, HD1⟩ |
              ⟨⟨%Hne, %Hns⟩, #Hea, -⟩)
            · icases Hsr with (HR | ⟨-, Hun⟩)
              · imodintro; ileft; iframe HR HT; ipureintro; exact Hnil
              · imod (net.rpc.unsent_reqSent W a cn γ.conn o) $$ [$Hrpc $Hlc1 $Hun $Hsent] with %Hf
                exact Hf.elim
            · icases Hsr with (HR | ⟨-, Hun⟩)
              · imodintro; iright; ileft
                iexists msg
                iframe HR HP HD1
                isplitr
                · ipureintro; exact ⟨Hmsg, Herrm⟩
                subst Herrm
                iapply net.rpc.errMsg_serverErr
              · imod (net.rpc.unsent_reqSent W a cn γ.conn o) $$ [$Hrpc $Hlc1 $Hun $Hsent] with %Hf
                exact Hf.elim
            · imodintro; iright; iright
              ihave #Hea' := models_lab.errPlain_errAny _ $$ Hea
              iframe Hea'
              ipureintro; exact ⟨Hne, Hns⟩
          iapply fupd_wp
          imod Hout
          imodintro
          try wp_auto
          wp_apply wp_check pa pr id dsl data fail err $$ [Hout]
          · iframe Hf Hstr Hout
          wp_bind (App (Val #fr) (Val _))
          iapply wp_wand $$ (Hrf $$ %go!"concurrent-calls")
          iintro %v' %Hv'
          subst Hv'
          try wp_auto
          wp_for_post
          iframe
          iexists i + W64 1
          iframe
          ipureintro; word
      · -- the calls done: the deferred `Done` gives the slot's token back
        try wp_auto
        wp_apply (sync.tokJoin.WaitGroup.wp_Done wkN iprop(False) wg_ptr iprop(True))
          $$ [$Hsync $Hdone] as Htok
        try wp_auto
        iframe Htok
    · inext
      iintro Htok
      try wp_auto
      wp_for_post
      iframe
      iexists w + W64 1, n + 1, iprop(Pw ∗ True)
      iframe
      ipureintro; word
  · try wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Wait wkN iprop(False) wg_ptr n Pw) $$ [$Hsync $Hadd]
      as ⟨-, -⟩
    try wp_auto
    iapply HΦ
    iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
