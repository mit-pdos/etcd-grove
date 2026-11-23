/-
The proof of `Client.Call` (`Net/Spec/net/rpc/Client__Call.lean`): a buffered channel of capacity 1
made a future (Perennial's future idiom) with one promise, whose contract is the call's outcome
(`callPost`) on its ticket; `Go`; the receive gets the outcome. `send`'s result and the outcome
together give dsverify's postcondition: an answer (`reqSent`) never comes for a request kept unsent
(`unsent_reqSent`).
-/
module

public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Go
public import Net.Proof.net.rpc.ClientGhost

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- Two `isChan` of one channel agree on its capacity. (A general fact of Perennial's channels,
proved here: `notes/perennial-changes.md`.) -/
theorem isChan_cap_agree (ch : Loc) (γ1 γ2 : ChanNames) :
    isChan (GF := GF) ch γ1 Loc ∗ isChan ch γ2 Loc ⊢ ⌜γ1.chanCap = γ2.chanCap⌝ := by
  rw [isChan_unseal]
  unfold isChanDef
  iintro ⟨⟨%m1, #Hc1, -⟩, ⟨%m2, #Hc2, -⟩⟩
  icombine Hc1 Hc2 gives %H
  ipureintro; exact H

theorem Client.Call.wp_proof (wp_Go : Client.Go.spec (GF := GF) (hG := hG)) :
    Client.Call.spec (GF := GF) (hG := hG) := by
  intro c W a sm svc M S args reply Φm Rargs D Θ C
  wp_start as ⟨#Hcl, %Hsv, #Hset, Henc, HD, #Hdec⟩
  iunfold isClient at Hcl
  icases Hcl with ⟨%γ, #Hcl⟩
  ihave #Hcl' := Hcl
  iunfold isClientN at Hcl'
  iunfold clientAt at Hcl'
  icases Hcl' with ⟨%cc, %t, %cn, %la, %ra, -, -, -, -, #Hrpc, -, -, -⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 1)) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Loc) ch γc (.Buffered []) (.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, Haw⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Option Nat) with ⟨%γt, Hγt⟩
  let K : Loc → IProp GF := fun v => iprop(∃ (o : Option Nat) (err : GoInterface),
    callFields v sm args reply ch ∗ ticket γt o ∗
    structFieldRef net.rpc.Call go!"Error" v ↦ err ∗ callPost γ.conn o Φm Θ D err)
  imod future_alloc_promise γf ch K [] $$ Hfut Haw with ⟨Hful, Haw⟩
  ihave %Hcapf := isChan_cap_agree ch γc γf.chanName $$ [Hch Hfut]
  · iframe Hch; iunfold isFuture at Hfut; icases Hfut with ⟨$, -⟩
  have hcap : γf.chanName.chanCap = W64 1 := Hcapf ▸ Hcap
  ihave %Hchn := isChan_not_null $$ Hch
  wp_apply wp_Go c W a γ sm svc M S args reply ch γt γf K Φm Rargs D Θ C
      $$ [$Hcl $Hset $Henc $HD $Hdec $Hγt Hful] as %pc ⟨#Hf, %o, #Ho, Hres⟩
  · isplitr
    · ipureintro; exact Hsv
    isplitr
    · ipureintro; exact ⟨Hchn, by rw [hcap]; decide⟩
    iunfold callDone
    iframe Hfut Hful
    iintro %pc %o %err Hf Ht He Hp
    iexists o, err
    iframe Hf Ht He Hp
  ihave #Hf' := Hf
  iunfold callFields at Hf'
  icases Hf' with ⟨-, -, -, #Hdn⟩
  wp_auto
  rw [List.nil_append]
  wp_apply (lc := 1) (wp_future_await (V := Loc) γf ch [K]) $$ [$Hfut $Haw]
    as %v %P %pre %post ⟨%Hsplit, HK, -⟩
  have hP : P = K := by
    rcases pre with _ | ⟨x, pre⟩
    · simp at Hsplit; exact Hsplit.1.symm
    · simp at Hsplit
  subst hP
  icases HK with ⟨%o', %err, #Hfv, #Hov, Herr, Hpost⟩
  iunfold ticket at Ho
  iunfold ticket at Hov
  ihave %Hoo := ghostMapElem_agree () γt _ _ o o' $$ Ho Hov
  subst Hoo
  iunfold callPost at Hpost
  iunfold sendRes at Hres
  icases Hpost with (⟨%Hnil, #Hsent, HΦ1⟩ | ⟨%msg, ⟨%Hmsg, %Herrm⟩, #Hsent, HΦ1, HD1⟩ |
    ⟨⟨%Hne, %Hns⟩, #Hea, Hrest⟩)
  · icases Hres with (HR | ⟨-, Hun⟩)
    · wp_auto
      iapply HΦ
      ileft
      iframe HR HΦ1
      ipureintro; exact Hnil
    · ihave Hf : (|={⊤}=> False : IProp GF) $$ [Hlc1 Hun]
      · iapply unsent_reqSent W a cn γ.conn o $$ [$Hrpc $Hlc1 $Hun $Hsent]
      imod Hf with %Hf
      exact Hf.elim
  · icases Hres with (HR | ⟨-, Hun⟩)
    · wp_auto
      iapply HΦ
      iright; ileft
      iexists msg
      iframe HR HΦ1 HD1
      isplitr
      · ipureintro; exact ⟨Hmsg, Herrm⟩
      subst Herrm
      iapply errMsg_serverErr
    · ihave Hf : (|={⊤}=> False : IProp GF) $$ [Hlc1 Hun]
      · iapply unsent_reqSent W a cn γ.conn o $$ [$Hrpc $Hlc1 $Hun $Hsent]
      imod Hf with %Hf
      exact Hf.elim
  · icases Hres with (HR | ⟨HE, Hun⟩)
    · wp_auto
      iapply HΦ
      iright; iright
      iframe Hea
      isplitr
      · ipureintro; exact ⟨Hne, Hns⟩
      ileft
      iframe HR
      icases Hrest with (HD1 | ⟨-, HT⟩)
      · ileft; iexact HD1
      · iright; iexact HT
    · icases Hrest with (HD1 | ⟨#Hsent, -⟩)
      · wp_auto
        iapply HΦ
        iright; iright
        iframe Hea
        isplitr
        · ipureintro; exact ⟨Hne, Hns⟩
        iright
        iframe HE HD1
      · ihave Hf : (|={⊤}=> False : IProp GF) $$ [Hlc1 Hun]
        · iapply unsent_reqSent W a cn γ.conn o $$ [$Hrpc $Hlc1 $Hun $Hsent]
        imod Hf with %Hf
        exact Hf.elim

end proof

end net.rpc
end Perennial
