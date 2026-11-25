/-
The proof of `Client.Call.spec_closed` (`Net/Spec/net/rpc/Client__Call.lean`): `Client.Call`'s proof
(`Client__Call.lean`) with `Go`'s refusal (`Client.Go.spec_closed`), for trivial continuation,
decoding and decoding resource: the ticket is `none`, so the outcome the channel carries
(`callPost` at no number) is an error, not a `ServerError` (the answers need `reqSent`, false at no
number).
-/
module

public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Go

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

/-- Two `isChan` of one channel agree on its capacity (`isChan_cap_agree` of `Client__Call.lean`,
which this proof cannot import). -/
private theorem isChan_cap_agree' (ch : Loc) (γ1 γ2 : ChanNames) :
    isChan (GF := GF) ch γ1 Loc ∗ isChan ch γ2 Loc ⊢ ⌜γ1.chanCap = γ2.chanCap⌝ := by
  rw [isChan_unseal]
  unfold isChanDef
  iintro ⟨⟨%m1, #Hc1, -⟩, ⟨%m2, #Hc2, -⟩⟩
  icombine Hc1 Hc2 gives %H
  ipureintro; exact H

theorem Client.Call.wp_proof_closed (wp_Go : Client.Go.spec_closed (GF := GF) (hG := hG)) :
    Client.Call.spec_closed (GF := GF) (hG := hG) := by
  intro c W a sm args reply
  wp_start as ⟨#Hcl, #Hclo⟩
  iunfold isClient at Hcl
  icases Hcl with ⟨%γ, #Hcl⟩
  wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 1)) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Loc) ch γc (.Buffered []) (.inr rfl) $$ Hch Hoc with ⟨%γf, #Hfut, Haw⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := Option Nat) with ⟨%γt, Hγt⟩
  let Φm : List w8 → GoString → IProp GF := fun _ _ => iprop(True)
  let Θ : List w8 → Bool → IProp GF := fun _ _ => iprop(True)
  let K : Loc → IProp GF := fun v => iprop(∃ (o : Option Nat) (err : GoInterface),
    callFields v sm args reply ch ∗ ticket γt o ∗
    structFieldRef net.rpc.Call go!"Error" v ↦ err ∗ callPost γ.conn o Φm Θ iprop(True) err)
  imod future_alloc_promise γf ch K [] $$ Hfut Haw with ⟨Hful, Haw⟩
  ihave %Hcapf := isChan_cap_agree' ch γc γf.chanName $$ [Hch Hfut]
  · iframe Hch; iunfold isFuture at Hfut; icases Hfut with ⟨$, -⟩
  have hcap : γf.chanName.chanCap = W64 1 := Hcapf ▸ Hcap
  ihave %Hchn := isChan_not_null $$ Hch
  wp_apply wp_Go c W a γ sm args reply ch γt γf K Φm iprop(True) Θ
      $$ [Hγt Hful] as %pc ⟨#Hf, #Ho⟩
  · isplitr
    · iexact Hcl
    isplitr
    · iexact Hclo
    isplitr
    · ipureintro; exact ⟨Hchn, by rw [hcap]; decide⟩
    isplitr
    · itrivial
    isplitl [Hγt]
    · iexact Hγt
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
  wp_apply (wp_future_await (V := Loc) γf ch [K]) $$ [$Hfut $Haw]
    as %v %P %pre %post ⟨%Hsplit, HK, -⟩
  have hP : P = K := by
    rcases pre with _ | ⟨x, pre⟩
    · simp at Hsplit; exact Hsplit.1.symm
    · simp at Hsplit
  subst hP
  icases HK with ⟨%o', %err, #Hfv, #Hov, Herr, Hpost⟩
  iunfold ticket at Ho
  iunfold ticket at Hov
  ihave %Hoo := ghostMapElem_agree () γt _ _ none o' $$ Ho Hov
  subst Hoo
  iunfold callPost at Hpost
  icases Hpost with (⟨-, Hsent, -⟩ | ⟨%msg, -, Hsent, -⟩ | ⟨⟨%Hne, %Hns⟩, -, -⟩)
  · iunfold reqSent at Hsent
    icases Hsent with %Hf
    exact Hf.elim
  · iunfold reqSent at Hsent
    icases Hsent with %Hf
    exact Hf.elim
  wp_auto
  iapply HΦ
  ipureintro; exact ⟨Hne, Hns⟩

end proof

end net.rpc
end Perennial
