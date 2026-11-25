/- Lean-first (no Rocq counterpart).

# `clientStream`'s proof (the section client-stream)

The loop sends the random word `v` one byte per request; while every `Send` succeeds the sender's
token is at the pieces sent, whose concatenation is the prefix of `v` sent so far (and at most 16 of
them, `csUp`: `v` is at most 16 letters). A failed `Send` ends the section. `CloseAndRecv` closes the
up queue after all the pieces (`upClosed γ S`) and receives the reply, whose content (`strmSpec csDn`)
is the concatenation of the requests the stream was closed after: `S` (`dghostVar_agree`), so `v`.
An error is a status error or `io.EOF`'s value, which `checkErr` takes.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.clientStream
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__ClientStream
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.context.Background
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Proof.context.LibKeysChain
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem clientStream.wp_proof (wp_randomWord : randomWord.spec (GF := GF) (hG := hG))
    (wp_checkErr : checkErr.spec (GF := GF) (hG := hG))
    (wp_CS : svc.driverClient.ClientStream.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG)) :
    clientStream.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as #Hcli
  iunfold drvCli at Hcli
  icases Hcli with ⟨#Hpkg, #Hf, -, %conn, #Hstub, #Hconn, -, -, -, #Hstrm⟩
  iunfold drvStubAt at Hstub
  icases Hstub with ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  iunfold drvStrmFacts at Hstrm
  icases Hstrm with ⟨⟨%d, #Hopts, %hnone⟩, -, #Hcs, -⟩
  ihave #Hsvc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  have hshape : ∀ err, streamErrShape (GF := GF) d err = grpcErrShape err := by
    intro err; unfold streamErrShape; rw [hnone]
  wp_auto
  wp_apply wp_Background
  try wp_auto
  let cd : context.ContextDesc (IProp GF) :=
    { Values := ∅, Deadline := none, Done_gn := ⟨γid, γid⟩, PDone := iprop(True) }
  ihave #Hctx : ctxOk context.backgroundCtxVal cd $$ []
  · iapply ctxOk_of_quiet
    isplitl
    · iapply drv_ctxQuiet_background
    · iapply metadata.outgoingCtxOkC_background
  wp_apply (wp_CS dc conn [drvAddr] d csUp (fun _ => strmSpec csDn) context.backgroundCtxVal cd
      none) $$ [] as %cs %err Hres
  · isplitr
    · iexact Hcc
    isplitr
    · iexact Hconn
    isplitr
    · iexact Hopts
    isplitr
    · ipureintro; exact hnone
    isplitr
    · iexact Hcs
    isplitr
    · iexact Hctx
    iapply metadata.outMD_background
  icases Hres with (⟨%He, %γ, %Dn, %cd', Hw, #Hcar, HSt, HRt, #HSpec⟩ | ⟨%Hcsn, #Herr⟩)
  · subst He
    iunfold cliBidiStreamIs at Hw
    icases Hw with ⟨%ci, %Hci, #HSend, -, -, -⟩
    subst Hci
    iunfold svc.carOk at Hcar
    icases Hcar with ⟨%ci', %Hci', #HCar⟩
    have hci : ci = ci' := by injection Hci'
    subst hci
    try wp_auto
    wp_apply wp_randomWord as %v %Hw
    have hv16 : v.length ≤ 16 := Hw.1
    try wp_auto
    ihave IH : iprop(∃ (k : w64) (S : List GoString), "i" ∷ i_ptr ↦ k ∗
        "HSt" ∷ cliSendTok (Req := strmMsg (GF := GF)) γ S ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ v.length ∧ S.length = sint.nat k ∧
          S.flatten = v.take (sint.nat k)⌝) $$ [i HSt]
    · iexists W64 0, []
      iframe
      ipureintro
      refine ⟨by word, by simp, by first | rfl | decide | simp, by first | rfl | simp⟩
    wp_for IH
    try wp_auto
    wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len v)
      as %Hslen
    wp_if_destruct
    · have hc : sint.Z k < sint.Z (W64 (v.length : Int)) := of_decide_eq_true (go.intoVal_inj Hif)
      split
      · rename_i hb
        have h1 : sint.nat (k + W64 1) - sint.nat k = 1 := by word
        rw [h1]
        try wp_auto
        wp_apply wp_String stringValueMax ((v.drop (sint.nat k)).take 1)
          (Nat.lt_of_le_of_lt (List.length_take_le _ _) (by decide)) as %l Hl
        try wp_auto
        wp_bind (App (Val #(methods ci.ty go!"Send" ci.v)) _)
        iapply HSend $$ %S %l %((v.drop (sint.nat k)).take 1) %iprop(True) [HSt Hl]
        · isplitr
          · ipureintro; trivial
          isplitr
          · itrivial
          isplitl [HSt]
          · iexact HSt
          isplitl [Hl]
          · iexact Hl
          isplitr
          · unfold csUp
            ipureintro
            exact ⟨List.length_take_le _ _, by rw [Hk.2.2.1]; word⟩
          ipureintro
          simp only [strmMsg, pbStringValueS, stringValueWireLen, grpcMsgMax]
          have := List.length_take_le 1 (v.drop (sint.nat k))
          omega
        iintro !> %err1 ⟨-, -, Hres1⟩
        icases Hres1 with (⟨%He1, HSt⟩ | ⟨#Hce1, -⟩)
        · subst He1
          wp_auto
          wp_for_post
          iframe
          iexists k + 1, S ++ [(v.drop (sint.nat k)).take 1]
          iframe
          ipureintro
          have hk1 : sint.nat (k + 1) = sint.nat k + 1 := by word
          refine ⟨by word, by word, by simp [Hk.2.2.1]; word, ?_⟩
          rw [List.flatten_append, Hk.2.2.2, hk1, List.take_add]
          simp
        · ihave #Hce1' := Hce1
          iunfold cliStreamErr at Hce1'
          icases Hce1' with ⟨%Hne, -⟩
          cases err1 with
          | nil => exact absurd rfl Hne.1
          | ok e =>
            wp_auto
            wp_for_post
            iapply HΦ
            itrivial
      · rename_i hb
        exfalso
        apply hb
        refine ⟨by word, by word, by word⟩
    · -- every byte sent: close and receive the reply
      have hc : decide (sint.Z k < sint.Z (W64 (v.length : Int))) = false := by
        cases h : decide (sint.Z k < sint.Z (W64 (v.length : Int)))
        · rfl
        · rw [h] at Hif; exact absurd rfl Hif
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hkv : sint.nat k = v.length := by
        have := of_decide_eq_false hc
        word
      have hSv : S.flatten = v := by rw [Hk.2.2.2, hkv, List.take_length]
      try simp only [decide_true, ↓reduceIte, ite_true]
      try rw [if_pos (decide_eq_true trivial)]
      try wp_auto
      wp_bind (App (Val #(methods ci.ty go!"CloseAndRecv" ci.v)) _)
      iapply HCar $$ %S [HSt HRt]
      · iframe
      iintro !> %resp %err2 ⟨#Hcl, Hres2⟩
      icases Hres2 with (⟨%He2, %a, %md, %m, ⟨%Ha, #HMd⟩, Hm, HDn⟩ | ⟨%Hne, Hres2⟩)
      · subst He2
        ihave #Hsp := HSpec $$ %a %md %Ha HMd
        iunfold strmSpec at Hsp
        ihave Hcd := Hsp $$ %0 %m HDn
        iunfold csDn at Hcd
        icases Hcd with ⟨-, %L, #HclL, %HmL⟩
        iunfold upClosed at Hcl
        iunfold upClosed at HclL
        ihave %Heq := dghostVar_agree γ.upEnd S DFrac.discard L DFrac.discard $$ Hcl HclL
        subst Heq
        have hmv : m = v := by rw [HmL, hSv]
        subst hmv
        isimp only [strmMsg, pbStringValueS, stringValueSend, stringValueSendB] at Hm
        icases Hm with ⟨%sv, Hsv, %Hsvp⟩
        obtain ⟨hval, -, -⟩ := Hsvp
        icases typedPointsto_split _ _ _ $$ Hsv with Hsv
        simp only [TypedPointsto.typedPointstoDef]
        icases Hsv with ⟨-, HV, -, -, -⟩
        wp_auto
        rw [hval]
        try simp only [decide_true]
        try wp_auto
        iunfold drvFacts at Hf
        icases Hf with ⟨%f, #Hfg, #Hfwp⟩
        try wp_auto
        try wp_bind (App (Val #f) (Val _))
        iapply wp_wand $$ (Hfwp $$ %go!"client-stream")
        iintro %u %Hu
        subst Hu
        try wp_auto
        iapply HΦ
        itrivial
      · cases err2 with
        | nil => exact absurd rfl Hne
        | ok ei =>
          icases Hres2 with (#Heof | #Hce2)
          · wp_auto
            wp_apply wp_checkErr _ $$ []
            · iframe #
              iapply svc.eof_statusErrOk
              iframe #
            try wp_auto
            iapply HΦ
            itrivial
          · iunfold cliStreamErr at Hce2
            icases Hce2 with ⟨-, #Hso, -, -, #Hsh⟩
            isimp only [streamErrShape, hnone, grpcErrShape] at Hsh
            try rw [hshape]
            wp_auto
            wp_apply wp_checkErr _ $$ []
            · iframe #
            try wp_auto
            iapply HΦ
            itrivial
  · ihave #Herr' := Herr
    iunfold cliStreamErr at Herr'
    icases Herr' with ⟨%Hne, #Hso, -, -, #Hsh⟩
    isimp only [streamErrShape, hnone, grpcErrShape] at Hsh
    try rw [hshape]
    subst Hcsn
    cases err with
    | nil => exact absurd rfl Hne.1
    | ok ei =>
      try wp_auto
      wp_apply wp_checkErr _ $$ []
      · iframe #
      try wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
