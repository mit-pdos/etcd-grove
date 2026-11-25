/- Lean-first (no Rocq counterpart).

# `serverStream`'s proof (the section server-stream)

The stub sends the random word `v` as the stream's first request (`upLb γ [v]`). Each response the
client receives, at position `j`, has the stream's content (`strmSpec ssDn`): the `j`th byte of the
first request (`ssDn`), which is `v` (`mono_list_lb_idx_lookup`); so the concatenation of the `n`
responses received is `v.take n`, a prefix of `v`. `io.EOF` ends the section; another error is a status
error (the stream's errors, grpc's own shape on a connection with no stream interceptor) or `io.EOF`'s
value, both of which `checkErr` takes.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.serverStream
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__ServerStream
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.context.Background
public import Perennial.Spec.strings.HasPrefix
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

theorem serverStream.wp_proof (wp_randomWord : randomWord.spec (GF := GF) (hG := hG))
    (wp_checkErr : checkErr.spec (GF := GF) (hG := hG))
    (wp_SS : svc.driverClient.ServerStream.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    serverStream.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as #Hcli
  iunfold drvCli at Hcli
  icases Hcli with ⟨#Hpkg, #Hf, -, %conn, #Hstub, #Hconn, -, -, -, #Hstrm, -⟩
  iunfold drvStubAt at Hstub
  icases Hstub with ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  iunfold drvStrmFacts at Hstrm
  icases Hstrm with ⟨⟨%d, #Hopts, %hnone⟩, #Hss, -, -⟩
  ihave #Hsvc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Heofp, #-, #Hmsg⟩
  have hshape : ∀ err, streamErrShape (GF := GF) d err = grpcErrShape err := by
    intro err; unfold streamErrShape; rw [hnone]
  wp_auto
  wp_apply wp_randomWord as %v %Hw
  try wp_auto
  wp_apply wp_Background
  try wp_auto
  wp_apply wp_String stringValueMax v (by
      have := Hw.1; unfold stringValueMax; omega) as %inp Hinp
  try wp_auto
  let cd : context.ContextDesc (IProp GF) :=
    { Values := ∅, Deadline := none, Done_gn := ⟨γid, γid⟩, PDone := iprop(True) }
  ihave #Hctx : ctxOk context.backgroundCtxVal cd $$ []
  · iapply ctxOk_of_quiet
    isplitl
    · iapply drv_ctxQuiet_background
    · iapply metadata.outgoingCtxOkC_background
  wp_apply (wp_SS dc conn [drvAddr] d ssUp (fun _ => strmSpec ssDn) context.backgroundCtxVal cd none
      inp v) $$ [Hinp] as %cs %err Hres
  · isplitr
    · iexact Hcc
    isplitr
    · iexact Hconn
    isplitr
    · iexact Hopts
    isplitr
    · ipureintro; exact hnone
    isplitr
    · iexact Hss
    isplitr
    · iexact Hctx
    isplitr
    · iapply metadata.outMD_background
    isplitl [Hinp]
    · iexact Hinp
    unfold ssUp
    ipureintro; rfl
  icases Hres with (⟨%He, %γ, %Dn, %cd', Hw, #Hlb, -, HRt, #HSpec⟩ | ⟨%Hcs, #Herr⟩)
  · -- the stream: its responses
    subst He
    iunfold cliBidiStreamIs at Hw
    icases Hw with ⟨%ci, %Hci, -, #HRecv, -, -⟩
    subst Hci
    try wp_auto
    ihave IH : iprop(∃ (L : List GoString) (g : GoString), "got" ∷ got_ptr ↦ g ∗
        "HRt" ∷ cliRecvTok (Rep := strmMsg (GF := GF)) γ L ∗
        "%Hg" ∷ ⌜g = v.take L.length ∧ L.length ≤ v.length⌝) $$ [got HRt]
    · iexists [], go!""
      iframe
      ipureintro
      exact ⟨by simp, by simp⟩
    wp_for IH
    try rw [if_pos (decide_eq_true rfl)]
    try wp_auto
    wp_bind (App (Val #(methods ci.ty go!"Recv" ci.v)) _)
    iapply HRecv $$ %L %iprop(True) [HRt]
    · isplitr
      · ipureintro; trivial
      isplitr
      · itrivial
      iexact HRt
    iintro !> %resp %err2 ⟨-, Hres2⟩
    icases Hres2 with (⟨%He2, %a, %md, %m, ⟨%Ha, #HMd⟩, -, Hm, HDn, HRt⟩ |
      ⟨%Hnull, #Heof, %Hne, -, -⟩ | ⟨%Hnull, #Hce, -⟩)
    · -- a response: the next byte of `v`
      subst He2
      ihave #Hsp := HSpec $$ %a %md %Ha HMd
      iunfold strmSpec at Hsp
      ihave Hss' := Hsp $$ %L.length %m HDn
      iunfold ssDn at Hss'
      icases Hss' with ⟨%v', #Hat, %Hv'⟩
      iunfold upAt at Hat
      ihave %Hlk := mono_list_lb_idx_lookup γ.up [v] 0 v' (by simp) $$ [Hlb] Hat
      · iunfold upLb at Hlb; iexact Hlb
      have hvv : v' = v := by simpa using Hlk.symm
      subst hvv
      obtain ⟨hlt, rfl⟩ := Hv'
      isimp only [strmMsg, pbStringValueS, stringValueSend, stringValueSendB] at Hm
      icases Hm with ⟨%sv, Hsv, %Hsvp⟩
      obtain ⟨hval, -, -⟩ := Hsvp
      icases typedPointsto_split _ _ _ $$ Hsv with Hsv
      simp only [TypedPointsto.typedPointstoDef]
      icases Hsv with ⟨-, HV, -, -, -⟩
      wp_auto
      rw [hval]
      wp_apply wp_HasPrefix $$ [$Hstr]
      have hpre : g ++ List.take 1 (List.drop L.length v') = v'.take (L.length + 1) := by
        rw [Hg.1, List.take_add]
      rw [hpre, decide_eq_true (List.take_prefix _ _)]
      try wp_auto
      wp_for_post
      iframe
      iexists L ++ [List.take 1 (List.drop L.length v')], v'.take (L.length + 1)
      iframe
      ipureintro
      exact ⟨by simp, by simp; omega⟩
    · -- `io.EOF`: the end
      iunfold eofIs at Heof
      icombine Heof Heofp gives %Heq
      subst Heq
      wp_auto
      iunfold drvFacts at Hf
      icases Hf with ⟨%f, #Hfg, #Hfwp⟩
      try wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hfwp $$ %go!"server-stream")
      iintro %u %Hu
      subst Hu
      try wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    · -- another error: `io.EOF`'s value (the end), or a status error
      ihave #Hce' := Hce
      iunfold cliStreamErr at Hce'
      icases Hce' with ⟨%Hne, #Hso, -, #Hse, #Hsh⟩
      isimp only [streamErrShape, hnone, grpcErrShape] at Hsh
      try rw [hshape]
      cases err2 with
      | nil => exact absurd rfl Hne.1
      | ok ei =>
        iunfold streamErr at Hse
        icases Hse with ⟨-, #Htree⟩
        ihave ⟨%Sx, %Mx, -, %HS⟩ := Htree $$
          %(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x)
        have htt := HS.2 (fun tii h => by cases h; exact ⟨_, x, rfl, rfl⟩)
        by_cases hty : ei.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty
        · obtain ⟨l, hl⟩ := htt ei ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
            HS.1 rfl hty
          obtain ⟨ety, ev⟩ := ei
          simp only at hty hl
          subst hty hl
          wp_auto
          try rw [if_pos rfl]
          try wp_auto
          by_cases hlx : l = x
          · rw [decide_eq_true hlx]
            try wp_auto
            iunfold drvFacts at Hf
            icases Hf with ⟨%f, #Hfg, #Hfwp⟩
            try wp_auto
            try wp_bind (App (Val #f) (Val _))
            iapply wp_wand $$ (Hfwp $$ %go!"server-stream")
            iintro %u %Hu
            subst Hu
            try wp_auto
            wp_for_post
            iapply HΦ
            itrivial
          · rw [decide_eq_false hlx]
            try wp_auto
            wp_apply wp_checkErr _ $$ []
            · iframe #
            try wp_auto
            wp_for_post
            iapply HΦ
            itrivial
        · wp_auto
          try rw [if_neg hty]
          try wp_auto
          wp_apply wp_checkErr _ $$ []
          · iframe #
          try wp_auto
          wp_for_post
          iapply HΦ
          itrivial
  · -- the stream's error
    ihave #Herr' := Herr
    iunfold cliStreamErr at Herr'
    icases Herr' with ⟨%Hne, #Hso, -, -, #Hsh⟩
    isimp only [streamErrShape, hnone, grpcErrShape] at Hsh
    try rw [hshape]
    subst Hcs
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
