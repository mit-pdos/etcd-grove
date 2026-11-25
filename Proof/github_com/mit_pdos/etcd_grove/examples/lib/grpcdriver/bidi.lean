/- Lean-first (no Rocq counterpart).

# `bidi`'s proof (the section bidi-stream)

The loop sends the random word `v` one byte per request; `sent` counts every piece it tried to send
(a failed `Send` may have delivered its piece), and the sender's token stays at pieces `T` whose
concatenation is a prefix of `sent` (all of them, or all but the last). Each response the client then
receives, at position `j`, has the stream's content (`strmSpec biDn`): the `j`th request (`biDn`),
which the token, still the client's, says is `T`'s `j`th piece (`mono_list_auth_idx_lookup`); so what
was received is a prefix of `T`'s concatenation, so of `sent`. An error is a status error or `io.EOF`'s
value, which `checkErr` takes.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.bidi
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Bidi
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.context.Background
public import Perennial.Spec.strings.HasPrefix
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Proof.context.LibKeysChain
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

/-- The concatenation of a prefix of a list of strings is a prefix of the concatenation. -/
theorem flatten_take_prefix (T : List GoString) (n : Nat) : (T.take n).flatten <+: T.flatten := by
  conv => rhs; rw [← List.take_append_drop n T]
  rw [List.flatten_append]
  exact List.prefix_append _ _

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- The sender's token and the `i`th request sent: the token stays, and the request is its `i`th. -/
theorem sendTok_upAt_lookup {Req : StreamMsg GF} (γ : StreamNames) (T : List Req.M) (i : Nat)
    (m : Req.M) :
    cliSendTok (GF := GF) γ T ∗ upAt γ i m ⊢ cliSendTok γ T ∗ ⌜T[i]? = some m⌝ := by
  have h : cliSendTok (GF := GF) γ T ∗ upAt γ i m ⊢ ⌜T[i]? = some m⌝ := by
    unfold cliSendTok upAt
    iintro ⟨H1, H2⟩
    iapply (mono_list_auth_idx_lookup γ.up _ T i m) $$ H1 H2
  refine (persistent_entails_left h).trans ?_
  iintro ⟨⟨H1, -⟩, %hp⟩
  isplitl [H1]
  · iexact H1
  · ipureintro; exact hp

theorem sendTok_upAt_lookup' {Req : StreamMsg GF} (γ : StreamNames) (T : List Req.M) (i : Nat)
    (m : Req.M) :
    ⊢ cliSendTok (GF := GF) γ T -∗ upAt γ i m -∗ cliSendTok γ T ∗ ⌜T[i]? = some m⌝ := by
  iintro H1 H2
  iapply (sendTok_upAt_lookup γ T i m)
  isplitl [H1]
  · iexact H1
  · iexact H2

theorem bidi.wp_proof (wp_randomWord : randomWord.spec (GF := GF) (hG := hG))
    (wp_checkErr : checkErr.spec (GF := GF) (hG := hG))
    (wp_Bi : svc.driverClient.Bidi.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    bidi.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids
  wp_start as #Hcli
  iunfold drvCli at Hcli
  icases Hcli with ⟨#Hpkg, #Hf, -, %conn, #Hstub, #Hconn, -, -, -, #Hstrm⟩
  iunfold drvStubAt at Hstub
  icases Hstub with ⟨%dc, %Hc, #Hcc⟩
  subst Hc
  iunfold drvStrmFacts at Hstrm
  icases Hstrm with ⟨⟨%d, #Hopts, %hnone⟩, -, -, #Hbis⟩
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
  wp_apply wp_Background
  try wp_auto
  let cd : context.ContextDesc (IProp GF) :=
    { Values := ∅, Deadline := none, Done_gn := ⟨γid, γid⟩, PDone := iprop(True) }
  ihave #Hctx : ctxOk context.backgroundCtxVal cd $$ []
  · iapply ctxOk_of_quiet
    isplitl
    · iapply drv_ctxQuiet_background
    · iapply metadata.outgoingCtxOkC_background
  wp_apply (wp_Bi dc conn [drvAddr] d biUp (fun _ => strmSpec biDn) context.backgroundCtxVal cd
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
    · iexact Hbis
    isplitr
    · iexact Hctx
    iapply metadata.outMD_background
  icases Hres with (⟨%He, %γ, %Dn, %cd', Hw, HSt, HRt, #HSpec⟩ | ⟨%Hcsn, #Herr⟩)
  · subst He
    iunfold cliBidiStreamIs at Hw
    icases Hw with ⟨%ci, %Hci, #HSend, #HRecv, #HClose, -⟩
    subst Hci
    try wp_auto
    wp_apply wp_randomWord as %v %Hw
    try wp_auto
    ihave IH : iprop(∃ (k : w64) (S : List GoString), "i" ∷ i_ptr ↦ k ∗ "sent" ∷ sent_ptr ↦ S.flatten ∗
        "HSt" ∷ cliSendTok (Req := strmMsg (GF := GF)) γ S ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ v.length ∧ S.flatten = v.take (sint.nat k)⌝) $$ [i sent HSt]
    · iexists W64 0, []
      iframe
      ipureintro
      refine ⟨by word, by simp, by simp⟩
    wp_for IH
    try wp_auto
    wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len v)
      as %Hslen
    wp_if_destruct
    · have hc : sint.Z k < sint.Z (W64 (v.length : Int)) := of_decide_eq_true (go.intoVal_inj Hif)
      have h1 : sint.nat (k + W64 1) - sint.nat k = 1 := by word
      split
      · rename_i hb
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
          · unfold biUp
            ipureintro
            exact List.length_take_le _ _
          ipureintro
          simp only [strmMsg, pbStringValueS, stringValueWireLen, grpcMsgMax]
          have := List.length_take_le 1 (v.drop (sint.nat k))
          omega
        iintro !> %err1 ⟨-, -, Hres1⟩
        wp_auto
        split
        · rw [h1]
          try wp_auto
          have hk1 : sint.nat (k + 1) = sint.nat k + 1 := by word
          have hcat : S.flatten ++ (v.drop (sint.nat k)).take 1 = v.take (sint.nat k + 1) := by
            rw [Hk.2.2, List.take_add]
          icases Hres1 with (⟨%He1, HSt⟩ | ⟨#Hce1, %T, %HT, HSt⟩)
          · subst He1
            wp_auto
            wp_for_post
            iframe
            iexists k + 1, S ++ [(v.drop (sint.nat k)).take 1]
            simp only [List.flatten_append, List.flatten_singleton]
            iframe
            ipureintro
            refine ⟨by word, by word, by rw [hcat, hk1]⟩
          · -- a failed `Send`: the break, with the token at `T`, a prefix of the pieces tried
            ihave #Hce1' := Hce1
            iunfold cliStreamErr at Hce1'
            icases Hce1' with ⟨%Hne, -⟩
            cases err1 with
            | nil => exact absurd rfl Hne.1
            | ok e =>
              wp_auto
              wp_for_post
              have HTs : T.flatten <+: S.flatten ++ (v.drop (sint.nat k)).take 1 := by
                rcases HT with rfl | rfl
                · exact List.prefix_append _ _
                · simp
              generalize S.flatten ++ (v.drop (sint.nat k)).take 1 = s at HTs ⊢
              ihave IH2 : iprop(∃ (L : List GoString) (g : GoString), "got" ∷ got_ptr ↦ g ∗
                  "HRt" ∷ cliRecvTok (Rep := strmMsg (GF := GF)) γ L ∗
                  "%Hg" ∷ ⌜g = (T.take L.length).flatten⌝) $$ [got HRt]
              · iexists [], go!""
                iframe
                ipureintro; simp
              wp_for IH2
              try wp_auto
              wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len g)
                as %Hgl
              wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s)
                as %Hsl
              wp_if_destruct
              · -- receive the next echo
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
                · subst He2
                  ihave #Hsp := HSpec $$ %a %md %Ha HMd
                  iunfold strmSpec at Hsp
                  ihave Hat := Hsp $$ %L.length %m HDn
                  iunfold biDn at Hat
                  ihave ⟨HSt, %Hlk⟩ := sendTok_upAt_lookup' γ _ L.length _ $$ HSt Hat
                  isimp only [strmMsg, pbStringValueS, stringValueSend, stringValueSendB] at Hm
                  icases Hm with ⟨%sv, Hsv, %Hsvp⟩
                  obtain ⟨hval, -, -⟩ := Hsvp
                  icases typedPointsto_split _ _ _ $$ Hsv with Hsv
                  simp only [TypedPointsto.typedPointstoDef]
                  icases Hsv with ⟨-, HV, -, -, -⟩
                  wp_auto
                  rw [hval]
                  wp_apply wp_HasPrefix $$ [$Hstr]
                  have hlt : L.length < T.length := by
                    rcases Nat.lt_or_ge L.length T.length with h | h
                    · exact h
                    · rw [List.getElem?_eq_none h] at Hlk; cases Hlk
                  have hpre : g ++ m = (T.take (L.length + 1)).flatten := by
                    rw [Hg, List.take_add_one, List.flatten_append, Hlk]
                    simp
                  rw [hpre, decide_eq_true ((flatten_take_prefix T _).trans HTs)]
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists L ++ [m], (T.take (L.length + 1)).flatten
                  iframe
                  ipureintro
                  simp
                · iunfold eofIs at Heof
                  icombine Heof Heofp gives %Heq
                  subst Heq
                  wp_auto
                  iunfold drvFacts at Hf
                  icases Hf with ⟨%f, #Hfg, #Hfwp⟩
                  try wp_auto
                  try wp_bind (App (Val #f) (Val _))
                  iapply wp_wand $$ (Hfwp $$ %go!"bidi-stream")
                  iintro %u %Hu
                  subst Hu
                  try wp_auto
                  wp_for_post
                  iapply HΦ
                  itrivial
                · ihave #Hce' := Hce
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
                        iapply wp_wand $$ (Hfwp $$ %go!"bidi-stream")
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
              · -- all received: close, and the section is done
                try simp only [Hif, decide_false, decide_true, eq_self_iff_true, Bool.false_eq_true, ↓reduceIte, ite_false, ite_true]
                try wp_auto
                wp_bind (App (Val #(methods ci.ty go!"CloseSend" ci.v)) _)
                iapply HClose $$ %T %iprop(True) [HSt]
                · isplitr
                  · ipureintro; trivial
                  isplitr
                  · itrivial
                  iexact HSt
                iintro !> %err3 -
                try wp_auto
                iunfold drvFacts at Hf
                icases Hf with ⟨%f, #Hfg, #Hfwp⟩
                try wp_auto
                try wp_bind (App (Val #f) (Val _))
                iapply wp_wand $$ (Hfwp $$ %go!"bidi-stream")
                iintro %u %Hu
                subst Hu
                try wp_auto
                iapply HΦ
                itrivial
        · rename_i hb2
          exfalso
          apply hb2
          refine ⟨by word, by word, by word⟩
      · rename_i hb
        exfalso
        apply hb
        refine ⟨by word, by word, by word⟩
    · -- every piece sent: the token at `S`, whose concatenation is `sent`
      have hc : decide (sint.Z k < sint.Z (W64 (v.length : Int))) = false := by
        cases h : decide (sint.Z k < sint.Z (W64 (v.length : Int)))
        · rfl
        · rw [h] at Hif; exact absurd rfl Hif
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      generalize hs : S.flatten = s
      have HTs : S.flatten <+: s := by rw [hs]; exact List.prefix_refl _
      generalize hT : S = T at HTs ⊢
      ihave IH2 : iprop(∃ (L : List GoString) (g : GoString), "got" ∷ got_ptr ↦ g ∗
          "HRt" ∷ cliRecvTok (Rep := strmMsg (GF := GF)) γ L ∗
          "%Hg" ∷ ⌜g = (T.take L.length).flatten⌝) $$ [got HRt]
      · iexists [], go!""
        iframe
        ipureintro; simp
      wp_for IH2
      try wp_auto
      wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len g)
        as %Hgl
      wp_apply (_root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len s)
        as %Hsl
      wp_if_destruct
      · -- receive the next echo
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
        · subst He2
          ihave #Hsp := HSpec $$ %a %md %Ha HMd
          iunfold strmSpec at Hsp
          ihave Hat := Hsp $$ %L.length %m HDn
          iunfold biDn at Hat
          ihave ⟨HSt, %Hlk⟩ := sendTok_upAt_lookup' γ _ L.length _ $$ HSt Hat
          isimp only [strmMsg, pbStringValueS, stringValueSend, stringValueSendB] at Hm
          icases Hm with ⟨%sv, Hsv, %Hsvp⟩
          obtain ⟨hval, -, -⟩ := Hsvp
          icases typedPointsto_split _ _ _ $$ Hsv with Hsv
          simp only [TypedPointsto.typedPointstoDef]
          icases Hsv with ⟨-, HV, -, -, -⟩
          wp_auto
          rw [hval]
          wp_apply wp_HasPrefix $$ [$Hstr]
          have hlt : L.length < T.length := by
            rcases Nat.lt_or_ge L.length T.length with h | h
            · exact h
            · rw [List.getElem?_eq_none h] at Hlk; cases Hlk
          have hpre : g ++ m = (T.take (L.length + 1)).flatten := by
            rw [Hg, List.take_add_one, List.flatten_append, Hlk]
            simp
          rw [hpre, decide_eq_true ((flatten_take_prefix T _).trans HTs)]
          try wp_auto
          wp_for_post
          iframe
          iexists L ++ [m], (T.take (L.length + 1)).flatten
          iframe
          ipureintro
          simp
        · iunfold eofIs at Heof
          icombine Heof Heofp gives %Heq
          subst Heq
          wp_auto
          iunfold drvFacts at Hf
          icases Hf with ⟨%f, #Hfg, #Hfwp⟩
          try wp_auto
          try wp_bind (App (Val #f) (Val _))
          iapply wp_wand $$ (Hfwp $$ %go!"bidi-stream")
          iintro %u %Hu
          subst Hu
          try wp_auto
          wp_for_post
          iapply HΦ
          itrivial
        · ihave #Hce' := Hce
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
                iapply wp_wand $$ (Hfwp $$ %go!"bidi-stream")
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
      · -- all received: close, and the section is done
        try simp only [Hif, decide_false, decide_true, eq_self_iff_true, Bool.false_eq_true, ↓reduceIte, ite_false, ite_true]
        try wp_auto
        wp_bind (App (Val #(methods ci.ty go!"CloseSend" ci.v)) _)
        iapply HClose $$ %T %iprop(True) [HSt]
        · isplitr
          · ipureintro; trivial
          isplitr
          · itrivial
          iexact HSt
        iintro !> %err3 -
        try wp_auto
        iunfold drvFacts at Hf
        icases Hf with ⟨%f, #Hfg, #Hfwp⟩
        try wp_auto
        try wp_bind (App (Val #f) (Val _))
        iapply wp_wand $$ (Hfwp $$ %go!"bidi-stream")
        iintro %u %Hu
        subst Hu
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
