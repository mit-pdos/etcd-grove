/-
The proof of `Encoder.Encode` on a connection (`Spec/encoding/json/Codec/Encoder__Encode_conn.lean`)
at the model's encoder representation (`encRepModel`, `EncoderModel.lean`): the sticky error is nil,
`marshalAny` encodes (`marshalVia`), no indentation is set, the encoding and a newline are written
by one `Write` on the connection (`net.Conn.Write.spec`, its steps extending `sendTok` under the
protocol: `writeP`, `write_acc`), and a write error is kept as the sticky error.
-/
module

public import Spec.encoding.json.Codec.Encoder__Encode_conn
public import Spec.encoding.json.Codec.marshalAny
public import Proof.encoding.json.EncoderModel
public import Proof.net.ErrOrNil
public import Proof.encoding.json.NetInit
public import Net.Spec.net.Conn__Write
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : encoding.json.Assumptions]
variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

attribute [local instance] encRepModel

theorem Encoder.Encode_conn.wp_proof (wp_marshalAny : marshalAny.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG)) :
    Encoder.Encode_conn.spec (GF := GF) (hG := hG) := by
  intro J F enc v w cn s a P W Ψ
  wp_start as ⟨Hvia, Henc, #Hc, Htok, Hj, Hfact⟩
  ihave ⟨%ed, #Hed⟩ := ed_of_net $$ Hpkg2
  rw [encRepModel_encOk]
  unfold encOkModel
  icases Henc with ⟨%e, He, %Hw, %Herr, %Hip, %Hiv⟩
  unfold net.isConn
  icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
  wp_auto
  rw [Herr]
  wp_auto
  wp_apply wp_marshalAny $$ [$Hpkg $Hvia $Hj] as %b %merr Hret
  unfold marshalRet
  icases Hret with (⟨%Hnil, %bs, Hb, Hcap, HΨ⟩ | ⟨%Hne, HΨ⟩)
  rotate_left
  · cases merr with
    | nil => exact absurd rfl Hne
    | ok i =>
      wp_auto
      iapply HΦ
      ileft
      iframe
      ipureintro; exact Hne
  subst Hnil
  wp_auto
  rw [Hip]
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %h1
  rw [Hiv]
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %h2
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 10]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b1 ⟨Hb1, Hcap1, -⟩
  subst Hct
  rw [Hw]
  wp_auto
  icases Hfact $$ HΨ with ⟨#Hp0, HΨ⟩
  wp_apply wp_Write t cn s a la ra b1 _ _ ed (writeP (Gg := hG.goose_globalGS) cn s P W)
      $$ [Hb1 Htok] as %nw %werr ⟨%wr, %res, Htok, Hb1, %Hwr, #HE⟩
  · iframe Hca Hb1 Hed
    isplitl [Htok]
    · iapply writeP_init $$ Htok
    · iapply write_acc cn s P W _ $$ Hp0
  ihave #Heo := net.resErr_errOrNil _ _ _ _ _ _ _ $$ HE
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
  obtain ⟨⟨z, hz0⟩, hn, hnone, -⟩ := Hwr
  unfold writeP
  cases res with
  | some k =>
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    iright
    iexists bs, wr.length
    rw [← hz0, List.take_left]
    iframe Htok HΨ Heo
    ipureintro
    constructor
    · have := congrArg List.length hz0
      simp at this; omega
    · intro h; cases h
  | none =>
    have := Hne.1 rfl
    subst this
    have hz := hnone rfl
    wp_auto
    iapply HΦ
    iright
    iexists bs, (bs ++ [W8 10]).length
    subst hz
    rw [List.take_length]
    iframe HΨ Heo Htok
    ipureintro
    simp

end proof

end encoding.json
end Perennial
