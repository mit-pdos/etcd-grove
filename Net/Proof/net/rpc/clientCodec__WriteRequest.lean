/-
The proof of `clientCodec.WriteRequest` (`Net/Spec/net/rpc/clientCodec__WriteRequest.lean`): the
sticky error first; then the header (`putU64`, `putString`), the codec's `Encode` (`encOk`), the
check against `maxFrame` (the stuck point, excluded by the caller's bounds), and the two frames
(`putFrame`), written by one `Write` through the library's writer predicate and accessor (`writeP`,
`write_acc`).
-/
module

public import Net.Spec.net.rpc.clientCodec__WriteRequest
public import Net.Spec.net.rpc.getCodec
public import Net.Spec.net.rpc.putU64
public import Net.Spec.net.rpc.putString
public import Net.Spec.net.rpc.putFrame
public import Net.Spec.net.Conn__Write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

theorem reqWire_bytes (seq : w64) (sm : GoString) (eb : List w8) :
    ([] ++ frameOf ([] ++ u64Le seq ++ strEnc sm)) ++ frameOf eb = reqWire seq sm eb := by
  simp [reqWire, reqHdr]

theorem sint_nat_lt' (x : w64) : sint.nat x < 2 ^ 63 := by
  unfold sint.nat; have := BitVec.toInt_lt (x := x); simp at this; omega

theorem reqWire_ne_nil (seq : w64) (sm : GoString) (eb : List w8) : reqWire seq sm eb ≠ [] := by
  intro h
  have := reqWire_length seq sm eb
  rw [h, List.length_nil] at this
  omega

theorem clientCodec.WriteRequest.wp_proof (wp_getCodec : getCodec.spec (GF := GF) (hG := hG))
    (wp_putU64 : putU64.spec (GF := GF) (hG := hG))
    (wp_putString : putString.spec (GF := GF) (hG := hG))
    (wp_putFrame : putFrame.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG)) :
    clientCodec.WriteRequest.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra r rv body w0 ed C Pr W0 Ψ0 Ψ
  wp_start as ⟨#Hrwc, #Hc, #Hed, Hwerr, Hr, #Hset, Htok, %Hsm, Henc, Hupd⟩
  ihave #Hpoll := net.connAt_poll _ _ _ _ _ _ $$ Hc
  wp_auto
  cases w0 with
  | ok e =>
    wp_auto
    iapply HΦ
    iframe Hr
    ileft
    iframe Hwerr Htok Henc
    ipureintro; exact ⟨fun h => (by cases h), rfl⟩
  | nil =>
  wp_auto
  ihave Hn0 := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hn0c := ownSliceCap_nil (V := w8)
  wp_apply wp_putU64 slice.nil [] rv.Seq' $$ [$Hn0 $Hn0c] as %h1 ⟨Hh1, Hh1c⟩
  wp_apply wp_putString h1 _ rv.ServiceMethod' $$ [$Hh1 $Hh1c] as %h2 ⟨Hh2, Hh2c⟩
  wp_apply wp_getCodec C $$ Hset as %cd #Hcd
  unfold codecIs
  icases Hcd with ⟨%v, #Hv, #Henc', #Hdec', -⟩
  iStructNamed Hv
  wp_auto
  unfold encOk
  wp_bind (App (Val #v.Encode') _)
  iapply Henc' $$ Henc
  inext
  iintro %sl %eb Hsl Hslc ⟨%Heb, HΨ0⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave %Hh2l := ownSlice_len $$ Hh2
  have hfit : rv.ServiceMethod'.length + 16 ≤ maxFrameN ∧ eb.length ≤ maxFrameN := ⟨Hsm, Heb⟩
  have hh2 : sint.nat h2.len ≤ 2 ^ 30 := by
    simp [strEnc_length, u64Le_length] at Hh2l
    unfold maxFrameN at Hsm
    omega
  have hsl : sint.nat sl.len ≤ 2 ^ 30 := by
    unfold maxFrameN at Heb
    omega
  wp_auto
  -- the check against `maxFrame`: neither frame is too long (the caller's bounds)
  wp_if_destruct
  · exfalso
    rename_i Hif
    have : sint.nat h2.len = (sint.Z h2.len).toNat := rfl
    word
  wp_if_destruct
  · exfalso
    rename_i Hif
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    word
  ihave Hn1 := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hn1c := ownSliceCap_nil (V := w8)
  wp_apply wp_putFrame slice.nil [] h2 (DFrac.own 1) _ $$ [$Hn1 $Hn1c $Hh2] as %b1 ⟨Hb1, Hb1c, Hh2⟩
  ihave Hupd := Hupd $$ %trivial
  unfold reqUpd
  imod Hupd $$ %eb %hfit HΨ0 with ⟨#Hproto, HΨ⟩
  wp_apply wp_putFrame b1 _ sl (DFrac.own 1) eb $$ [$Hb1 $Hb1c $Hsl] as %b2 ⟨Hb2, Hb2c, Hsl⟩
  rw [reqWire_bytes]
  ihave Hw0 := writeP_init (Gg := hG.goose_globalGS) cn s Pr W0 $$ Htok
  ihave #Hacc := write_acc (Gg := hG.goose_globalGS) cn s Pr W0
    (reqWire rv.Seq' rv.ServiceMethod' eb) $$ Hproto
  wp_apply wp_Write t cn s a la ra b2 (reqWire rv.Seq' rv.ServiceMethod' eb) (DFrac.own 1) ed
      (writeP (Gg := hG.goose_globalGS) cn s Pr W0) $$ [$Hpoll $Hc $Hb2 $Hed $Hw0 $Hacc]
    as %n %err ⟨%w, %res, Hw, Hb2, ⟨%Hpre, %Hn, %Hnone, %Hall⟩, #Herr⟩
  unfold writeP
  cases res with
  | none =>
    unfold net.resErr
    icases Herr with %Herr
    subst Herr
    have hw := Hnone rfl
    subst hw
    wp_auto
    iapply HΦ
    iframe Hr
    iright
    isplitr
    · ipureintro; trivial
    iexists eb
    iframe HΨ
    ileft
    iframe Hwerr Hw
    ipureintro; rfl
  | some k =>
    ihave %Hnet := net.resErr_netErr (some k) go!"write" la ra (some ed) (· = go!"write") err $$ Herr
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    wp_auto
    iapply HΦ
    iframe Hr
    iright
    isplitr
    · ipureintro; trivial
    iexists eb
    iframe HΨ
    iright
    iexists w, k
    iframe Hwerr Hw Herr
    ipureintro
    refine ⟨Hpre, fun h => ?_⟩
    rcases Hall h with h' | h'
    · cases h'
    · exact reqWire_ne_nil _ _ _ h'

end proof

end net.rpc
end Perennial
