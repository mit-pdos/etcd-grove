/-
The proof of `serverCodec.WriteResponse` (`Net/Spec/net/rpc/serverCodec__WriteResponse.lean`): the
sticky error first; then the header (`putU64`, two `putString`s) and the two frames (`putFrame`; for
a success response the codec's `Encode`, `encOk`, for an error response an empty frame), written by
one `Write` through the library's writer predicate and accessor (`writeP`, `write_acc`).
-/
module

public import Net.Spec.net.rpc.serverCodec__WriteResponse
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
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem respWire_ok (seq : w64) (sm e : GoString) (eb : List w8) (he : e = []) :
    ([] ++ frameOf ([] ++ u64Le seq ++ strEnc sm ++ strEnc e)) ++ frameOf eb =
      respWire seq sm e eb := by
  simp [respWire, respHdr, he]

theorem respWire_err (seq : w64) (sm e : GoString) (eb : List w8) (he : e ≠ []) :
    ([] ++ frameOf ([] ++ u64Le seq ++ strEnc sm ++ strEnc e)) ++ frameOf [] =
      respWire seq sm e eb := by
  simp [respWire, respHdr, he]

theorem sint_nat_lt'' (x : w64) : sint.nat x < 2 ^ 63 := by
  unfold sint.nat; have := BitVec.toInt_lt (x := x); simp at this; omega

theorem respWire_ne_nil (seq : w64) (sm e : GoString) (eb : List w8) :
    respWire seq sm e eb ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [respWire, frameOf_length] at this

theorem serverCodec.WriteResponse.wp_proof (wp_getCodec : getCodec.spec (GF := GF) (hG := hG))
    (wp_putU64 : putU64.spec (GF := GF) (hG := hG))
    (wp_putString : putString.spec (GF := GF) (hG := hG))
    (wp_putFrame : putFrame.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG)) :
    serverCodec.WriteResponse.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra r rv body w0 ed C Pr W0 Ψ0 Ψ
  wp_start as ⟨#Hrwc, #Hc, #Hed, Hwerr, Hr, #Hset, Htok, Henc, Hupd⟩
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
  ihave Hupd := Hupd $$ %rfl
  ihave Hn0 := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hn0c := ownSliceCap_nil (V := w8)
  wp_apply wp_putU64 slice.nil [] rv.Seq' $$ [$Hn0 $Hn0c] as %h1 ⟨Hh1, Hh1c⟩
  wp_apply wp_putString h1 _ rv.ServiceMethod' $$ [$Hh1 $Hh1c] as %h2 ⟨Hh2, Hh2c⟩
  wp_apply wp_putString h2 _ rv.Error' $$ [$Hh2 $Hh2c] as %h3 ⟨Hh3, Hh3c⟩
  ihave Hn1 := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hn1c := ownSliceCap_nil (V := w8)
  wp_apply wp_putFrame slice.nil [] h3 (DFrac.own 1) _ $$ [$Hn1 $Hn1c $Hh3] as %b1 ⟨Hb1, Hb1c, Hh3⟩
  ihave %Hh3l := ownSlice_len $$ Hh3
  have hhdr : rv.ServiceMethod'.length + rv.Error'.length + 24 < 2 ^ 63 := by
    have := sint_nat_lt'' h3.len
    simp [strEnc_length, u64Le_length] at Hh3l
    omega
  wp_if_destruct
  · have he := Hif
    unfold respEnc
    rw [if_pos he]
    wp_apply wp_getCodec C $$ Hset as %cd #Hcd
    unfold codecIs
    icases Hcd with ⟨%v, #Hv, #Henc', #Hdec', -⟩
    iStructNamed Hv
    wp_auto
    unfold encOk
    wp_bind (App (Val #v.Encode') _)
    iapply Henc' $$ Henc
    inext
    iintro %sl %eb Hsl Hslc HΨ0
    ihave %Hsll := ownSlice_len $$ Hsl
    have hfit : rv.ServiceMethod'.length + rv.Error'.length + 24 < 2 ^ 63 ∧ eb.length < 2 ^ 63 := by
      have := sint_nat_lt'' sl.len
      omega
    wp_apply wp_putFrame b1 _ sl (DFrac.own 1) eb $$ [$Hb1 $Hb1c $Hsl] as %b2 ⟨Hb2, Hb2c, Hsl⟩
    rw [respWire_ok _ _ _ eb he]
    unfold respUpd
    imod Hupd $$ %eb %hfit HΨ0 with ⟨#Hproto, HΨ⟩
    ihave Hw0 := writeP_init (Gg := hG.goose_globalGS) cn s Pr W0 $$ Htok
    ihave #Hacc := write_acc (Gg := hG.goose_globalGS) cn s Pr W0
      (respWire rv.Seq' rv.ServiceMethod' rv.Error' eb) $$ Hproto
    wp_apply wp_Write t cn s a la ra b2 (respWire rv.Seq' rv.ServiceMethod' rv.Error' eb) (DFrac.own 1) ed
        (writeP (Gg := hG.goose_globalGS) cn s Pr W0) $$ [$Hc $Hb2 $Hed $Hw0 $Hacc]
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
      · exact respWire_ne_nil _ _ _ _ h'
  · have he := Hif
    unfold respEnc
    rw [if_neg he]
    ihave Hn2 := ownSlice_nil (V := w8) (DFrac.own 1)
    ihave Hn2c := ownSliceCap_nil (V := w8)
    wp_apply wp_putFrame b1 _ slice.nil (DFrac.own 1) [] $$ [$Hb1 $Hb1c $Hn2] as %b2 ⟨Hb2, Hb2c, -⟩
    rw [respWire_err _ _ _ [] he]
    have hfit : rv.ServiceMethod'.length + rv.Error'.length + 24 < 2 ^ 63 ∧ ([] : List w8).length < 2 ^ 63 := by
      simp; omega
    ihave HΨ0 := Henc
    unfold respUpd
    imod Hupd $$ %([] : List w8) %hfit HΨ0 with ⟨#Hproto, HΨ⟩
    ihave Hw0 := writeP_init (Gg := hG.goose_globalGS) cn s Pr W0 $$ Htok
    ihave #Hacc := write_acc (Gg := hG.goose_globalGS) cn s Pr W0
      (respWire rv.Seq' rv.ServiceMethod' rv.Error' ([] : List w8)) $$ Hproto
    wp_apply wp_Write t cn s a la ra b2 (respWire rv.Seq' rv.ServiceMethod' rv.Error' ([] : List w8)) (DFrac.own 1) ed
        (writeP (Gg := hG.goose_globalGS) cn s Pr W0) $$ [$Hc $Hb2 $Hed $Hw0 $Hacc]
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
      iexists ([] : List w8)
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
      iexists ([] : List w8)
      iframe HΨ
      iright
      iexists w, k
      iframe Hwerr Hw Herr
      ipureintro
      refine ⟨Hpre, fun h => ?_⟩
      rcases Hall h with h' | h'
      · cases h'
      · exact respWire_ne_nil _ _ _ _ h'
end proof

end net.rpc
end Perennial
