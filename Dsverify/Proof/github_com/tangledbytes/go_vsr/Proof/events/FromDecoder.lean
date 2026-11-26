/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/events/FromDecoder.lean (lab master
915f964; notes/dsv-vr.md): over any `GF`, on the net extension; the hook's lock is the hub's
`hookLockInvFull`. What changed: `Unmarshal` is the main tree's `encoding.json.Unmarshal.spec`
(proved, #24 J2/J3: by the dispatch `unmarshalVia`, here each payload type's own
`JSONModelUnmarshal`, `events.payload_via`) and the kit's JSON facts `vsrnet.codecOk`
(`Spec/json.lean`; the lab's theorem `codec_ok`), at the kit's contract `vsrnet.jsonCodec`; the frame decoder's own codec is the spec's (any instance `C`). It proves the
hub's `events.Event.FromDecoder.spec` directly (the lab's `wp_FromDecoder'` and its wrapper in
`Results.lean` in one).
-/
/-
`ev.FromDecoder(dec)`: the hook `FrameDecoder` (set for good: `frameDecoderSet`, its value
`decodeFrame`, a frame decoder `frameDecOk` by `Proof/vsrwire/Hook.lean`) decodes the next frame; the payload is decoded into its type's zero
value (`vsrnet.dec_payload`) and stored as `ev`'s event.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Spec.encoding.json.Codec.NewEncoder
public import Spec.encoding.json.Codec.Unmarshal
public import Spec.encoding.json.Codec.Encoder__Encode_conn
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrwire.Hook
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions] [log.Assumptions] [examples.vsrwire.Assumptions]
variable [net.Assumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- `Unmarshal` into a message's zero payload: the payload type's own `JSONModelUnmarshal` (#24
J3), from the kit's facts. -/
theorem events.payload_via (F : List w8 → Bool → w64 × w64) (m : Msg) (p : Loc) :
    encoding.json.kitCodecOk (GF := GF) F ⊢
      encoding.json.unmarshalVia C F
        (interface.mkOk (go.GoType.PointerType (events.payloadTy m)) #p) := by
  cases m <;> simp only [events.payloadTy] <;>
    exact encoding.json.kitCodecOk_unmarshalVia F _ p (by simp [encoding.json.kitTypes])
      (by go_type_set)

/-- `getFrameDecoder()` with the hook set: `decodeFrame`. -/
theorem events.wp_getFrameDecoder :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events ∗
      events.frameDecoderSet }}
    (App (Val (@! events.getFrameDecoder)) (Val #()))
  {{ (f : GoFunc), RET #f; ⌜f = events.kitFrameDecoder⌝ }} := by
  wp_start as #Hfs
  iunfold events.frameDecoderSet at Hfs
  icases Hfs with ⟨%γh, #Hst, #Hlb⟩
  iunfold events.hookState at Hst
  icases Hst with ⟨%mu, #Hmu, #Hlock⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock mu (events.hookLockInvFull γh) $$ [$Hlock] as ⟨Hown, Hinv⟩
  iunfold events.hookLockInvFull at Hinv
  icases Hinv with ⟨%f, Hf, (⟨%Hnil, Ha⟩ | ⟨%Hk, Ha⟩)⟩
  · ihave %Hv := mono_list_auth_lb_valid γh _ _ _ $$ Ha Hlb
    exact absurd Hv.2 (by simp)
  wp_auto
  wp_apply sync.Mutex.wp_Unlock mu (events.hookLockInvFull γh) $$ [$Hlock $Hown Hf Ha]
  · inext
    iunfold events.hookLockInvFull
    iexists f
    iframe
    iright
    iframe
    ipureintro; exact Hk
  iapply HΦ
  ipureintro; exact Hk

/-- `events.Event.FromDecoder.spec`, over `Unmarshal.spec` (the main tree's), `vsrnet.codecOk` and
`Decoder.Decode_frame.spec` (what the hook's `decodeFrame` calls). -/
theorem events.Event.FromDecoder.wp'
    (wp_Decode_frame : events.Decoder.Decode_frame.spec (GF := GF) (hG := hG))
    (wp_Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    events.Event.FromDecoder.spec (GF := GF) (hG := hG) := by
  intro F γ ev dec e0
  wp_start as ⟨#Hfs, #Hset, #HokF, Hrs, Hev⟩
  unfold examples.vsrnet.codecOk at codec_ok
  ihave #Hok := codec_ok
  wp_auto
  wp_apply events.wp_getFrameDecoder $$ [Hfs] as %f %Hfk
  · iexact Hfs
  subst Hfk
  ihave #Hf := examples.vsrwire.decodeFrame.wp' wp_Decode_frame $$ []
  · iPkgInit
  rw [decide_eq_false events.kitFrameDecoder_ne_nil]
  wp_auto
  unfold events.frameDecOk
  wp_apply Hf $$ %F %γ %dec [Hrs] as %t %data %err ⟨Hrs, Hpost⟩
  · iframe; isplit
    · iexact Hset
    · iexact HokF
  iclear Hf HokF Hfs
  cases err with
  | ok e =>
    simp only [decide_false, reduceCtorEq, Bool.false_eq_true, ↓reduceIte]
    icases Hpost with #HerrOk
    wp_auto
    iapply HΦ
    iframe HerrOk
    simp only [decide_false, reduceCtorEq, Bool.false_eq_true, ↓reduceIte]
    isplitl [Hrs]
    · iexact Hrs
    iexists _; iexact Hev
  | nil =>
    simp only [_root_.decide_true, ↓reduceIte]
    ihave #Hnil : bufio.errOrNil (GF := GF) GoInterface.nil $$ []
    · unfold bufio.errOrNil; ileft; ipureintro; rfl
    icases Hpost with ⟨%m, %ht, Hdata, %hm, %hmb, #Hfact⟩
    subst ht
    ihave %Hdl := ownSlice_len _ _ _ $$ Hdata
    cases m
    case request id cid op =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.request id cid op) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.request id cid op)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case reply id cid v res =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.reply id cid v res) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.reply id cid v res)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case prepare v k c e rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.prepare v k c e rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.prepare v k c e rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case prepareOK v k rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.prepareOK v k rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.prepareOK v k rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case commit v c rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.commit v c rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.commit v c rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case startViewChange v rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.startViewChange v rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.startViewChange v rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case doViewChange dv =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.doViewChange dv) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo, Hcap⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.doViewChange dv)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitl [Hcap]
      · unfold events.evCap
        iexists x
        isplitr
        · iExactEq Hev; rfl
        iexact Hcap
      iexact Hfact
    case startView v k c logs rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.startView v k c logs rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo, Hcap⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.startView v k c logs rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitl [Hcap]
      · unfold events.evCap
        iexists x
        isplitr
        · iExactEq Hev; rfl
        iexact Hcap
      iexact Hfact
    case getState v k rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.getState v k rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.getState v k rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case newState v logs c k rid =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF (Msg.newState v logs c k rid) v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo, Hcap⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists (Msg.newState v logs c k rid)
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact
    case heartbeat  =>
      simp only [events.typeOf]
      wp_auto
      ihave Hdep := examples.vsrnet.dec_payload _ v_ptr hm hmb $$ [v]
      · iPkgInit
        isplitr
        · iexact Hset
        unfold events.payloadZero
        iexact v
      ihave #Hvia := events.payload_via (C := examples.vsrnet.jsonCodec) examples.vsrnet.scanF Msg.heartbeat v_ptr $$ Hok
      simp only [events.payloadTy]
      wp_apply wp_Unmarshal examples.vsrnet.jsonCodec examples.vsrnet.scanF data _ _ _ _
        $$ [Hdata Hdep] as %err Hpost2
      · iframe
        iexact Hvia
      icases Hpost2 with ⟨Hdata, Hret⟩
      iunfold encoding.json.unmarshalRet at Hret
      icases Hret with (⟨%Hvalid, %ok, %Hok', ⟨%Hok1, Hpay⟩⟩ | ⟨⟨%Hnv, -⟩, -⟩)
      rotate_left
      · exact absurd (examples.vsrnet.encPayload_valid _ hm (by have := Hdl.1; word)) Hnv
      subst Hok1
      have herr : err = interface.nil := Hok'.2 rfl
      subst herr
      unfold events.payloadAt
      icases Hpay with ⟨%x, Hx, #Hpo⟩
      iapply wp_fupd
      wp_auto
      ipersist Hev
      imodintro
      iapply HΦ
      iframe Hnil
      simp only [_root_.decide_true, ↓reduceIte]
      isplitl [Hrs]
      · iexact Hrs
      iexists Msg.heartbeat
      isplitr
      · unfold events.isEvent
        iexists _
        isplitr
        · iExactEq Hev; rfl
        iexact Hpo
      isplitr
      · unfold events.evCap
        itrivial
      iexact Hfact

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
