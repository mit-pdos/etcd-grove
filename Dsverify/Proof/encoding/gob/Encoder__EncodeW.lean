/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/Encoder__EncodeW.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `Spec/gob/Encoder__EncodeW.lean` (change log C18: `Encode` over a sink; over
`getCodec`'s spec and the kit's codec obligations). The frame's header lemmas are
Proof/gob/Encoder__Encode.lean's.
-/
module

public import Dsverify.Proof.encoding.gob.getCodec
public import Dsverify.Spec.encoding.gob.Encoder__EncodeW
public import Dsverify.Proof.encoding.gob.Encoder__Encode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Bytes

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]

theorem Encoder.EncodeW.wp_proof (wp_getCodec : getCodec.spec (GF := GF)) :
    Encoder.EncodeW.spec (GF := GF) := by
  intro enc dq e S Q W v Θ
  wp_start as ⟨#Hset, #Hok, #Hsink, He, HS, Henc⟩
  wp_auto
  wp_apply wp_getCodec $$ [$Hset] as %c #Hfns
  unfold codecFns
  icases Hfns with ⟨#HE, -⟩
  unfold net.rpc.kitCodecOk
  icases Hok with ⟨#HencOk, -⟩
  unfold net.rpc.encOk
  wp_auto
  wp_apply HencOk $$ Henc as %body %bs Hbody ⟨#HQ, HΘ⟩
  ihave %Hbl := ownSlice_len _ _ _ $$ Hbody
  ihave %Hb47 := net.rpc.ownSlice_bytes_len _ _ _ $$ Hbody
  wp_apply (wp_slice_make3 (V := w8) (W64 8) (W64 8 + body.len) ⟨by decide, by word⟩)
    as %frame ⟨Hf, Hcap, -⟩
  rw [show List.replicate 8 (_root_.Perennial.zero_val w8) = hdrBytes body.len 0 by rw [hdrBytes_zero]; rfl]
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hf" ∷ frame ↦* hdrBytes body.len (uint.nat i) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i Hf]
  · iexists W64 0; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · ihave %Hfl := ownSlice_len _ _ _ $$ Hf
    have hl8 : (hdrBytes body.len (uint.nat i)).length = 8 := by simp [hdrBytes]
    rw [ite_eq_left (by rw [hl8] at Hfl; word)]
    wp_apply wp_store_slice_index frame (sint.Z i) (hdrBytes body.len (uint.nat i)) _ $$ [Hf] as Hf
    · iframe; ipureintro; rw [hl8]; word
    wp_for_post
    iframe
    iexists i + W64 1
    have hi8 : uint.nat i < 8 := by word
    rw [show (sint.Z i).toNat = uint.nat i by word, show W64 8 * i = W64 8 * W64 (uint.nat i) by word,
      hdrBytes_succ _ _ hi8, show uint.nat (i + W64 1) = uint.nat i + 1 by word]
    iframe
    ipureintro; omega
  · have hi : uint.nat i = 8 := by word
    rw [hi, hdrBytes_eight]
    wp_apply wp_slice_append $$ [Hf Hcap Hbody] as %frame' ⟨Hf, Hcap, -⟩
    · iframe
    have hg : u64Le body.len ++ bs = github_com.imdea_software.swiftpaxos.sp.gobFrame bs := by
      simp only [github_com.imdea_software.swiftpaxos.sp.gobFrame]
      congr 2; word
    rw [hg]
    wp_auto
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ He
    iStructNamed He
    wp_load
    wp_auto
    iunfold writeSink at Hsink
    wp_bind (App (Val #(methods e.ty go!"Write" e.v)) (Val #frame'))
    iapply Hsink $$ HS HQ Hf
    inext
    iintro %nn %err HS Hf
    wp_auto
    ihave He : (enc ↦{dq} (⟨interface.ok e⟩ : encoding.gob.Encoder) : IProp GF) $$ [w]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iexists bs
    iframe

end proof

end Perennial.encoding.gob
