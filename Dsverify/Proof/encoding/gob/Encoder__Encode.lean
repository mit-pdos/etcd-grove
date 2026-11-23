/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/Encoder__Encode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `Spec/gob/Encoder__Encode.lean` (over `getCodec`'s spec and the kit's codec
obligations; `bufio`'s `Write` from the harness).
-/
module

public import Dsverify.Proof.encoding.gob.getCodec
public import Dsverify.Spec.encoding.gob.Encoder__Encode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Bytes

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The frame header after `i` of the 8 stores of `n`'s bytes. -/
def hdrBytes (n : w64) (i : Nat) : List w8 :=
  (List.range 8).map (fun j => if j < i then W8 (uint.Z (n >>> (W64 8 * W64 j))) else W8 0)

theorem hdrBytes_zero (n : w64) : hdrBytes n 0 = List.replicate 8 (W8 0) := by
  simp [hdrBytes]; rfl

theorem hdrBytes_succ (n : w64) (i : Nat) (hi : i < 8) :
    (hdrBytes n i).set i (W8 (uint.Z (n >>> (W64 8 * W64 i)))) = hdrBytes n (i + 1) := by
  apply List.ext_getElem
  · simp [hdrBytes]
  · intro j h1 h2
    simp only [hdrBytes, List.getElem_set, List.getElem_map, List.getElem_range]
    by_cases hj : i = j
    · subst hj; simp
    · simp only [hj, ↓reduceIte]
      have : (j < i) ↔ (j < i + 1) := by omega
      simp only [this]

theorem hdrBytes_eight (n : w64) : hdrBytes n 8 = u64Le n := by
  rw [← github_com.imdea_software.swiftpaxos.examples.swiftnet.u64Le_bytes]
  rfl

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]

theorem Encoder.Encode.wp_proof (wp_getCodec : getCodec.spec (GF := GF)) :
    Encoder.Encode.spec (GF := GF) := by
  intro enc dq bw wr J Q sent pend err v Θ
  wp_start as ⟨#Hset, #Hok, #Hbufio, #Hwr, He, Hw, Henc⟩
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
    wp_apply (bufio.wp_Write bw wr J Q sent pend err frame' (DFrac.own 1)
      (github_com.imdea_software.swiftpaxos.sp.gobFrame bs)) $$ [$Hbufio $Hwr Hw HQ Hf]
      as %nn %e ⟨%k, %sent', %pend', %Hk, Hf, Hw⟩
    · iframe; iexact HQ
    ihave He : (enc ↦{dq} (⟨interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw⟩ :
        encoding.gob.Encoder) : IProp GF) $$ [w]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    obtain ⟨rfl, hk1, hk2, hk3, hk4, hk5⟩ := Hk
    iapply HΦ
    iexists bs, k, sent', pend'
    iframe
    ipureintro; exact ⟨hk1, hk2, hk3, hk4, hk5⟩

end proof

end Perennial.encoding.gob
