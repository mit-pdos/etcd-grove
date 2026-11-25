/-
Package `proxy` (stage 3, P4): `msgBuffer.Write` (`proxynetwork.go`) and `ClientBatch.Marshal`
into a `*msgBuffer` (`internalSendMessage` encodes an answer before it writes its code byte).

Changed against the lab: `proto.Marshal` is the hypothesis `hyp.PbHyp.marshal` (over
`hyp.qpCodec`), in place of the lab's codec model (`codecSet`, `kitCodecOk`); the lab's
`WireProof.lean` lemmas on little-endian lengths are here (its proofs of `Wire.lean`'s specs, over
the lab's `bufio`, go: the kit's client will prove them over the landed `bufio`).
-/
module

public import Dsverify.Proof.raxos.Wire
public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.encoding.binary
public import Dsverify.Proof.raxos.Replica

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open models_lab.pbcodec (PbCodec)

theorem u64Le_le8 (v : w64) : u64Le v = le8 (uint.nat v) := by
  rw [encoding.binary.u64Le_8]
  simp only [le8, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq; simp [W8, uint.Z, uint.nat, Int.shiftRight_eq_div_pow]; try omega)

theorem leNum_combine_aux (d : List w8) (k : Nat) :
    ((d.zipIdx k).map (fun p => p.1.toNat * 2 ^ (8 * p.2))).sum =
      2 ^ (8 * k) * LittleEndian.combine d := by
  induction d generalizing k with
  | nil => simp [LittleEndian.combine]
  | cons b bs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih, LittleEndian.combine_unfold]
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]

theorem leNum_combine (d : List w8) : leNum d = LittleEndian.combine d := by
  simpa [leNum] using leNum_combine_aux d 0

theorem leToU64_sint_nonneg (d : List w8) (hlt : leNum d < 2 ^ 63) :
    0 ≤ sint.Z (leToU64 d) := by
  have h1 : uint.nat (leToU64 d) = leNum d := by
    simp only [leToU64, leToU64Def, leNum_combine] at *
    simp [uint.nat]
    omega
  word

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]

/-- A `msgBuffer` at `mb` holding the bytes `bs` (its slice owned, with its capacity). -/
def ownMB (mb : Loc) (bs : List w8) : IProp GF :=
  iprop(∃ s : GoSlice, mb ↦ raxos.replica.src.msgBuffer.mk s ∗ s ↦* bs ∗
    ownSliceCap w8 s (DFrac.own 1))

/-- `m.Write(p)`: appends `p`'s bytes, returns `len(p), nil`. -/
theorem wp_msgBuffer_Write (mb : Loc) (bs : List w8) (p : GoSlice) (dq : DFrac) (ps : List w8) :
    {{ ownMB (GF := GF) mb bs ∗ p ↦*{dq} ps }}
      (App (Val (mb @!! go.GoType.PointerType raxos.replica.src.msgBuffer.ty @!! go!"Write"))
        (Val #p))
    {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e);
        ⌜e = interface.nil ∧ nn = p.len⌝ ∗ ownMB mb (bs ++ ps) ∗ p ↦*{dq} ps }} := by
  wp_start as ⟨Hmb, Hp⟩
  iunfold ownMB at Hmb
  icases Hmb with ⟨%s, Hm, Hs, Hcap⟩
  wp_auto
  wp_apply (wp_slice_append (V := w8) s bs p ps dq) $$ [$Hs $Hcap $Hp] as %s' ⟨Hs', Hcap', Hp⟩
  iapply HΦ
  iframe Hp
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iunfold ownMB
  iexists s'
  iframe Hm Hs' Hcap'

/-- `t.Marshal(&mb)` into a `msgBuffer` holding `bs`: on nil, the batch fits and its 8-byte
length and encoding are appended; on an error, the buffer holds anything (it is dropped). -/
theorem marshal_buf (t : Loc) (dq : DFrac) (b : Batch) (mb : Loc) (bs : List w8) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗ repCB t dq b ∗ ownMB mb bs }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Marshal"))
      (Val #(interface.mkOk (go.GoType.PointerType raxos.replica.src.msgBuffer.ty) #mb)))
  {{ (e : GoInterface), RET #e; repCB t dq b ∗ ∃ bs' : List w8, ownMB mb bs' ∗
      ⌜e = interface.nil → batchFit b ∧ bs' = bs ++ le8 (encBatch b).length ++ encBatch b⌝ }} := by
  wp_start as ⟨Hrep, Hmb⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply (pb.marshal _
    (fun o => iprop(repCB t dq b ∗ ⌜match o with
      | some bs => batchOk b ∧ bs = encBatch b
      | none => ¬ batchOk b⌝))) $$ [Hrep] as %data %e Hpost
  · unfold marshalPre
    iright; iright; iright; iright; iright; iright
    iexists t, dq, b
    iframe Hrep
    isplitr
    · ipureintro; rfl
    iPkgInit
    iintro Hrep
    isplit
    · iintro %Hb; iframe Hrep; ipureintro; exact ⟨Hb, rfl⟩
    · iintro %Hb; iframe Hrep; ipureintro; exact Hb
  icases Hpost with (⟨%He, %bs0, Hbs, Hrep, %Hb⟩ | ⟨%He, -, Hrep, %Hb⟩)
  · subst He
    obtain ⟨Hbok, rfl⟩ := Hb
    wp_auto
    ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
    · iPkgInit
    ihave #Hle := encoding.binary.isInit_access $$ Hbin
    icases Hle with ⟨#Hle, -⟩
    wp_method_call
    wp_call
    wp_auto
    have h0 : sint.Z (W64 0) = 0 := rfl
    have h8 : W64 8 - W64 0 = W64 8 := rfl
    rw [h0, go.arrayIndexRef_0, h8]
    ihave Hsl := slice_array b_ptr 8 _ (by decide) $$ b
    ihave %Hdl := ownSlice_len $$ Hbs
    have Hblen : (encBatch b).length < 2 ^ 63 := by rw [Hdl.1]; word
    wp_apply (encoding.binary.littleEndian.wp_PutUint64 _ _
      (zero_val (GoArray w8 8)).arr [] data.len (by rfl)) $$ [Hsl] as Hsl
    · simp only [List.append_nil]; iexact Hsl
    have HL : data.len = W64 (encBatch b).length := by word
    rw [HL, u64Le_le8, show uint.nat (W64 (encBatch b).length) = (encBatch b).length by word]
    simp only [List.append_nil]
    wp_apply wp_msgBuffer_Write mb bs _ _ _ $$ [$Hmb $Hsl] as %nn %e1 ⟨%He1, Hmb, -⟩
    obtain ⟨rfl, -⟩ := He1
    wp_auto
    wp_apply wp_msgBuffer_Write mb _ _ _ _ $$ [$Hmb $Hbs] as %nn2 %e2 ⟨%He2, Hmb, -⟩
    obtain ⟨rfl, -⟩ := He2
    wp_auto
    wp_end
    iframe Hrep
    iexists _
    iframe Hmb
    ipureintro
    intro _
    exact ⟨⟨Hbok, Hblen⟩, by simp [List.append_assoc]⟩
  · cases e with
    | nil => exact absurd rfl He
    | ok ie => ?_
    wp_auto
    wp_end
    iframe Hrep
    iexists bs
    iframe Hmb
    ipureintro
    intro h; exact absurd h He

end proofs
end Perennial.raxos
