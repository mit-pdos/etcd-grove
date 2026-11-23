/-
Package `proxy`: the writer side's lemmas for `internalSendMessage` (`NetSend.lean`): the client
port's protocol is prefix-closed, a sticky `WriteByte`, a stronger `Marshal` (the writer's error
is the returned one), and the answer frames' protocol facts.
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs
public import Dsverify.Proof.raxos.Proxy.MsgBuf

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- The client port's protocol is prefix-closed. -/
theorem clientInProto_prefixClosed (γ : QNames) (c : Nat) (cid : w64) :
    ⊢ bufio.prefixClosed (GF := GF) (clientInProto γ c cid) := by
  unfold bufio.prefixClosed
  iintro !> %x %y H
  unfold clientInProto
  icases H with ⟨%k, %L, %Hp, HL⟩
  iexists k, L
  iframe HL
  ipureintro
  exact ⟨Hp.1, List.IsPrefix.trans (List.prefix_append x y) Hp.2.1, Hp.2.2⟩

end lemmas

section sticky
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [bufio.Assumptions]

set_option goose.wp.extras true

/-- `WriteByte(c)` on a writer with a sticky error: returns it, nothing changes (no protocol
obligation). -/
theorem wp_WriteByte_sticky (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (ei : GoInterfaceOk) (c : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ bufio.writerOk wr J Q ∗
        bufio.ownWriter bw wr J Q sent pend (interface.ok ei) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #(interface.ok ei); bufio.ownWriter bw wr J Q sent pend (interface.ok ei) }} := by
  wp_start as ⟨#Hwr, Hown⟩
  ihave #Hwr' := Hwr
  iunfold bufio.writerOk at Hwr'
  icases Hwr' with ⟨%e, %He, -, -⟩
  obtain ⟨rfl, hty⟩ := He
  iunfold bufio.ownWriter, bufio.writerRep at Hown
  icases Hown with ⟨HJ, #HQ, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  wp_auto
  iapply HΦ
  iunfold bufio.ownWriter, bufio.writerRep
  iframe HJ HQ
  iexists buf, n, rest
  iframe Hb Hbuf Herr
  ipureintro; exact Hn

end sticky

section marshal
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions]

open models_lab.pbcodec (PbCodec)

/-- `ClientBatch.Marshal.spec`, and the writer's final error is the returned one (for a
well-formed batch). -/
theorem marshal_strong (t : Loc) (dq : DFrac) (b : Batch) (bw : Loc) (wr : GoInterface)
    (J Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ repCB t dq b ∗
      bufio.writerOk wr J Q ∗ bufio.ownWriter bw wr J Q sent pend err ∗
      □ (⌜batchOk b ∧ (encBatch b).length < 2 ^ 63⌝ →
          Q (sent ++ pend ++ le8 (encBatch b).length ++ encBatch b)) }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Marshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw)))
  {{ (e : GoInterface), RET #e; repCB t dq b ∗
      ∃ (k : Nat) (sent' pend' : List w8) (e' : GoInterface),
        ⌜sent' ++ pend' = sent ++ pend ++ (le8 (encBatch b).length ++ encBatch b).take k ∧
          (e = interface.nil → batchOk b ∧ (encBatch b).length < 2 ^ 63 ∧
            k = (le8 (encBatch b).length ++ encBatch b).length) ∧
          (¬ (batchOk b ∧ (encBatch b).length < 2 ^ 63) → k = 0) ∧
          (batchOk b → (encBatch b).length < 2 ^ 63) ∧ (batchOk b → e' = e)⌝ ∗
        bufio.ownWriter bw wr J Q sent' pend' e' }} := by
  wp_start as ⟨#Hcs, #Hok, Hrep, #Hwr, Hown, #HQ⟩
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  wp_auto
  wp_apply (google_golang_org.protobuf.proto.Marshal.wp_proof _
    (fun o => iprop(repCB t dq b ∗ ⌜match o with
      | some bs => batchOk b ∧ bs = encBatch b
      | none => ¬ batchOk b⌝))) $$ [Hrep] as %data %e Hpost
  · iframe Hcs Hok
    iright
    isplitr
    · ipureintro; intro h; cases h
    simp only [google_golang_org.protobuf.proto.PbCodec.marshal, marshalPre]
    iright; iright; iright; iright; iright; iright
    iexists t, dq, b
    iframe Hrep
    isplitr
    · ipureintro; rfl
    iintro Hrep
    isplit
    · iintro %Hb; iframe Hrep; ipureintro; exact ⟨Hb, rfl⟩
    · iintro %Hb; iframe Hrep; ipureintro; exact Hb
  iunfold google_golang_org.protobuf.proto.marshalPost at Hpost
  icases Hpost with (⟨%He, %bs, Hbs, Hrep, %Hb⟩ | ⟨%He, -, Hrep, %Hb⟩)
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
    ihave #Hwr' := Hwr
    iunfold bufio.writerOk at Hwr'
    icases Hwr' with ⟨%e0, %He0, #Hpc, -⟩
    have Hbb : batchOk b ∧ (encBatch b).length < 2 ^ 63 := ⟨Hbok, Hblen⟩
    ihave #HQf := HQ $$ %Hbb
    ihave #HQ1 := bufio.Q_of_prefix Q (sent ++ pend ++ le8 (encBatch b).length)
      (sent ++ pend ++ le8 (encBatch b).length ++ encBatch b) ⟨encBatch b, by simp⟩ $$ Hpc HQf
    simp only [List.append_nil]
    wp_apply bufio.wp_Write bw wr J Q sent pend err _ _ _ $$ [Hown Hsl]
      as %nn %e1 ⟨%k, %sent', %pend', %Hk, Hsl, Hown⟩
    · iframe Hwr Hown Hsl
      iexact HQ1
    cases e1 with
    | ok i1 =>
      -- the length's write failed
      wp_auto
      wp_end
      iframe Hrep
      iexists k, sent', pend', GoInterface.ok i1
      iframe Hown
      ipureintro
      refine ⟨?_, fun h => by simp at h, fun h => absurd Hbb h, fun _ => Hblen, fun _ => rfl⟩
      rw [Hk.2.2.1, List.take_append_of_le_length (by have := Hk.2.1; simp at this ⊢; omega)]
    | nil =>
      wp_auto
      -- the length is written: the encoding
      have Hk8 : k = (le8 (encBatch b).length).length := Hk.2.2.2.2.1 rfl
      ihave #HQ2 : □ Q (sent' ++ pend' ++ encBatch b) $$ []
      · rw [Hk.2.2.1, Hk8, List.take_length]; simp only [List.append_assoc]; iexact HQf
      wp_apply bufio.wp_Write bw wr J Q sent' pend' GoInterface.nil _ _ _ $$ [Hown Hbs]
        as %nn2 %e2 ⟨%k2, %sent'', %pend'', %Hk2, Hbs, Hown⟩
      · iframe Hwr Hown Hbs
        iexact HQ2
      cases e2 with
      | ok i2 =>
        wp_auto
        wp_end
        iframe Hrep
        iexists (le8 (encBatch b).length).length + k2, sent'', pend'', GoInterface.ok i2
        iframe Hown
        ipureintro
        refine ⟨?_, fun h => by simp at h, fun h => absurd Hbb h, fun _ => Hblen, fun _ => rfl⟩
        rw [Hk2.2.2.1, Hk.2.2.1, Hk8, List.take_length]
        simp [List.append_assoc, List.take_append]
        exact (List.take_of_length_le (by omega)).symm
      | nil =>
        wp_auto
        wp_end
        iframe Hrep
        iexists (le8 (encBatch b).length).length + k2, sent'', pend'', GoInterface.nil
        iframe Hown
        ipureintro
        have Hk2f : k2 = (encBatch b).length := Hk2.2.2.2.2.1 rfl
        refine ⟨?_, fun _ => ⟨Hbok, Hblen, by simp [Hk2f]⟩, fun h => absurd Hbb h, fun _ => Hblen, fun _ => rfl⟩
        rw [Hk2.2.2.1, Hk.2.2.1, Hk8, List.take_length]
        simp [List.append_assoc, List.take_append]
        exact (List.take_of_length_le (by omega)).symm
  · cases e with
    | nil => exact absurd rfl He
    | ok ie => ?_
    wp_auto
    wp_end
    iframe Hrep
    iexists 0, sent, pend, err
    iframe Hown
    ipureintro
    refine ⟨by simp, fun h => absurd h He, fun _ => rfl, fun h => absurd h Hb,
      fun h => absurd h Hb⟩


end marshal

end Perennial.raxos
