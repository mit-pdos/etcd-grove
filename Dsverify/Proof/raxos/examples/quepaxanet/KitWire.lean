/-
`ClientBatch.Marshal` into a `*bufio.Writer` (`proto/client/clientwrapper.go`), the kit's client's
send of a request batch (`replica.send`), over `proto.Marshal` (the hypothesis `hyp.PbHyp.marshal`)
and the landed `bufio`'s `Writer.Write` (two writes: the 8-byte length, then the encoding).

This restates the lab's `ClientBatch.Marshal.spec` (it stood in `Wire.lean`, unused; deleted): the writer's
protocol `Q` is asked of the stream after the length prefix too (`Write` asks `□ Q` of every
write's stream, and `ownBufWriter` does not expose the prefix closure of `Q`), and the post only
says what the client needs (on `nil`: the batch fits and its length and encoding were appended).
The lab's `ClientBatch.Unmarshal.spec` is `Proxy/NetUnmarshal.lean`'s `unmarshalB.spec`
(the stream fact `Φ` bounds the length once read), proved there (`unmarshal_bounded`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetReader
public import Dsverify.Proof.raxos.Proxy.MsgBuf

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open EtcdGrove (bufio.ownBufWriter)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `t.Marshal(w)` on a `*bufio.Writer` `bw` (as an `io.Writer`): on `nil`, the batch is well
formed, its encoding fits (`batchFit`), and its 8-byte length and encoding were appended to the
writer's stream, which must allow both writes' streams. -/
abbrev cbMarshal.spec : Prop :=
  ∀ (t : Loc) (dq : DFrac) (b : Batch) (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗ repCB t dq b ∗
      bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      □ (⌜batchFit b⌝ → Q (sent ++ pend ++ le8 (encBatch b).length) ∗
        Q (sent ++ pend ++ le8 (encBatch b).length ++ encBatch b)) }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Marshal"))
      (Val #(interface.mkOk (go.GoType.PointerType Perennial.bufio.Writer.ty) #bw)))
  {{ (e : GoInterface), RET #e; repCB t dq b ∗
      ∃ (sent' pend' : List w8) (e' : GoInterface),
        ⌜e = interface.nil → batchFit b ∧
          sent' ++ pend' = sent ++ pend ++ le8 (encBatch b).length ++ encBatch b⌝ ∗
        bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e' }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]
variable [_root_.Perennial.bufio.Assumptions]
variable [QpBufioDeps GF]

theorem cbMarshal_proof : cbMarshal.spec (GF := GF) (hG := hG) := by
  intro t dq b bw wi J Q Ew sz sent pend err
  wp_start as ⟨Hrep, Hown, #HQ⟩
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
    have Hfit : batchFit b := ⟨Hbok, Hblen⟩
    wp_apply (encoding.binary.littleEndian.wp_PutUint64 _ _
      (zero_val (GoArray w8 8)).arr [] data.len (by rfl)) $$ [Hsl] as Hsl
    · simp only [List.append_nil]; iexact Hsl
    have HL : data.len = W64 (encBatch b).length := by word
    rw [HL, u64Le_le8, show uint.nat (W64 (encBatch b).length) = (encBatch b).length by word]
    simp only [List.append_nil]
    ihave ⟨#HQ1, #HQ2⟩ := HQ $$ %Hfit
    wp_apply QpBufioDeps.write bw wi J Q
        Ew sz sent pend err _ (DFrac.own 1) _ $$ [Hown Hsl]
      as %nn %e1 ⟨%k1, %sent1, %pend1, %Hk1, -, Hown⟩
    · iframe Hown Hsl
      iintro %_
      iexact HQ1
    rcases e1 with ei | _
    · wp_auto
      wp_end
      iframe Hrep
      iexists _, _, _
      iframe Hown
      ipureintro; intro h; cases h
    have H1 : sent1 ++ pend1 = sent ++ pend ++ le8 (encBatch b).length := by
      rw [Hk1.2.2.1, Hk1.2.2.2.2.1 rfl, List.take_length]
    wp_auto
    wp_apply QpBufioDeps.write bw wi J Q
        Ew sz sent1 pend1 GoInterface.nil data (DFrac.own 1) _ $$ [Hown Hbs]
      as %nn2 %e2 ⟨%k2, %sent2, %pend2, %Hk2, -, Hown⟩
    · iframe Hown Hbs
      iintro %_
      rw [H1]
      iexact HQ2
    rcases e2 with ei | _
    · wp_auto
      wp_end
      iframe Hrep
      iexists _, _, _
      iframe Hown
      ipureintro; intro h; cases h
    wp_auto
    wp_end
    iframe Hrep
    iexists _, _, _
    iframe Hown
    ipureintro
    intro _
    refine ⟨Hfit, ?_⟩
    rw [Hk2.2.2.1, Hk2.2.2.2.2.1 rfl, List.take_length, H1]
  · cases e with
    | nil => exact absurd rfl He
    | ok ie => ?_
    wp_auto
    wp_end
    iframe Hrep
    iexists _, _, _
    iframe Hown
    ipureintro
    intro h; cases h

end proof
end Perennial.raxos
