/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Client/Bufio.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md), restated over dsv-bufio (never unfolding its predicates).

* `writerRoom bw wr J Q sent pend room`: a healthy writer (`ownWriter … nil`) whose buffer has
  room for `room` more bytes: `pend.length + room ≤ wr.sz` (dsv-bufio's size index; the lab
  unfolded its writer). A fresh writer has room for `wr.sz = 4096` (`wp_NewWriter_room`); a writer
  with nothing buffered has room for one (`ownWriter_room`, `bufio.ownBufWriter_size`: `0 < sz`);
  `Write` / `WriteByte` within the room succeed and send nothing (`wp_Write_room`,
  `wp_WriteByte_room`: dsv-bufio's fit clauses).
* `ownReader_proto`: what a connection's buffered reader has returned is a prefix of an allowed
  stream, under a later (`net.connReader_proto`; the lab's had none).
* `ownWriter_sentLb`: a connection writer's sent bytes are a lower bound (`bufio.ownBufWriter_fact`
  with `sendTok_sentLb`). The lab's `sentLb_comparable` is not restated here: two lower bounds of
  one direction are comparable (the mono list), a law `GooseLang/Ext/Net/Proto.lean` does not
  state yet (rabia's review: `sentLb_prefix`/`sentLb_agree` to move there).
-/
module

public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Net.Proof.net.ConnIo

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [sem : go.Semantics]
variable [bufio.Assumptions] [BufioSpecs GF]

/-- See the file header. -/
def writerRoom (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (room : Nat) : IProp GF :=
  iprop(ownWriter bw wr J Q sent pend interface.nil ∗ ⌜pend.length + room ≤ wr.sz⌝)

theorem writerRoom_own (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (room : Nat) :
    writerRoom bw wr J Q sent pend room ⊢ ownWriter bw wr J Q sent pend interface.nil := by
  unfold writerRoom
  iintro ⟨H, -⟩
  iexact H

theorem ownWriter_room (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent : List w8) :
    ownWriter bw wr J Q sent [] interface.nil ⊢ writerRoom bw wr J Q sent [] 1 := by
  unfold writerRoom ownWriter
  iintro H
  ihave ⟨%Hsz, H⟩ := EtcdGrove.bufio.ownBufWriter_size _ _ _ _ _ _ _ _ _ $$ H
  iframe H
  ipureintro; simp; omega

theorem writerRoom_mono (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (r1 r2 : Nat) (h : r2 ≤ r1) :
    writerRoom bw wr J Q sent pend r1 ⊢ writerRoom bw wr J Q sent pend r2 := by
  unfold writerRoom
  iintro ⟨H, %Hr⟩
  iframe H
  ipureintro; omega

/-- `bufio.NewWriter(w)`: a writer with room for its whole buffer. -/
theorem wp_NewWriter_room (wr : WSt GF) (J Q : List w8 → IProp GF) (W : List w8)
    (hsz : wr.sz = 4096) (hty : wr.wi.ty ≠ go.GoType.PointerType bufio.Writer.ty) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗ J W ∗ □ Q W }}
      (App (Val (@! bufio.NewWriter)) (Val #(GoInterface.ok wr.wi)))
    {{ (bw : Loc), RET #bw; writerRoom bw wr J Q W [] 4096 }} := by
  iintro %Φ Hpre HΦ
  iapply wp_NewWriter wr J Q W hsz hty $$ Hpre
  iintro !> %bw Hown
  iapply HΦ
  unfold writerRoom
  iframe Hown
  ipureintro; simp [hsz]

/-- `WriteByte(c)` within the room: no error, nothing sent. -/
theorem wp_WriteByte_room (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (room : Nat) (c : w8) (hroom : 1 ≤ room) :
    {{ writerRoom bw wr J Q sent pend room ∗ □ Q (sent ++ pend ++ [c]) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #interface.nil; writerRoom bw wr J Q sent (pend ++ [c]) (room - 1) }} := by
  iintro %Φ ⟨Hr, #HQ⟩ HΦ
  unfold writerRoom
  icases Hr with ⟨Hown, %Hr⟩
  iapply wp_WriteByte bw wr J Q sent pend interface.nil c $$ [Hown]
  · iframe Hown
    iintro %_
    iexact HQ
  iintro !> %e Hpost
  icases Hpost with ⟨%sent', %pend', %Hk, Hown⟩
  obtain ⟨-, hnil, -, -, hfit⟩ := Hk
  obtain ⟨he, hs⟩ := hfit ⟨rfl, by omega⟩
  subst he hs
  have hp : pend' = pend ++ [c] := by
    have := hnil rfl
    simpa [List.append_assoc] using this
  subst hp
  iapply HΦ
  iframe Hown
  ipureintro; simp; omega

/-- `Write(p)` within the room: all of `p` buffered, no error, nothing sent. -/
theorem wp_Write_room (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (room : Nat) (p : GoSlice) (dq : DFrac) (ps : List w8)
    (hroom : ps.length ≤ room) :
    {{ writerRoom bw wr J Q sent pend room ∗ □ Q (sent ++ pend ++ ps) ∗ p ↦*{dq} ps }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ RET (PairV #(W64 ps.length) #interface.nil);
        p ↦*{dq} ps ∗ writerRoom bw wr J Q sent (pend ++ ps) (room - ps.length) }} := by
  iintro %Φ ⟨Hr, #HQ, Hp⟩ HΦ
  unfold writerRoom
  icases Hr with ⟨Hown, %Hr⟩
  iapply BufioSpecs.write (GF := GF) bw wr.wi J Q wr.Ew wr.sz sent pend interface.nil p dq ps
    $$ [Hown Hp]
  · iframe Hown Hp
    iintro %_
    iexact HQ
  iintro !> %nn %e Hpost
  icases Hpost with ⟨%k, %sent', %pend', %Hk, Hp, Hown⟩
  obtain ⟨hnn, -, hsp, -, hnil, -, hfit⟩ := Hk
  obtain ⟨he, hs⟩ := hfit ⟨rfl, by omega⟩
  subst he hs
  have hk : k = ps.length := hnil rfl
  subst hk hnn
  have hp : pend' = pend ++ ps := by
    rw [List.take_length] at hsp
    simpa [List.append_assoc] using hsp
  subst hp
  iapply HΦ
  iframe Hp
  iframe Hown
  ipureintro; simp; omega

end

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions]

/-- What a connection's buffered reader has returned is a prefix of an allowed stream
(`net.connReader_proto`). -/
theorem ownReader_proto (br : Loc) (rd : RSt GF) (cn : Nat) (s : Bool) (P : Proto GF)
    (R : List w8) :
    ownReader br rd (recvTokL (Gg := hG.goose_globalGS) cn s P) R ⊢
      ownReader br rd (recvTokL (Gg := hG.goose_globalGS) cn s P) R ∗ ▷ protoPrefix P cn R := by
  unfold ownReader
  exact net.connReader_proto br rd.ri _ cn s P rd.E R

/-- A connection writer's sent bytes are a lower bound of its direction. -/
theorem ownWriter_sentLb (bw : Loc) (wr : WSt GF) (cn : Nat) (s : Bool) (P : Proto GF)
    (Q : List w8 → IProp GF) (sent pend : List w8) (err : GoInterface) :
    ownWriter bw wr (sendTok (Gg := hG.goose_globalGS) cn s P) Q sent pend err ⊢
      ownWriter bw wr (sendTok (Gg := hG.goose_globalGS) cn s P) Q sent pend err ∗
        sentLb (Gg := hG.goose_globalGS) cn s sent := by
  unfold ownWriter
  exact EtcdGrove.bufio.ownBufWriter_fact bw wr.wi _ Q wr.Ew wr.sz sent pend err
    (fun w => sentLb (Gg := hG.goose_globalGS) cn s w) (fun w => sendTok_sentLb cn s P w)

end conn

end Perennial.gryff.wire
