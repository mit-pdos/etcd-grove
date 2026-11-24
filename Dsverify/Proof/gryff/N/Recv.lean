/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Recv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: receiving a message of a known kind (`New`, then `Unmarshal`: `replicaListener`'s
dispatch through the rpc table)
-/
module

public import Dsverify.Proof.gryff.N.SendMsg
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg Out)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF]


/-- A fresh struct of the kind of `m` at `l` (`New`'s result, what `Unmarshal` fills). -/
def freshMsg (m : Msg) (l : Loc) : IProp GF :=
  match m with
  | .read1 _ => iprop(∃ v : src.gryffproto.Read1Proxied, l ↦ v)
  | .read2 _ => iprop(∃ v : src.gryffproto.Read2Proxied, l ↦ v)
  | .read1Reply _ => iprop(∃ v : src.gryffproto.Read1Reply, l ↦ v)
  | .read2Reply _ => iprop(∃ v : src.gryffproto.Read2Reply, l ↦ v)
  | .write1 _ => iprop(∃ v : src.gryffproto.Write1Proxied, l ↦ v)
  | .write2 _ => iprop(∃ v : src.gryffproto.Write2Proxied, l ↦ v)
  | .write1Reply _ => iprop(∃ v : src.gryffproto.Write1Reply, l ↦ v)
  | .write2Reply _ => iprop(∃ v : src.gryffproto.Write2Reply, l ↦ v)
  | .preAccept _ => iprop(∃ v : src.gryffproto.PreAccept, l ↦ v)
  | .preAcceptReply _ => iprop(∃ v : src.gryffproto.PreAcceptReply, l ↦ v)
  | .preAcceptOK _ => iprop(∃ v : src.epaxosproto.PreAcceptOK, l ↦ v)
  | .accept _ => iprop(∃ v : src.gryffproto.EAccept, l ↦ v)
  | .acceptReply _ => iprop(∃ v : src.epaxosproto.AcceptReply, l ↦ v)
  | .commit _ => iprop(∃ v : src.gryffproto.ECommit, l ↦ v)
  | .prepare _ => iprop(∃ v : src.epaxosproto.Prepare, l ↦ v)
  | .prepareReply _ => iprop(∃ v : src.gryffproto.PrepareReply, l ↦ v)
  | .executed _ => iprop(∃ v : src.gryffproto.Executed, l ↦ v)
  | .executeOverwrite _ => iprop(False)

set_option goose.wp.extras true

/-- `obj.New()` for a registered object of the kind of `m`. -/
theorem wp_New_msg (m : Msg) (obj : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗ ⌜netN.msgCode m ≠ none⌝ }}
      (App (Val (obj @!! msgTy m @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (msgTy m) #l); freshMsg m l }} := by
  cases m with
  | read1 mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | read2 mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | read1Reply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | read2Reply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | write1 mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | write2 mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | write1Reply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | write2Reply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | preAccept mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | preAcceptReply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | preAcceptOK mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | accept mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | acceptReply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | commit mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | prepare mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | prepareReply mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | executed mm =>
    simp only [msgTy, freshMsg]
    wp_start
    wp_auto
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    iexists _; iframe
  | executeOverwrite mm =>
    iintro %Φ ⟨-, -, %h⟩ -
    exact absurd rfl h

/-- `obj.Unmarshal(reader)` for a fresh object of the kind of `m1` (code `c`): the bytes after the
reader's position are (comparable with) a message of that kind; on success, a message `m` of the
kind, `msgAt`, its bytes `c :: e` read. -/
theorem wp_Unmarshal_msg (m1 : Msg) (c : w8) (hc : netN.msgCode m1 = some c) (l br : Loc)
    (rd : wire.RSt GF) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        wire.readerOk rd I ∗
        wire.readNext br rd I R (fun D =>
          ∃ m' b, netN.msgCode m' = some c ∧ netN.msgWireB m' (c :: b) ∧ (D <+: b ∨ b <+: D)) ∗
        wire.ownReader br rd I R ∗ freshMsg m1 l }}
      (App (Val (l @!! msgTy m1 @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ (m : Msg) (e : List w8),
          ⌜netN.msgCode m = some c ∧ msgWire m (c :: e)⌝ ∗ msgAt l m ∗
          wire.ownReader br rd I (R ++ e)) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ R' : List w8, wire.ownReader br rd I (R ++ R')) }} := by
  cases m1 with
  | read1 mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Read1Proxied.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.read1 (read1Of g), wire.gryffproto.Read1Proxied.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | read2 mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Read2Proxied.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.read2 (read2Of g), wire.gryffproto.Read2Proxied.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | read1Reply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Read1Reply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.read1Reply (read1ReplyOf g), wire.gryffproto.Read1Reply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | read2Reply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Read2Reply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.read2Reply (read2ReplyOf g), wire.gryffproto.Read2Reply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | write1 mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Write1Proxied.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.write1 (write1Of g), wire.gryffproto.Write1Proxied.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | write2 mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Write2Proxied.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.write2 (write2Of g), wire.gryffproto.Write2Proxied.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | write1Reply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Write1Reply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.write1Reply (write1ReplyOf g), wire.gryffproto.Write1Reply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | write2Reply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Write2Reply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.write2Reply (write2ReplyOf g), wire.gryffproto.Write2Reply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | preAccept mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    iapply wp_fupd
    wp_apply (wire.gryffproto.PreAccept.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply (wire.readNext_mono br rd I R _ wire.gryffproto.PreAccept.nextOk ?_) $$ Hnx
      intro D Hn
      obtain ⟨m', b, hc', hb, hD⟩ := Hn
      have hk := netN.msgCode_kind hc' (rfl : netN.msgCode (Msg.preAccept mm1) = _)
      cases m' <;> simp only [netN.msgKindIdx] at hk <;> try exact absurd hk (by decide)
      obtain ⟨g', hb', hw', -⟩ := hb
      simp only [List.cons.injEq] at hb'
      exact ⟨g', hw', hb'.2 ▸ hD⟩
    · ihave ⟨Ho, %Hl⟩ := netN.preAccept_len _ _ _ $$ Ho
      iunfold wire.gryffproto.PreAccept.own at Ho
      icases Ho with ⟨%sl, Ho, Hs⟩
      imod (ownSlice_persist _ _ _) $$ Hs with #Hs
      imodintro
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.preAccept (preAcceptOf g), wire.gryffproto.PreAccept.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, Hl.1, Hl.2, rfl⟩
      unfold msgAt
      iexists g, sl; iframe Ho Hs; ipureintro; rfl
    · imodintro
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | preAcceptReply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.PreAcceptReply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · ihave ⟨Ho, %Hl⟩ := netN.preAcceptReply_len _ _ _ $$ Ho
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.preAcceptReply (preAcceptReplyOf g), wire.gryffproto.PreAcceptReply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, Hl.1, Hl.2, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | preAcceptOK mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.epaxosproto.PreAcceptOK.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.preAcceptOK (preAcceptOKOf g), wire.epaxosproto.PreAcceptOK.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | accept mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    iapply wp_fupd
    wp_apply (wire.gryffproto.EAccept.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply (wire.readNext_mono br rd I R _ wire.gryffproto.EAccept.nextOk ?_) $$ Hnx
      intro D Hn
      obtain ⟨m', b, hc', hb, hD⟩ := Hn
      have hk := netN.msgCode_kind hc' (rfl : netN.msgCode (Msg.accept mm1) = _)
      cases m' <;> simp only [netN.msgKindIdx] at hk <;> try exact absurd hk (by decide)
      obtain ⟨g', hb', hw', -⟩ := hb
      simp only [List.cons.injEq] at hb'
      exact ⟨g', hw', hb'.2 ▸ hD⟩
    · ihave ⟨Ho, %Hl⟩ := netN.accept_len _ _ _ $$ Ho
      iunfold wire.gryffproto.EAccept.own at Ho
      icases Ho with ⟨%sl, Ho, Hs⟩
      imod (ownSlice_persist _ _ _) $$ Hs with #Hs
      imodintro
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.accept (acceptOf g), wire.gryffproto.EAccept.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, Hl.1, Hl.2, rfl⟩
      unfold msgAt
      iexists g, sl; iframe Ho Hs; ipureintro; rfl
    · imodintro
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | acceptReply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.epaxosproto.AcceptReply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.acceptReply (acceptReplyOf g), wire.epaxosproto.AcceptReply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | commit mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    iapply wp_fupd
    wp_apply (wire.gryffproto.ECommit.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply (wire.readNext_mono br rd I R _ wire.gryffproto.ECommit.nextOk ?_) $$ Hnx
      intro D Hn
      obtain ⟨m', b, hc', hb, hD⟩ := Hn
      have hk := netN.msgCode_kind hc' (rfl : netN.msgCode (Msg.commit mm1) = _)
      cases m' <;> simp only [netN.msgKindIdx] at hk <;> try exact absurd hk (by decide)
      obtain ⟨g', hb', hw', -⟩ := hb
      simp only [List.cons.injEq] at hb'
      exact ⟨g', hw', hb'.2 ▸ hD⟩
    · ihave ⟨Ho, %Hl⟩ := netN.commit_len _ _ _ $$ Ho
      iunfold wire.gryffproto.ECommit.own at Ho
      icases Ho with ⟨%sl, Ho, Hs⟩
      imod (ownSlice_persist _ _ _) $$ Hs with #Hs
      imodintro
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.commit (commitOf g), wire.gryffproto.ECommit.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, Hl.1, Hl.2, rfl⟩
      unfold msgAt
      iexists g, sl; iframe Ho Hs; ipureintro; rfl
    · imodintro
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | prepare mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.epaxosproto.Prepare.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.prepare (prepareOf g), wire.epaxosproto.Prepare.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | prepareReply mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    iapply wp_fupd
    wp_apply (wire.gryffproto.PrepareReply.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply (wire.readNext_mono br rd I R _ wire.gryffproto.PrepareReply.nextOk ?_) $$ Hnx
      intro D Hn
      obtain ⟨m', b, hc', hb, hD⟩ := Hn
      have hk := netN.msgCode_kind hc' (rfl : netN.msgCode (Msg.prepareReply mm1) = _)
      cases m' <;> simp only [netN.msgKindIdx] at hk <;> try exact absurd hk (by decide)
      obtain ⟨g', hb', hw', -⟩ := hb
      simp only [List.cons.injEq] at hb'
      exact ⟨g', hw', hb'.2 ▸ hD⟩
    · ihave ⟨Ho, %Hl⟩ := netN.prepareReply_len _ _ _ $$ Ho
      iunfold wire.gryffproto.PrepareReply.own at Ho
      icases Ho with ⟨%sl, Ho, Hs⟩
      imod (ownSlice_persist _ _ _) $$ Hs with #Hs
      imodintro
      iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.prepareReply (prepareReplyOf g), wire.gryffproto.PrepareReply.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, Hl.1, Hl.2, rfl⟩
      unfold msgAt
      iexists g, sl; iframe Ho Hs; ipureintro; rfl
    · imodintro
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | executed mm1 =>
    obtain rfl := Option.some.inj hc.symm
    simp only [msgTy, freshMsg]
    iintro %Φ ⟨#Hg, #He, #Hb, #Hio, #Hrd, #Hnx, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (wire.gryffproto.Executed.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, -, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Msg.executed (executedOf g), wire.gryffproto.Executed.enc g
      iframe Hown
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        rw [msgWire_eq]
        exact ⟨g, rfl, rfl⟩
      unfold msgAt
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  | executeOverwrite mm1 => simp [netN.msgCode] at hc

end

end Perennial.gryff.replica2
