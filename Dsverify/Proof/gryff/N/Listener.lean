/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Listener.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: `genericsmr.(*Replica).replicaListener` (proof of `Replica2/Specs.lean`'s
`Replica.replicaListener.wp`)

Each message read from peer `q`'s stream gets its receive token (`peerStream_recv`, `recv_msg`)
and goes, with it, on its kind's channel (the rpc table of `genericOk`).
-/
module

public import Dsverify.Proof.gryff.N.Recv
public import Dsverify.Proof.gryff.N.Stats
public import Dsverify.Proof.gryff.N.SpecsDefs
public import Perennial.Proof.fmt.Results
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure
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


/-- A reader whose underlying stream's bytes after `hdr` are a prefix of peer `q`'s stream: so are
the bytes it has returned. -/
theorem ownReader_peer (γ : GryffNames GF) (q k : Fin 3) (br : Loc) (rd : wire.RSt GF)
    (I : List w8 → IProp GF) (hdr Y : List w8) (hY : Y ≠ []) :
    wire.ownReader br rd I (hdr ++ Y) ∗
        □ (∀ Y', ⌜Y' ≠ []⌝ -∗ wire.ownReader br rd I (hdr ++ Y') ={⊤}=∗
          wire.ownReader br rd I (hdr ++ Y') ∗ ∃ W, peerStreamOk γ.proto q k W ∗ ⌜Y' <+: W⌝) ⊢
      |={⊤}=> wire.ownReader br rd I (hdr ++ Y) ∗ ∃ W, peerStreamOk γ.proto q k W ∗ ⌜Y <+: W⌝ := by
  iintro ⟨Hown, #Hbr⟩
  iapply Hbr $$ %Y %hY Hown

set_option goose.wp.extras true

theorem dec_ft : decide ((#false : val) = #true) = false :=
  decide_eq_false (fun h => Bool.noConfusion (GoGlobalContext.intoVal_inj_bool h))

theorem dec_tt : decide ((#true : val) = #true) = true := decide_eq_true rfl
theorem dec_ff : decide ((#false : val) = #false) = true := decide_eq_true rfl

theorem replicaListener_wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3)
    (r gR rd : Loc) (ms : List Msg) (hq : q ≠ k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ netN.peerReaderB γ q k rd ms ∗
        rxCurTok γ.proto q k ms.length }}
      (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"replicaListener")) (Val #(W64 q.val))) (Val #rd))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrep, #HgR, Hrd, Hcur⟩
  ihave Hr := (isReplica_open ..).1 $$ Hrep
  icases Hr with ⟨%gR2, %h, #Hex, #HgR2, -, -, -, -, -, -, -, #Hgen⟩
  icombine HgR HgR2 gives %Heq
  subst Heq
  ihave Hx := (isExec_open ..).1 $$ Hex
  icases Hx with ⟨%gR3, %mtx, %ex, %p, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hinv, -⟩
  ihave ⟨%rt, %st, %M, #Hrt, #HM, #Htab, #Hst, #Hsto, #HId, #HSh, #Hgp, #Hep⟩ :=
    genericOk_listen γ ρ k r gR h $$ Hgen
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  wp_auto
  ihave IH : iprop(∃ (mt : w8) (e : GoInterface),
      "msgType" ∷ msgType_ptr ↦ mt ∗ "err" ∷ err_ptr ↦ e ∗
      "Hst" ∷ ((⌜e = interface.nil⌝ ∗ ∃ ms' : List Msg, netN.peerReaderB γ q k rd ms' ∗
          rxCurTok γ.proto q k ms'.length) ∨ ⌜e ≠ interface.nil⌝)) $$ [msgType err Hrd Hcur]
  · iexists _, _
    iframe msgType err
    ileft
    isplitr
    · ipureintro; rfl
    iexists ms
    iframe
  wp_for IH
  icases Hst with (⟨%He, %ms', Hrd, Hcur⟩ | %He)
  rotate_left
  · obtain ⟨ei, rfl⟩ : ∃ ei, e = interface.ok ei := by
      cases e with
      | nil => exact absurd rfl He
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    rw [dec_ft]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_true]
    wp_auto
    iapply HΦ; itrivial
  subst He
  wp_auto
  rw [dec_tt]
  simp only [↓reduceIte]
  wp_auto
  -- the reader
  iunfold netN.peerReaderB at Hrd
  icases Hrd with ⟨%rdi, %I, %hdr, %V, #Hrdok, Hown, %HV, #Hbr⟩
  wp_apply (wire.wp_ReadByte rd rdi I (hdr ++ V)) $$ [$Hrdok $Hown]
    as %c %err (⟨%Herr, Hown⟩ | ⟨%Herr, -, Hown⟩)
  rotate_left
  · -- a read error: the loop ends
    obtain ⟨ei, rfl⟩ : ∃ ei, err = interface.ok ei := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    wp_for_post
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  -- the next message's code
  ihave Hup := ownReader_peer γ q k rd rdi I hdr (V ++ [c]) (by simp) $$ [Hown]
  · rw [← List.append_assoc]; iframe Hown Hbr
  iapply fupd_wp
  imod Hup with ⟨Hown, %W, #Hps, %HW⟩
  imodintro
  ihave %Hnext := peer_next γ q k ms' V W c [] HV (by simpa using HW) $$ Hps
  obtain ⟨m1, e1, hc1, hm1, -⟩ := Hnext
  obtain ⟨hc6, hc7⟩ := netN.msgCode_ne_beacon hc1
  rw [decide_eq_false hc6]
  wp_auto
  rw [decide_eq_false hc7]
  wp_auto
  -- the rpc table's entry for the kind
  have hne : netN.msgCode m1 ≠ none := by rw [hc1]; simp
  ihave #Hent := BigSepL.bigSepL_mem (msgKind_mem m1 hne) $$ Htab
  icases Hent with ⟨%c', %pp, %obj, %ch, %Hc', #Hpp, #Hbag⟩
  rw [kindCode_msgKind m1 hne, hc1] at Hc'
  obtain ⟨hcc, hpp⟩ := Hc'
  obtain rfl := Option.some.inj hcc
  wp_apply (wp_map_lookup2 (V := Loc) go.uint8 _ rt M c DFrac.discard) $$ [HM] as -
  · iexact HM
  rw [hpp]
  simp only [Option.getD_some, Option.isSome_some, decide_true]
  iStructNamed Hpp
  wp_auto
  rw [kindTy_msgKind m1 hne]
  wp_apply (wp_New_msg m1 obj) $$ [] as %l Hfresh
  · ipureintro; exact hne
  wp_apply (wp_Unmarshal_msg m1 c hc1 l rd rdi I (hdr ++ (V ++ [c]))) $$ [Hown Hfresh]
    as %err2 (⟨%Herr2, %m, %e, %Hm, Hmsg, Hown⟩ | ⟨%Herr2, %R', Hown⟩)
  · iframe Hown Hfresh
    iframe #
    iunfold wire.readNext
    imodintro
    iintro %D HI
    rw [show hdr ++ (V ++ [c]) ++ D = hdr ++ (V ++ [c] ++ D) by simp]
    imod Hbr $$ %(V ++ [c] ++ D) %(by simp) HI with ⟨HI, %W', #Hps', %HW'⟩
    ihave %Hn := peer_next γ q k ms' V W' c D HV (by simpa using HW') $$ Hps'
    imodintro
    iframe HI
    ipureintro
    obtain ⟨m', e', h1, h2, h3⟩ := Hn
    exact ⟨[], m', e', h1, h2, by simpa using h3⟩
  rotate_left
  · -- an unmarshaling error: the loop ends
    obtain ⟨ei, rfl⟩ : ∃ ei, err2 = interface.ok ei := by
      cases err2 with
      | nil => exact absurd rfl Herr2
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    iright; ipureintro; simp
  subst Herr2
  wp_auto
  -- the message's receive token
  ihave Hup := ownReader_peer γ q k rd rdi I hdr (V ++ c :: e) (by simp) $$ [Hown]
  · rw [show hdr ++ (V ++ [c]) ++ e = hdr ++ (V ++ c :: e) by simp]; iframe Hown Hbr
  iapply fupd_wp
  imod Hup with ⟨Hown, %W3, #Hps3, %HW3⟩
  imodintro
  have hV' : msgsWire (ms' ++ [m]) (V ++ c :: e) := msgsWire_snoc HV Hm.2
  ihave #Hlb := peerStream_recv γ.proto q k (ms' ++ [m]) (V ++ c :: e) W3 hV' HW3 $$ Hps3
  iapply fupd_wp
  imod (recv_msg γ.proto q k ms'.length ms' m ⊤ (fun p hp => CoPset.subseteq_top p hp) rfl) $$ [$Hinv $Hcur $Hlb]
    with ⟨Hcur, Htok⟩
  imodintro
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  obtain ⟨hkd, hty⟩ := msgCode_same Hm.1 hc1
  wp_apply (wp_bag_send (ρ.chans (msgKind m1)) ch (interface.mkOk (msgTy m1) #l)
    (msgChanP γ ρ k (msgKind m1))) $$ [Hmsg Htok]
  · iframe Hbag
    unfold msgChanP
    iexists l, m
    isplitr
    · ipureintro; exact ⟨hkd, by rw [hty]⟩
    iframe Hmsg
    iexists q, ms'.length
    iexact Htok
  -- `Stats.Max(Sprintf("server_rpc_%d_chan_length", code), len(ch))`
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf
    go!"server_rpc_%d_chan_length"
    [.lit go!"server_rpc_", .dir none _root_.Perennial.fmt.verb_d, .lit go!"_chan_length"]
    _ _ _ _ (by fmt_encode) ?fits ?pa $$ [$Hfmt $Hasl] as %key ⟨-, %Hkey⟩
  case pa => exact .int _ _ _ _ (.uint8 _) .nil
  case fits => fmt_fits
  ihave #Hch := is_bag_is_chan _ _ _ $$ Hbag
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_Len $$ [$Hch] as %len -
  ihave #Hstats : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats $$ []
  · iPkgInit
  have hkey : key ∉ netN.strIntKeys := by
    rw [Hkey]
    simp [_root_.Perennial.fmt.render, netN.strIntKeys]
  wp_apply (netN.wp_Max st key len hkey) $$ [$Hsto] as %n -
  wp_for_post
  iframe
  iexists _, _
  iframe
  ileft
  isplitr
  · ipureintro; rfl
  iexists ms' ++ [m]
  rw [List.length_append, List.length_singleton]
  iframe Hcur
  iunfold netN.peerReaderB
  iexists rdi, I, hdr, V ++ c :: e
  iframe Hrdok Hown Hbr
  ipureintro; exact hV'

end

end Perennial.gryff.replica2
