/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*MSync).Unmarshal(br)` (18): `gob.NewDecoder(br).Decode(m)`, over the real `encoding/gob`'s
specs (`encoding.gob.NewDecoder.spec`, `encoding.gob.Decoder.Decode.spec`, hypotheses; format
`sp.GobFmt`). On a peer stream the next message is an `MSync` written by gob (`sp.nextOk 18`: a
`.sync s bs` with `GobFmt.bytes s bs`), so without an error the decoder read exactly `bs`, and
the target holds `s` up to its maps' order.

**Port change.** The lab's gob model read one frame (`gobFrame`, an 8-byte length) and decoded
it with the kit's codec; the real decoder reads gob's messages through the value's.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableLaw
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.encoding.gob.Decoder__Decode
public import Dsverify.Spec.encoding.gob.NewDecoder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MsgRep

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

theorem sync_of_next [sp.GobFmt] {d : List w8} (h : sp.nextOk (W8 18) d) :
    ∃ (s : sp.SyncWire) (bs w : List w8), sp.GobFmt.bytes s bs ∧ d <+: bs ++ w := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  exact ⟨_, _, w, hw, hp⟩

section entries
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

/-- The persistent facts `MSync`'s entry uses: gob's package, the readers' packages. -/
def ctxS : IProp netDistGF :=
  iprop(isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.gob ∗
    isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗ isPkgInit (PROP := IProp netDistGF) pkg_id.bufio)

instance ctxS_persistent : Persistent (ctxS (hG := hG)) := by
  unfold ctxS; infer_instance

/-- `(*MSync).Unmarshal(br)` on a stream whose next bytes are an `MSync`'s gob stream. -/
abbrev MSync.Unmarshal.specS : Prop :=
  ∀ (l br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF) (R : List w8),
  {{ ctxS ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 18)) ∗
      bufio.ownReader br rd I R ∗ l ↦ (zero_val swift.MSync) }}
    (App (Val (l @!! go.GoType.PointerType swift.MSync.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (s : sp.SyncWire) (bs : List w8) (m' : sp.SyncWire),
          ⌜data = bs ∧ sp.GobFmt.bytes s bs ∧ sp.KitVal.equiv (.msync s) (.msync m')⌝ ∗
          structOwn swift.MSync.ty l (DFrac.own 1) (.msync m')) ∨
        ⌜err ≠ interface.nil⌝) }}

theorem MSync.Unmarshal.wp_proof (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF)) :
    MSync.Unmarshal.specS (hG := hG) := by
  intro l br rd I R
  wp_start as ⟨#Hctx, #Hrd, #Hlaw, Hown, Hl⟩
  ihave #Hctx' := Hctx
  iunfold ctxS at Hctx'
  icases Hctx' with ⟨#Hgob, #Hio, #Hbuf⟩
  ihave #Hrs := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  wp_auto
  wp_apply wp_ND br $$ [$Hgob] as %dec Hdec
  try wp_auto
  -- the postcondition under an update: the stream law's fact comes a step later
  iapply wp_fupd
  wp_apply wp_Dec dec _ (bufio.ownReader br rd I) R l $$ [$Hgob $Hio $Hrs $Hown $Hdec $Hl]
    as %e ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %m', %Hd, Hs⟩ | %He)
  · subst He
    icases streamLaw_use br rd I R data _ $$ [$Hlaw $Hown] with ⟨Hown, >%Hn⟩
    try wp_auto
    obtain ⟨s, bs, w, hb, u, hu⟩ := sync_of_next Hn
    obtain ⟨hdb, he⟩ := Hd s bs u w hb hu
    iapply HΦ
    iexists _
    iframe Hown
    ileft
    isplitr
    · ipureintro; rfl
    iexists s, bs, m'
    unfold encoding.gob.syncOwn
    iframe Hs
    ipureintro
    exact ⟨hdb, hb, he⟩
  · try wp_auto
    iapply HΦ
    iexists _
    iframe Hown
    iright
    ipureintro; exact He

theorem unmarshalOk_sync (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF)) (l : Loc) :
    ctxS ∗ l ↦ (zero_val swift.MSync) ⊢ sp.unmarshalOk (W8 18) (swift.msgRep (W8 18))
      (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  wp_apply MSync.Unmarshal.wp_proof wp_ND wp_Dec l br rd I R $$ [$Hctx $Hrd $Hlaw $Hown $Hl]
    as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %s, %bs, %m', ⟨%Hd, %Hb, %Hx⟩, Hs⟩ | %He)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .sync s bs
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hb
    unfold swift.msgRep swift.msgRepM
    iexists l, m'
    iframe Hs
    ipureintro; exact ⟨rfl, Hx⟩
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem wp_New_MSync (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MSync.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l);
        l ↦ (zero_val swift.MSync) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem newOk_sync (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF)) (o : Loc) :
    ctxS ⊢ sp.newOk (W8 18) (swift.msgRep (W8 18))
      (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #o) := by
  apply newOk_of _ _ _ o ctxS (fun l => iprop(l ↦ (zero_val swift.MSync)))
  · iintro %Φ - HΦ
    iapply wp_New_MSync o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_sync wp_ND wp_Dec l

end entries

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
