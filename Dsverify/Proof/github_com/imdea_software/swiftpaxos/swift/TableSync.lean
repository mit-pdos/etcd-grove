/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*MSync).Unmarshal(br)` (18): `gob.NewDecoder(br).Decode(m)` (the codec group's specs,
`encoding.gob.NewDecoder.spec`, `encoding.gob.Decoder.Decode.spec`, as hypotheses): without an
error the reader delivered one gob frame `gobFrame bs`, and the target holds the codec's
decoding of `bs`. On a peer stream the frame is the next message's (`sp.nextOk 18`: an `MSync`
whose codec encoding fits the frame), so the bytes are its body; the target holds the message's
value when its map listings have distinct keys (`KitVal.wf`, which the codec's `dec` needs).

`gobFrame_body`: `Decoder.Decode.spec`'s postcondition bounds the frame's body
(`bs.length < 2 ^ 64`, change log C17, SWC-G1), so the frame's 8-byte length determines `bs`
among the stream's frames.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableLaw
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.encoding.gob.Decoder__Decode
public import Dsverify.Spec.encoding.gob.NewDecoder
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitLike

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

/-- The zero `MSync`'s codec value. -/
def syncX0 : sp.KitVal := .msync ⟨0, 0, none, none, none⟩

theorem merge_syncX0 (s : sp.SyncWire) : sp.KitVal.merge syncX0 (.msync s) = .msync s := by
  obtain ⟨r, b, p, c, d⟩ := s
  simp [syncX0, sp.KitVal.merge]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem tag17 {x : sp.KitVal} (h : x.tag = 17) : ∃ s, x = .msync s := by
  cases x <;> simp [sp.KitVal.tag] at h
  exact ⟨_, rfl⟩

/-- The frame read is the stream's `MSync`'s (see the file header). -/
theorem gobFrame_body {bs : List w8} {s : sp.SyncWire} {u w : List w8} (hs : s.wf)
    (hb : bs.length < 2 ^ 64)
    (h : sp.gobFrame bs ++ u = sp.gobFrame (sp.KitVal.msync s).encode ++ w) :
    bs = (sp.KitVal.msync s).encode := by
  unfold sp.gobFrame at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hl, h2⟩ := sp.u64Le_peel h
  unfold sp.SyncWire.wf at hs
  have hlen : bs.length = (sp.KitVal.msync s).encode.length := by
    have := congrArg BitVec.toNat hl
    simp only [W64, BitVec.toNat_ofInt] at this
    omega
  exact (List.append_inj h2 hlen).1

theorem sync_of_next {d : List w8} (h : sp.nextOk (W8 18) d) :
    ∃ (s : sp.SyncWire) (w : List w8), s.wf ∧ d <+: sp.gobFrame (sp.KitVal.msync s).encode ++ w := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  exact ⟨_, w, hw, hp⟩

section entries
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]
-- the kit's codec instance (any `KitLike` one: the linked results use `kitCodecC`, D6)
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

set_option goose.wp.extras true

/-- The persistent facts `MSync`'s entry uses: the gob model's package and codec, the kit's
codec, the readers' packages. -/
def ctxS : IProp netDistGF :=
  iprop(isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.gob ∗
    encoding.gob.codecSet (GF := netDistGF) ∗ net.rpc.kitCodecOk (GF := netDistGF) ∗
    isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗ isPkgInit (PROP := IProp netDistGF) pkg_id.bufio)

instance ctxS_persistent : Persistent (ctxS (hG := hG)) := by
  unfold ctxS; infer_instance

/-- What the decoding gives back (`Decode`'s `Ψ bs ok`): the target holds some value of its
type, the `MSync` of `bs` when `bs` encodes a well-formed one with distinct keys. -/
def syncPsi (l : Loc) (bs : List w8) (_ok : Bool) : IProp netDistGF :=
  iprop(∃ x1 : sp.KitVal,
    kitValOwn (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) (DFrac.own 1) x1 ∗
    ⌜x1.tag = 17 ∧ ∀ s : sp.SyncWire, bs = (sp.KitVal.msync s).encode → s.wf →
      sp.KitVal.wf (.msync s) → x1 = .msync s⌝)

/-- `(*MSync).Unmarshal(br)` on a stream whose next bytes are an `MSync`'s frame. -/
abbrev MSync.Unmarshal.specS : Prop :=
  ∀ (l br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF) (R : List w8),
  {{ ctxS ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 18)) ∗
      bufio.ownReader br rd I R ∗ l ↦ (zero_val swift.MSync) }}
    (App (Val (l @!! go.GoType.PointerType swift.MSync.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (s : sp.SyncWire) (x : sp.KitVal),
          ⌜data = (sp.Msg.sync s).body ∧ s.wf ∧ (sp.KitVal.wf (.msync s) → x = .msync s)⌝ ∗
          structOwn swift.MSync.ty l (DFrac.own 1) x) ∨
        ⌜err ≠ interface.nil⌝) }}

theorem MSync.Unmarshal.wp_proof (wp_ND : encoding.gob.NewDecoder.spec (GF := netDistGF))
    (wp_Dec : encoding.gob.Decoder.Decode.spec (GF := netDistGF)) :
    MSync.Unmarshal.specS (hG := hG) := by
  intro l br rd I R
  wp_start as ⟨#Hctx, #Hrd, #Hlaw, Hown, Hl⟩
  ihave #Hctx' := Hctx
  iunfold ctxS at Hctx'
  icases Hctx' with ⟨#Hgob, #Hcs, #Hko, #Hio, #Hbuf⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  ihave #Hrs := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  ihave HD : kitValOwn (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) (DFrac.own 1)
      syncX0 $$ [Hl]
  · unfold kitValOwn structOwn syncX0
    iexists swift.MSync.ty, l
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    isplitr
    · ipureintro; rfl
    iexists map.nil, map.nil, map.nil
    isplitl [Hl]
    · iExactEq Hl; rfl
    unfold mapOwn
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    ipureintro; rfl
  wp_auto
  wp_apply wp_ND _ $$ [$Hgob] as %dec Hdec
  try wp_auto
  wp_apply wp_Dec dec (DFrac.own 1) _ (bufio.ownReader br rd I) R
    (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l)
    (kitValOwn (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #l) (DFrac.own 1) syncX0)
    (syncPsi l) $$ [$Hgob $Hcs $Hko $Hio $Hrs $Hown $Hdec $HD] as %e ⟨Hdec, %data, Hown, Hres⟩
  · imodintro
    iintro HD %bs
    iapply KitLike.dec_intro
    unfold decT
    iexists syncX0
    iframe HD
    isplitr
    · ipureintro; rfl
    isplit
    · iintro %y %Hy Hy
      obtain ⟨hbs, htag, hwf⟩ := Hy
      obtain ⟨s', rfl⟩ := tag17 (x := y) (by rw [htag]; rfl)
      rw [merge_syncX0]
      unfold syncPsi
      iexists .msync s'
      iframe Hy
      ipureintro
      refine ⟨rfl, fun s hs hsw _ => ?_⟩
      rw [sp.syncEnc_inj hsw (hs.symm.trans hbs)]
    · iintro %Hn %ok ⟨%x1, %Htag, Hx1⟩
      unfold syncPsi
      iexists x1
      iframe Hx1
      ipureintro
      refine ⟨by rw [Htag]; rfl, fun s hs _ hk => ?_⟩
      exact absurd hs (Hn (.msync s) rfl hk)
  try wp_auto
  icases Hres with (⟨%He, %bs, ⟨%Hd, %Hbl⟩, Hpsi⟩ | ⟨%He, -, -⟩)
  · subst He Hd
    icases streamLaw_use br rd I R (sp.gobFrame bs) _ $$ [$Hlaw $Hown] with ⟨Hown, %Hn⟩
    obtain ⟨s, w, hsw, u, hu⟩ := sync_of_next Hn
    have hbs := gobFrame_body hsw Hbl hu
    subst hbs
    unfold syncPsi
    icases Hpsi with ⟨%x1, Hx1, ⟨%Htag, %Hx⟩⟩
    obtain ⟨s1, rfl⟩ := tag17 Htag
    unfold kitValOwn
    icases Hx1 with ⟨%ty, %p, ⟨%Hv, -⟩, Hs⟩
    have hp : ty = swift.MSync.ty ∧ p = l := by
      simp [interface.mkOk] at Hv
      exact ⟨Hv.1.symm, (go.intoVal_inj Hv.2).symm⟩
    obtain ⟨rfl, rfl⟩ := hp
    iapply HΦ
    iexists _
    iframe Hown
    ileft
    isplitr
    · ipureintro; rfl
    iexists s, .msync s1
    iframe Hs
    ipureintro
    exact ⟨rfl, hsw, fun hk => Hx s rfl hsw hk⟩
  · iapply HΦ
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
  icases Hres with (⟨%He, %s, %x, ⟨%Hd, %Hsw, %Hx⟩, Hs⟩ | %He)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .sync s
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hsw
    unfold swift.msgRep swift.msgRepM
    iexists l, x
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
