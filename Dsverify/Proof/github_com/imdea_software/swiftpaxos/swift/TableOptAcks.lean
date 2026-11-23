/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableOptAcks.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*MOptAcks).Unmarshal` (14) on a stream whose next bytes are an `MOptAcks`'s body: the
8-byte header, the count (`optAcks_v1`), the acks by the element decoder (`Ack.Unmarshal.specS`,
each under its law `ackNext`, `optAcks_elem`); the acks' slices made read-only (`ackRepr`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAcks

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `(*MOptAcks).Unmarshal(br)`: without an error, the bytes read are the body of a
well-formed `.optAcks r b al`, which `t` represents (`swift.msgRepM`'s shape). -/
abbrev MOptAcks.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MOptAcks) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 14)) ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MOptAcks.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b : w32) (asl : GoSlice) (ps : List (swift.Ack × sp.Ack)),
          ⌜data = (sp.Msg.optAcks r b (ps.map Prod.snd)).body ∧
            (sp.Msg.optAcks r b (ps.map Prod.snd)).wf⌝ ∗
          t ↦ swift.MOptAcks.mk r b asl ∗ asl ↦* ps.map Prod.fst ∗
          [∗list] p ∈ ps, swift.ackRepr p.1 p.2) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MOptAcks, t ↦ v')) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] in
/-- The first 8 bytes of a 10-byte buffer, as the slice `b[:8]`. -/
theorem slice_take8 (p : Loc) (xs : List w8) (hl : xs.length = 10) :
    (slice.mk p (W64 10) (W64 10) ↦* xs : IProp netDistGF) ⊢
      slice.mk p (W64 8) (W64 10) ↦* xs.take 8 := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := H; simp [slice.nil] at h1
  iright
  simp only
  icases (array_split (V := w8) (W64 8) p (DFrac.own 1) _ _ (by word)).1 $$ H
    with ⟨H, -⟩
  isplitl [H]
  · iExactEq H; rfl
  · ipureintro; simp [hl]; decide

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] go_gctx hG sem in
theorem optAcks_body (r b : w32) (al : List sp.Ack) :
    (sp.Msg.optAcks r b al).body = (sp.le32 r ++ sp.le32 b) ++ sp.varintLen al.length ++
      (al.map sp.Ack.enc).flatten := by
  simp [sp.Msg.body, List.append_assoc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem MOptAcks.Unmarshal.wp_proof (wp_Ack : Ack.Unmarshal.specS (hG := hG)) :
    MOptAcks.Unmarshal.specS (hG := hG) := by
  intro t v br rd I R
  wp_start as ⟨#Hctx, #Hrd, #Hlaw, Hown, Ht⟩
  ihave #Hctx' := Hctx
  iunfold ctxV at Hctx'
  icases Hctx' with ⟨#Hio, #Hbuf, #Hbin, %ov, #Hov, %Hovn⟩
  ihave #Hbr := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) swift.byteReader.ty = true := by
    go_type_set
  try wp_auto
  rw [hts]
  wp_auto
  ihave Hb := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl]
  ihave Hsl := slice_take8 b_ptr _ (by simp) $$ Hb
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
    show W64 10 - W64 0 = W64 10 from rfl]
  try wp_auto
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ _ (W64 8) (by simp; decide) $$
    [$Hio $Hbr $Hown $Hsl] as %n %err ⟨%data, %Hd, Hsl, Hown, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists data
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  have h8 : data.length = 8 := by
    have := herr.1 rfl; simp at hdl; have : sint.Z (W64 8) = 8 := rfl; omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ :
      ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8, data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
    match data, h8 with
    | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
  isimp only [List.length_cons, List.length_nil, List.take_replicate, List.drop_replicate,
    List.append_nil, Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
  wp_auto
  rd_ld8
  isimp only [← encoding.binary.leToU32_4] at Ht
  -- the acks' count
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    rw [List.append_assoc]
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht1, hb1, hx1⟩ := Hx rfl
  icases streamLaw_use br rd I R ([d0, d1, d2, d3, d4, d5, d6, d7] ++ vd1) _ $$ [$Hlaw Hown]
    with ⟨Hown, >%Hn1⟩
  · iExactEq Hown; simp only [List.append_assoc]
  obtain ⟨n, rfl, hn62⟩ := optAcks_v1 rfl ht1 Hn1
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n hb1 hx1
  try wp_auto
  wp_apply wp_slice_make2 (V := swift.Ack) (W64 n) as %sl ⟨Hsl', -⟩
  · ipureintro; word
  ihave %Hsllen := ownSlice_len $$ Hsl'
  rw [show sint.nat (W64 n) = n by word]
  try wp_auto
  ihave HL : (∃ (k : Nat) (ps : List (swift.Ack × sp.Ack)),
      "i" ∷ i_ptr ↦ W64 k ∗
      "Ht" ∷ t ↦ swift.MOptAcks.mk (leToU32 [d0, d1, d2, d3]) (leToU32 [d4, d5, d6, d7]) sl ∗
      "Hsl" ∷ sl ↦* (ps.map Prod.fst ++ List.replicate (n - k) (zero_val swift.Ack)) ∗
      "Hreps" ∷ ([∗list] p ∈ ps, swift.ackRepr p.1 p.2) ∗
      "Hown" ∷ bufio.ownReader br rd I
        (R ++ ([d0, d1, d2, d3, d4, d5, d6, d7] ++ sp.varintLen n ++
          ((ps.map Prod.snd).map sp.Ack.enc).flatten)) ∗
      "%Hk" ∷ ⌜k ≤ n ∧ ps.length = k ∧ ∀ p ∈ ps, p.2.wf⌝ : IProp netDistGF) $$ [i Ht Hsl' Hown]
  · iexists 0, []
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · obtain ⟨hkn', rfl, hok⟩ := Hk
    have hkn : ps.length < n := by
      have h1 : sint.Z (W64 (ps.length : Int)) = ps.length := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    have hlook : (ps.map Prod.fst ++ List.replicate (n - ps.length) (zero_val swift.Ack))[
        ((ps.length : Nat) : Int).toNat]? = some (zero_val swift.Ack) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    have hbnd : 0 ≤ sint.Z (W64 (ps.length : Int)) ∧
        sint.Z (W64 (ps.length : Int)) < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hsllen
      have hn' : sint.nat (W64 (n : Int)) = n := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have : sint.Z (W64 (ps.length : Int)) = ps.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (ps.length : Int)) = ps.length := by word
    rw [ite_cond_eq_true _ _ (eq_true hbnd)]
    rw [hk64]
    icases ownSlice_elem_acc ((ps.length : Nat) : Int) (zero_val swift.Ack) sl _ _ (by omega)
      hlook $$ Hsl with ⟨He, Hsl⟩
    have hwf : ∀ a ∈ ps.map Prod.snd, a.wf := by
      intro a ha; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha; exact hok p hp
    have hel : ∀ d, sp.nextOk (W8 14)
        (([d0, d1, d2, d3, d4, d5, d6, d7] ++ sp.varintLen n ++
          ((ps.map Prod.snd).map sp.Ack.enc).flatten) ++ d) → ackNext d :=
      fun d hd => optAcks_elem (prev := ps.map Prod.snd) rfl hwf (by simp; omega) hd
    ihave #Hlaw1 := streamLaw_shift br rd I R
      ([d0, d1, d2, d3, d4, d5, d6, d7] ++ sp.varintLen n ++
        ((ps.map Prod.snd).map sp.Ack.enc).flatten) _ $$ Hlaw
    ihave #Hlaw' := streamLaw_mono br rd I _ _ ackNext hel $$ Hlaw1
    wp_apply wp_Ack _ _ br rd I _ $$ [$Hctx $Hrd $Hlaw' $He Hown]
      as %err ⟨%data, Hown, Hres⟩
    · iExactEq Hown; simp [List.append_assoc]
    icases Hres with (⟨%Hen, %a, %dsl, %csl, ⟨%Hd, %Hwf⟩, He, Hdsl, Hcsl⟩ | ⟨%Hen, %v', He⟩)
    · subst Hen Hd
      imod ownSlice_persist $$ Hdsl with #Hdsl
      imod ownSlice_persist $$ Hcsl with #Hcsl
      ihave Hsl := Hsl $$ He
      wp_auto
      wp_for_post
      iframe
      iexists ps.length + 1, ps ++ [(swift.Ack.mk (ofCmdId a.id) dsl csl a.seqnum, a)]
      isplitl [i]
      · iExactEq i; congr 1; word
      isplitl [Ht]
      · iexact Ht
      isplitl [Hsl]
      · iExactEq Hsl; congr 1
        rw [Int.toNat_natCast, swift.rd.set_slot Prod.fst ps _ _ (n - ps.length) (by omega)]
        simp [List.map_append, List.append_assoc, show n - (ps.length + 1) = n - ps.length - 1 by omega]
      isplitl [Hreps]
      · iapply (BigSepL.bigSepL_snoc).2
        iframe Hreps
        unfold swift.ackRepr
        iframe Hdsl Hcsl
        ipureintro; exact ⟨rfl, rfl⟩
      isplitl [Hown]
      · iExactEq Hown; congr 1
        simp [List.map_append, List.flatten_append, List.append_assoc]
      ipureintro
      refine ⟨by omega, by simp, ?_⟩
      intro p hp
      rcases List.mem_append.1 hp with h' | h'
      · exact hok p h'
      · simp at h'; subst h'; exact Hwf
    · rcases err with eo | _
      · wp_auto
        wp_for_post
        iapply HΦ
        iexists _
        isplitl [Hown]
        · iExactEq Hown; simp only [List.append_assoc]; rfl
        iright
        isplitr
        · ipureintro; exact Hen
        iexists _
        iexact Ht
      · exact absurd rfl Hen
  · -- the end: the message
    obtain ⟨hkn', hlk, hok⟩ := Hk
    have hkn : k = n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    subst hkn hlk
    have hwf : ∀ a ∈ ps.map Prod.snd, a.wf := by
      intro a ha; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha; exact hok p hp
    try wp_auto
    iapply HΦ
    iexists (sp.Msg.optAcks (leToU32 [d0, d1, d2, d3]) (leToU32 [d4, d5, d6, d7])
      (ps.map Prod.snd)).body
    isplitl [Hown]
    · iExactEq Hown; congr 2
      rw [optAcks_body]
      simp only [sp.le32]
      rw [leToU32_le _ rfl, leToU32_le _ rfl]
      simp
    ileft
    isplitr
    · ipureintro; rfl
    iexists leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7], sl, ps
    isplitr
    · ipureintro
      exact ⟨rfl, by simpa using hn62, hwf⟩
    iframe Ht Hreps
    iExactEq Hsl; simp

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

section entries
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

theorem unmarshalOk_optAcks (wp_Ack : Ack.Unmarshal.specS (hG := hG)) (l : Loc)
    (v : swift.MOptAcks) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 14) (swift.msgRep (W8 14))
      (interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  wp_apply MOptAcks.Unmarshal.wp_proof wp_Ack l v br rd I R $$ [$Hctx $Hrd $Hlaw $Hown $Hl]
    as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %r, %b, %asl, %ps, ⟨%Hd, %Hwf⟩, Ht, Hasl, Hreps⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .optAcks r b (ps.map Prod.snd)
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hwf
    unfold swift.msgRep swift.msgRepM
    iexists l, asl, ps
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iframe
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

omit [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
theorem wp_New_MOptAcks (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MOptAcks.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #l);
        l ↦ (zero_val swift.MOptAcks) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem newOk_optAcks (wp_Ack : Ack.Unmarshal.specS (hG := hG)) (o : Loc) :
    ctxV ⊢ sp.newOk (W8 14) (swift.msgRep (W8 14))
      (interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #o) := by
  apply newOk_of _ _ _ o ctxV (fun l => iprop(l ↦ (zero_val swift.MOptAcks)))
  · iintro %Φ - HΦ
    iapply wp_New_MOptAcks o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_optAcks wp_Ack l _

end entries

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
