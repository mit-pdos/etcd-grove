/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableClient.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`MFastAckClient.Unmarshal` (type 10) and `MReply.Unmarshal` (type 15) on a replica's peer
reader, and their table entries (`sp.newOk`): the client's proofs (Proof/swift/client/
Unmarshal.lean) with the client's stream (`sp.cw.rd_stOk`, `next_v1`, `next_v2`) replaced by
the reader's stream law (`sp.streamLaw`): each varint the decoder accepts is the encoding's own
count (`fac_v1`, `rep_v1`, `rep_v2`).

FINDING (MReply with an empty checksum): `(*MReply).Unmarshal` (fork swift/defs.go l.2841-3003)
sets `bs = b[:1]` only inside the checksum loop; with `len(Checksum) = 0` the result loop's
`io.ReadAtLeast(wire, bs, 1)` reads into `bs = b[:16]`, up to 16 bytes per result byte, so it
consumes bytes past the message (the reader loses the stream's alignment). A well-formed
`.reply` (`Msg.wf`) may have an empty checksum, so `MReply.Unmarshal.specS` asks for the law
`replyNext` (a reply with a non-empty checksum: what every reply's witness `checksum Ps D cs`
gives, `cs` ending with the dependency hash). No peer sends an `MReply` (`Msg.isPeer`, which
`sp.nextOk` says): on a peer stream the entry is never reached (`nextOk_reply`, vacuous); the
decoder's proof covers the client's streams' shape.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableLaw

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

open swift.handler (shashOf)
open swift.rd

/-! ## Pure: the counts are the encoding's -/

/-- What a reply decoder reads next: a reply with a non-empty checksum (see the header). -/
def replyNext (d : List w8) : Prop :=
  ∃ (r b : w32) (x : sp.CmdId) (cs : List sp.Hash) (v : List w8) (w : List w8),
    sp.hashesWf cs ∧ cs ≠ [] ∧ v.length < 2 ^ 62 ∧ d <+: (sp.Msg.reply r b x cs v).body ++ w

theorem nextOk10 {d : List w8} (h : sp.nextOk (W8 10) d) :
    ∃ (r b : w32) (x : sp.CmdId) (cs : List sp.Hash) (w : List w8),
      sp.hashesWf cs ∧ d <+: (sp.Msg.fastAckClient r b x cs).body ++ w := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> (try (simp [sp.Msg.code, sp.rpcTable] at hc; done))
  exact ⟨_, _, _, _, w, hw, hp⟩

theorem hashOk_of {cs : List sp.Hash} (h : sp.hashesWf cs) : sp.cw.hashOk cs :=
  fun x hx => h.2 x hx

/-- The first varint of an `MFastAckClient`: the frame's own count. -/
theorem fac_v1 {hdr d1 : List w8} (hl : hdr.length = 16) (ht : sp.uvTerm d1)
    (h : sp.nextOk (W8 10) (hdr ++ d1)) : ∃ n, d1 = sp.varintLen n ∧ n < 2 ^ 62 := by
  obtain ⟨r, b, x, cs, w, hw, u, hu⟩ := nextOk10 h
  simp only [sp.Msg.body] at hu
  have e : hdr ++ (d1 ++ u) = sp.cw.hdr16 r b x ++ (sp.encHashes cs ++ w) := by
    simpa [sp.cw.hdr16, List.append_assoc] using hu
  obtain ⟨-, e2⟩ := List.append_inj e (by rw [hl, sp.cw.hdr16_length])
  unfold sp.encHashes sp.varintLen at e2
  rw [List.append_assoc] at e2
  exact ⟨cs.length, (sp.cw.uvTerm_peel ht e2).1, hw.1⟩

/-- The first varint of a reply: its own count, positive. -/
theorem rep_v1 {hdr d1 : List w8} (hl : hdr.length = 16) (ht : sp.uvTerm d1)
    (h : replyNext (hdr ++ d1)) : ∃ n, d1 = sp.varintLen n ∧ n < 2 ^ 62 ∧ 0 < n := by
  obtain ⟨r, b, x, cs, v, w, hw, hne, -, u, hu⟩ := h
  simp only [sp.Msg.body] at hu
  have e : hdr ++ (d1 ++ u) = sp.cw.hdr16 r b x ++ (sp.encHashes cs ++ (sp.encBytes v ++ w)) := by
    simpa [sp.cw.hdr16, List.append_assoc] using hu
  obtain ⟨-, e2⟩ := List.append_inj e (by rw [hl, sp.cw.hdr16_length])
  unfold sp.encHashes sp.varintLen at e2
  rw [List.append_assoc] at e2
  exact ⟨cs.length, (sp.cw.uvTerm_peel ht e2).1, hw.1, List.length_pos_iff.2 hne⟩

/-- The second varint of a reply, after its hashes: its own count. -/
theorem rep_v2 {hdr d2 : List w8} {hs : List sp.Hash} (hl : hdr.length = 16)
    (hh : sp.cw.hashOk hs) (ht : sp.uvTerm d2)
    (h : replyNext (hdr ++ (sp.varintLen hs.length ++ (hs.flatten ++ d2)))) :
    ∃ m, d2 = sp.varintLen m ∧ m < 2 ^ 62 := by
  obtain ⟨r, b, x, cs, v, w, hw, -, hv, u, hu⟩ := h
  simp only [sp.Msg.body] at hu
  have e : hdr ++ (sp.varintLen hs.length ++ (hs.flatten ++ (d2 ++ u))) =
      sp.cw.hdr16 r b x ++ (sp.varintLen cs.length ++ (cs.flatten ++ (sp.uvarint (2 * v.length) ++
        (v ++ w)))) := by
    simpa [sp.cw.hdr16, sp.encHashes, sp.encBytes, sp.varintLen, List.append_assoc] using hu
  obtain ⟨-, e2⟩ := List.append_inj e (by rw [hl, sp.cw.hdr16_length])
  obtain ⟨hl2, e3⟩ := sp.cw.varintLen_peel e2
  obtain ⟨-, e4⟩ := sp.cw.flat_peel hh (hashOk_of hw) hl2 e3
  exact ⟨v.length, by unfold sp.varintLen; exact (sp.cw.uvTerm_peel ht e4).1, hv⟩

/-- `nextOk 15` is vacuous: no peer message has type 15 (`sp.nextOk` says `Msg.isPeer`). -/
theorem nextOk_reply (d : List w8) (h : sp.nextOk (W8 15) d) : replyNext d := by
  exfalso
  obtain ⟨m, w, -, hp, hc, -⟩ := h
  cases m <;> simp [sp.Msg.isPeer, sp.Msg.code, sp.rpcTable] at hp hc

section law
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- The stream law at any bytes `B` read: whatever `B` extends `R` with satisfies `L`. -/
theorem streamLaw_at (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8) (L : List w8 → Prop) (B : List w8) :
    sp.streamLaw br rd I R L ∗ bufio.ownReader br rd I B ⊢
      bufio.ownReader br rd I B ∗ ⌜∀ Y, B = R ++ Y → L Y⌝ := by
  iintro ⟨#Hlaw, Hown⟩
  by_cases hB : ∃ Y, B = R ++ Y
  · obtain ⟨Y0, rfl⟩ := hB
    icases streamLaw_use br rd I R Y0 L $$ [$Hlaw $Hown] with ⟨Hown, %H⟩
    iframe Hown
    ipureintro
    intro Y hY
    rw [← List.append_cancel_left hY]; exact H
  · iframe Hown
    ipureintro
    intro Y hY
    exact absurd ⟨Y, hY⟩ hB

end law

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- `(*MFastAckClient).Unmarshal(br)` on a peer reader whose next bytes are of an
`MFastAckClient` (type 10). -/
abbrev MFastAckClient.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MFastAckClient) (br : Loc) (rd : GoInterface)
    (I : List w8 → IProp netDistGF) (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 10)) ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MFastAckClient.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b : w32) (x : sp.CmdId) (cs : List sp.Hash) (csl : GoSlice),
          ⌜data = (sp.Msg.fastAckClient r b x cs).body ∧ (sp.Msg.fastAckClient r b x cs).wf⌝ ∗
          t ↦ swift.MFastAckClient.mk r b (ofCmdId x) csl ∗ csl ↦* cs.map shashOf) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MFastAckClient, t ↦ v')) }}

/-- `(*MReply).Unmarshal(br)` on a peer reader whose next bytes are of a reply with a
non-empty checksum (`replyNext`, see the header). -/
abbrev MReply.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MReply) (br : Loc) (rd : GoInterface)
    (I : List w8 → IProp netDistGF) (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R replyNext ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MReply.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b : w32) (x : sp.CmdId) (cs : List sp.Hash) (val : List w8)
          (csl vsl : GoSlice),
          ⌜data = (sp.Msg.reply r b x cs val).body ∧ (sp.Msg.reply r b x cs val).wf⌝ ∗
          t ↦ swift.MReply.mk r b (ofCmdId x) csl vsl ∗ csl ↦* cs.map shashOf ∗ vsl ↦* val) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MReply, t ↦ v')) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem MFastAckClient.Unmarshal.wp_proof : MFastAckClient.Unmarshal.specS (hG := hG) := by
  intro t v br rd I R
  wp_start as ⟨Hctx, #Hrd, #Hlaw, Hown, Ht⟩
  iunfold ctxV at Hctx
  icases Hctx with ⟨#Hpkg, #Hpkg2, #Hpkg3, %ov, #Hov, %Hovn⟩
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) swift.byteReader.ty = true := by
    go_type_set
  try wp_auto
  rw [hts]
  wp_auto
  ihave #Hbr := bufio.bufioReadsOk br rd I $$ [$Hpkg2 $Hrd]
  ihave Hsl := slice_array b_ptr 16 (Perennial.zero_val (GoArray w8 16)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 16)).arr = List.replicate 16 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ (List.replicate 16 (W8 0)) (W64 16) ?_ $$
    [$Hpkg $Hbr $Hown $Hsl] as %n %err ⟨%data, %Hd, Hsl, Hown, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · -- an error: returned
    wp_auto
    iapply HΦ
    iexists data
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  have h16 : data.length = 16 := by
    have := herr.1 rfl; simp at hdl; have : sint.Z (W64 16) = 16 := rfl; omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :
      ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : w8,
      data = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15] := by
    match data, h16 with
    | [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15], _ =>
      exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩
  isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
    Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
  wp_auto
  rd_ld16
  isimp only [← encoding.binary.leToU32_4] at Ht
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · -- an error: returned
    wp_auto
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht1, hb1, hx1⟩ := Hx rfl
  -- the varint is the frame's own: a count `n`
  icases streamLaw_at br rd I R _ _ $$ [$Hlaw $Hown] with ⟨Hown, %Hst⟩
  obtain ⟨n, rfl, hn62⟩ := fac_v1 (hdr := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15]) rfl ht1 (Hst _ (by simp))
  obtain ⟨hn63, rfl⟩ := varint_count n hb1 hx1
  wp_auto
  wp_apply wp_slice_make2 (V := swift.SHash) (W64 n) as %sl ⟨Hsl', -⟩
  · ipureintro; word
  ihave %Hsllen := ownSlice_len $$ Hsl'
  ihave Hb1 := slice_take1 b_ptr d0 [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15]
    rfl $$ Hsl
  rw [show sint.nat (W64 n) = n by word]
  ihave HL : (∃ (k : Nat) (hs : List sp.Hash) (y : w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "Ht" ∷ t ↦ swift.MFastAckClient.mk (leToU32 [d0, d1, d2, d3]) (leToU32 [d4, d5, d6, d7])
        ⟨leToU32 [d8, d9, d10, d11], leToU32 [d12, d13, d14, d15]⟩ sl ∗
      "Hsl" ∷ sl ↦* (hs.map shashOf ++ List.replicate (n - k) (zero_val swift.SHash)) ∗
      "Hown" ∷ bufio.ownReader br rd I
        (R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten) ∗
      "Hb1" ∷ slice.mk b_ptr (W64 1) (W64 16) ↦* [y] ∗
      "%Hk" ∷ ⌜k ≤ n ∧ hs.length = k ∧ sp.cw.hashOk hs⌝ : IProp netDistGF) $$ [i bs Ht Hsl' Hown Hb1]
  · iexists 0, [], d0, _
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp [sp.cw.hashOk]
  wp_for HL
  wp_if_destruct
  · have hkn : k < n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    obtain ⟨hkn', rfl, hok⟩ := Hk
    have hlook : (hs.map shashOf ++ List.replicate (n - hs.length) (zero_val swift.SHash))[
        ((hs.length : Nat) : Int).toNat]? = some (zero_val swift.SHash) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    icases ownSlice_elem_acc ((hs.length : Nat) : Int) (zero_val swift.SHash) sl _ _ (by omega)
      hlook $$ Hsl with ⟨He, Hsl⟩
    have hbnd : 0 ≤ sint.Z (W64 (hs.length : Int)) ∧ sint.Z (W64 (hs.length : Int)) < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hsllen
      simp only [List.length_replicate] at h1
      have hn' : sint.nat (W64 (n : Int)) = n := by word
      rw [hn'] at h1
      have h3 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have : sint.Z (W64 (hs.length : Int)) = hs.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (hs.length : Int)) = hs.length := by word
    rw [show (zero_val swift.SHash) = swift.SHash.mk ⟨([] : List w8) ++
      List.replicate 32 (W8 0)⟩ from rfl] at *
    rw [show R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten = (R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten) ++ [] from (List.append_nil _).symm]
    generalize hB : R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten = B
    rd_hbyte z0
    rd_hbyte z1
    rd_hbyte z2
    rd_hbyte z3
    rd_hbyte z4
    rd_hbyte z5
    rd_hbyte z6
    rd_hbyte z7
    rd_hbyte z8
    rd_hbyte z9
    rd_hbyte z10
    rd_hbyte z11
    rd_hbyte z12
    rd_hbyte z13
    rd_hbyte z14
    rd_hbyte z15
    rd_hbyte z16
    rd_hbyte z17
    rd_hbyte z18
    rd_hbyte z19
    rd_hbyte z20
    rd_hbyte z21
    rd_hbyte z22
    rd_hbyte z23
    rd_hbyte z24
    rd_hbyte z25
    rd_hbyte z26
    rd_hbyte z27
    rd_hbyte z28
    rd_hbyte z29
    rd_hbyte z30
    rd_hbyte z31
    ihave Hsl := Hsl $$ He
    subst hB
    wp_for_post
    iframe
    iexists hs.length + 1, hs ++ [[z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31]], z31, _
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [bs]
    · iexact bs
    isplitl [Ht]
    · iexact Ht
    isplitl [Hsl]
    · iExactEq Hsl; congr 1
      rw [Int.toNat_natCast, set_slot shashOf hs _ _ (n - hs.length) (by omega)]
      simp [shashOf, List.map_append, List.append_assoc]
      rfl
    isplitl [Hown]
    · iExactEq Hown; congr 1
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_assoc,
        List.nil_append, List.append_nil, List.singleton_append, List.cons_append]
    isplitl [Hb1]
    · iexact Hb1
    ipureintro
    refine ⟨by omega, by simp, ?_⟩
    intro h hh
    rcases List.mem_append.1 hh with h' | h'
    · exact hok h h'
    · simp at h'; subst h'; rfl
  · -- the loop's end: `n` hashes
    obtain ⟨hkn', hlk, hok⟩ := Hk
    have hkn : k = n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    subst hkn hlk
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    ileft
    isplitr
    · ipureintro; rfl
    iexists leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7],
      ⟨leToU32 [d8, d9, d10, d11], leToU32 [d12, d13, d14, d15]⟩, hs, sl
    isplitr
    · ipureintro
      refine ⟨?_, ⟨hn62, hok⟩⟩
      simp only [sp.Msg.body, sp.le32, sp.encCmdId, sp.encHashes]
      rw [leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl]
      simp
    isplitl [Ht]
    · iExactEq Ht; rfl
    iExactEq Hsl; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem MReply.Unmarshal.wp_proof : MReply.Unmarshal.specS (hG := hG) := by
  intro t v br rd I R
  wp_start as ⟨Hctx, #Hrd, #Hlaw, Hown, Ht⟩
  iunfold ctxV at Hctx
  icases Hctx with ⟨#Hpkg, #Hpkg2, #Hpkg3, %ov, #Hov, %Hovn⟩
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) swift.byteReader.ty = true := by
    go_type_set
  try wp_auto
  rw [hts]
  wp_auto
  ihave #Hbr := bufio.bufioReadsOk br rd I $$ [$Hpkg2 $Hrd]
  ihave Hsl := slice_array b_ptr 16 (Perennial.zero_val (GoArray w8 16)) (by decide) $$ b
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 16 - W64 0 = W64 16 from rfl]
  rw [show (Perennial.zero_val (GoArray w8 16)).arr = List.replicate 16 (W8 0) from rfl]
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ (List.replicate 16 (W8 0)) (W64 16) ?_ $$
    [$Hpkg $Hbr $Hown $Hsl] as %n %err ⟨%data, %Hd, Hsl, Hown, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · -- an error: returned
    wp_auto
    iapply HΦ
    iexists data
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  have h16 : data.length = 16 := by
    have := herr.1 rfl; simp at hdl; have : sint.Z (W64 16) = 16 := rfl; omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :
      ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : w8,
      data = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15] := by
    match data, h16 with
    | [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15], _ =>
      exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩
  isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
    Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hsl
  wp_auto
  rd_ld16
  isimp only [← encoding.binary.leToU32_4] at Ht
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · -- an error: returned
    wp_auto
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht1, hb1, hx1⟩ := Hx rfl
  -- the varint is the frame's own: a count `n`
  icases streamLaw_at br rd I R _ _ $$ [$Hlaw $Hown] with ⟨Hown, %Hst⟩
  obtain ⟨n, rfl, hn62, hnpos⟩ := rep_v1 (hdr := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15]) rfl ht1 (Hst _ (by simp))
  obtain ⟨hn63, rfl⟩ := varint_count n hb1 hx1
  wp_auto
  wp_apply wp_slice_make2 (V := swift.SHash) (W64 n) as %sl ⟨Hsl', -⟩
  · ipureintro; word
  ihave %Hsllen := ownSlice_len $$ Hsl'
  ihave Hb1 := slice_take1 b_ptr d0 [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15]
    rfl $$ Hsl
  rw [show sint.nat (W64 n) = n by word]
  ihave HL : (∃ (k : Nat) (hs : List sp.Hash) (y : w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "Ht" ∷ t ↦ swift.MReply.mk (leToU32 [d0, d1, d2, d3]) (leToU32 [d4, d5, d6, d7])
        ⟨leToU32 [d8, d9, d10, d11], leToU32 [d12, d13, d14, d15]⟩ sl v.Rep' ∗
      "Hsl" ∷ sl ↦* (hs.map shashOf ++ List.replicate (n - k) (zero_val swift.SHash)) ∗
      "Hown" ∷ bufio.ownReader br rd I
        (R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten) ∗
      "Hb1" ∷ slice.mk b_ptr (W64 1) (W64 16) ↦* [y] ∗
      "%Hk" ∷ ⌜k ≤ n ∧ hs.length = k ∧ sp.cw.hashOk hs ∧
        (k = 0 ∨ bsv = slice.mk b_ptr (W64 1) (W64 16))⌝ : IProp netDistGF) $$ [i bs Ht Hsl' Hown Hb1]
  · iexists 0, [], d0, _
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp [sp.cw.hashOk]
  wp_for HL
  wp_if_destruct
  · have hkn : k < n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    obtain ⟨hkn', rfl, hok, -⟩ := Hk
    have hlook : (hs.map shashOf ++ List.replicate (n - hs.length) (zero_val swift.SHash))[
        ((hs.length : Nat) : Int).toNat]? = some (zero_val swift.SHash) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    icases ownSlice_elem_acc ((hs.length : Nat) : Int) (zero_val swift.SHash) sl _ _ (by omega)
      hlook $$ Hsl with ⟨He, Hsl⟩
    have hbnd : 0 ≤ sint.Z (W64 (hs.length : Int)) ∧ sint.Z (W64 (hs.length : Int)) < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hsllen
      simp only [List.length_replicate] at h1
      have hn' : sint.nat (W64 (n : Int)) = n := by word
      rw [hn'] at h1
      have h3 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have : sint.Z (W64 (hs.length : Int)) = hs.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (hs.length : Int)) = hs.length := by word
    rw [show (zero_val swift.SHash) = swift.SHash.mk ⟨([] : List w8) ++
      List.replicate 32 (W8 0)⟩ from rfl] at *
    rw [show R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten = (R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten) ++ [] from (List.append_nil _).symm]
    generalize hB : R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
          d13, d14, d15] ++ sp.varintLen n ++ hs.flatten = B
    rd_hbyte z0
    rd_hbyte z1
    rd_hbyte z2
    rd_hbyte z3
    rd_hbyte z4
    rd_hbyte z5
    rd_hbyte z6
    rd_hbyte z7
    rd_hbyte z8
    rd_hbyte z9
    rd_hbyte z10
    rd_hbyte z11
    rd_hbyte z12
    rd_hbyte z13
    rd_hbyte z14
    rd_hbyte z15
    rd_hbyte z16
    rd_hbyte z17
    rd_hbyte z18
    rd_hbyte z19
    rd_hbyte z20
    rd_hbyte z21
    rd_hbyte z22
    rd_hbyte z23
    rd_hbyte z24
    rd_hbyte z25
    rd_hbyte z26
    rd_hbyte z27
    rd_hbyte z28
    rd_hbyte z29
    rd_hbyte z30
    rd_hbyte z31
    ihave Hsl := Hsl $$ He
    subst hB
    wp_for_post
    iframe
    iexists hs.length + 1, hs ++ [[z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31]], z31, _
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [bs]
    · iexact bs
    isplitl [Ht]
    · iexact Ht
    isplitl [Hsl]
    · iExactEq Hsl; congr 1
      rw [Int.toNat_natCast, set_slot shashOf hs _ _ (n - hs.length) (by omega)]
      simp [shashOf, List.map_append, List.append_assoc]
      rfl
    isplitl [Hown]
    · iExactEq Hown; congr 1
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_assoc,
        List.nil_append, List.append_nil, List.singleton_append, List.cons_append]
    isplitl [Hb1]
    · iexact Hb1
    ipureintro
    refine ⟨by omega, by simp, ?_, Or.inr rfl⟩
    intro h hh
    rcases List.mem_append.1 hh with h' | h'
    · exact hok h h'
    · simp at h'; subst h'; rfl
  · -- the hashes' end: `n ≥ 1` hashes, then the result's count and bytes
    obtain ⟨hkn', hlk, hok, hbs⟩ := Hk
    have hkn : k = n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    subst hkn hlk
    rcases hbs with h0 | rfl
    · omega
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at *
    wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x2 %err ⟨%vd2, Hown, %Hx2⟩
    · ipureintro; exact Hovn
    rcases err with e | _
    · -- an error: returned
      wp_auto
      iapply HΦ
      iexists _
      isplitl [Hown]
      · iExactEq Hown; simp only [List.append_assoc]; rfl
      iright
      isplitr
      · ipureintro; intro h; cases h
      iexists _
      iexact Ht
    obtain ⟨ht2, hb2, hx2⟩ := Hx2 rfl
    icases streamLaw_at br rd I R _ _ $$ [$Hlaw $Hown] with ⟨Hown, %Hst2⟩
    obtain ⟨m, rfl, hm62⟩ := rep_v2 (hdr := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15]) rfl hok ht2 (Hst2 _ (by simp))
    obtain ⟨hm63, rfl⟩ := varint_count m hb2 hx2
    wp_auto
    wp_apply wp_slice_make2 (V := w8) (W64 m) as %rsl ⟨Hrsl, -⟩
    · ipureintro; word
    ihave %Hrsllen := ownSlice_len $$ Hrsl
    rw [show sint.nat (W64 m) = m by word] at *
    isimp only at Ht
    ihave HL2 : (∃ (k : Nat) (vs : List w8) (y : w8),
        "i" ∷ i_ptr ↦ W64 k ∗
        "Ht" ∷ t ↦ swift.MReply.mk (leToU32 [d0, d1, d2, d3]) (leToU32 [d4, d5, d6, d7])
          ⟨leToU32 [d8, d9, d10, d11], leToU32 [d12, d13, d14, d15]⟩ sl rsl ∗
        "Hrsl" ∷ rsl ↦* (vs ++ List.replicate (m - k) (W8 0)) ∗
        "Hown" ∷ bufio.ownReader br rd I
          (R ++ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15] ++ sp.varintLen hs.length ++ hs.flatten ++
            sp.varintLen m ++ vs) ∗
        "Hb1" ∷ slice.mk b_ptr (W64 1) (W64 16) ↦* [y] ∗
        "%Hk" ∷ ⌜k ≤ m ∧ vs.length = k⌝ : IProp netDistGF) $$ [i Ht Hrsl Hown Hb1]
    · iexists 0, [], _
      simp only [List.nil_append, Nat.sub_zero, List.append_nil]
      iframe
      ipureintro; simp
    wp_for HL2
    wp_if_destruct
    · have hkm : k < m := by
        have h1 : sint.Z (W64 (k : Int)) = k := by word
        have h2 : sint.Z (W64 (m : Int)) = m := by word
        omega
      obtain ⟨hkm', rfl⟩ := Hk
      wp_apply bufio.wp_ReadAtLeast _ _ _ _ [_] (W64 1) (by simp) $$
        [$Hpkg $Hbr $Hown $Hb1] as %n0 %err ⟨%data0, %Hd0, Hb1, Hown, #He0⟩
      obtain ⟨-, hdl0, herr0⟩ := Hd0
      rcases err with e0 | _
      · wp_auto
        wp_for_post
        iapply HΦ
        iexists _
        isplitl [Hown]
        · iExactEq Hown; simp only [List.append_assoc]; rfl
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists _
        iexact Ht
      obtain ⟨z, rfl⟩ := data_one hdl0 (herr0.1 rfl)
      try isimp only [List.length_cons, List.length_nil, List.drop_one, List.drop_nil, List.append_nil,
        List.tail_cons, Nat.reduceAdd] at Hb1
      try wp_auto
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hb1] as Hb1
      · iframe Hb1; ipureintro; rfl
      have hbnd2 : 0 ≤ sint.Z (W64 (vs.length : Int)) ∧ sint.Z (W64 (vs.length : Int)) < sint.Z rsl.len := by
        obtain ⟨h1, h2⟩ := Hrsllen
        simp only [List.length_replicate] at h1
        have h3 : sint.nat rsl.len = (sint.Z rsl.len).toNat := rfl
        have : sint.Z (W64 (vs.length : Int)) = vs.length := by word
        rw [this]; omega
      rw [ite_cond_eq_true _ _ (eq_true hbnd2)]
      try wp_auto
      wp_apply wp_store_slice_index _ _ _ z $$ [Hrsl] as Hrsl
      · iframe Hrsl; ipureintro
        have : sint.Z (W64 (vs.length : Int)) = vs.length := by word
        rw [this]; simp; omega
      wp_for_post
      iframe
      iexists vs.length + 1, vs ++ [z], z
      isplitl [i]
      · iExactEq i; congr 1; word
      isplitl [Ht]
      · iexact Ht
      isplitl [Hrsl]
      · iExactEq Hrsl; congr 1
        have : sint.Z (W64 (vs.length : Int)) = vs.length := by word
        rw [this, Int.toNat_natCast, List.set_append_right _ _ (by simp)]
        simp only [Nat.sub_self, List.append_assoc, List.length_append, List.length_singleton]
        obtain ⟨q, hq⟩ : ∃ q, m - vs.length = q + 1 := ⟨m - vs.length - 1, by omega⟩
        rw [hq, List.replicate_succ, List.set_cons_zero, show m - (vs.length + 1) = q by omega]
        rfl
      isplitl [Hown]
      · iExactEq Hown; congr 1; simp only [List.append_assoc]
      isplitl [Hb1]
      · iexact Hb1
      ipureintro
      simp; omega
    · -- the result's end: return
      obtain ⟨hkm', rfl⟩ := Hk
      have hkm : vs.length = m := by
        have h1 : sint.Z (W64 (vs.length : Int)) = vs.length := by word
        have h2 : sint.Z (W64 (m : Int)) = m := by word
        omega
      subst hkm
      iapply HΦ
      iexists _
      isplitl [Hown]
      · iExactEq Hown; simp only [List.append_assoc]; rfl
      ileft
      isplitr
      · ipureintro; rfl
      iexists leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7],
        ⟨leToU32 [d8, d9, d10, d11], leToU32 [d12, d13, d14, d15]⟩, hs, vs, sl, rsl
      isplitr
      · ipureintro
        refine ⟨?_, ⟨hn62, hok⟩, hm62⟩
        simp only [sp.Msg.body, sp.le32, sp.encCmdId, sp.encHashes, sp.encBytes]
        rw [leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl]
        simp
      isplitl [Ht]
      · iExactEq Ht; rfl
      isplitl [Hsl]
      · iExactEq Hsl; simp
      iExactEq Hrsl; simp


/-! ## The entries -/

omit [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
theorem wp_New_MFastAckClient' (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MFastAckClient.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l);
        l ↦ (zero_val swift.MFastAckClient) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

omit [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
theorem wp_New_MReply' (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MReply.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l);
        l ↦ (zero_val swift.MReply) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem unmarshalOk_fastAckClient (l : Loc) (v : swift.MFastAckClient) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 10) (swift.msgRep (W8 10))
      (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  wp_apply MFastAckClient.Unmarshal.wp_proof l v br rd I R $$ [$Hctx $Hrd $Hlaw $Hown $Hl]
    as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %r, %b, %x, %cs, %csl, %Hd, Hl, Hcs⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .fastAckClient r b x cs
    isplitr
    · ipureintro; rw [Hd.1]; exact sp.decodes_of_body rfl Hd.2
    unfold swift.msgRep swift.msgRepM
    iexists l, csl
    iframe
    ipureintro; rfl
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem unmarshalOk_reply (l : Loc) (v : swift.MReply) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 15) (swift.msgRep (W8 15))
      (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  ihave #Hlaw' := streamLaw_mono br rd I R _ _ nextOk_reply $$ Hlaw
  wp_apply MReply.Unmarshal.wp_proof l v br rd I R $$ [$Hctx $Hrd $Hlaw' $Hown $Hl]
    as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %r, %b, %x, %cs, %val, %csl, %vsl, %Hd, Hl, Hcs, Hvs⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .reply r b x cs val
    isplitr
    · ipureintro; rw [Hd.1]; exact sp.decodes_of_body rfl Hd.2
    unfold swift.msgRep swift.msgRepM
    iexists l, csl, vsl
    iframe
    ipureintro; rfl
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem newOk_fastAckClient (o : Loc) :
    ctxV ⊢ sp.newOk (W8 10) (swift.msgRep (W8 10))
      (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #o) := by
  apply newOk_of _ _ _ o ctxV (fun l => iprop(l ↦ (zero_val swift.MFastAckClient)))
  · iintro %Φ - HΦ
    iapply wp_New_MFastAckClient' o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_fastAckClient l _

theorem newOk_reply (o : Loc) :
    ctxV ⊢ sp.newOk (W8 15) (swift.msgRep (W8 15))
      (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #o) := by
  apply newOk_of _ _ _ o ctxV (fun l => iprop(l ↦ (zero_val swift.MReply)))
  · iintro %Φ - HΦ
    iapply wp_New_MReply' o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_reply l _

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
