/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableAcks.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*MAcks).Unmarshal` (13) on a stream whose next bytes are an `MAcks`'s body: the fast acks
by the element decoder (`MFastAck.Unmarshal.specS`, each under its law `fastAckNext`,
`acks_elem`), the slow acks 16 bytes each; the counts are the message's own (`acks_v1`,
`acks_v2`). The fast acks' slices are made read-only (`fastAckRepr`), as the batcher and the
handlers take them.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableAcksPure

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

/-- A slow ack as the Go struct. -/
def slowV (s : sp.SlowAck) : swift.MLightSlowAck := ⟨s.rep, s.bal, ofCmdId s.id⟩

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- `(*MAcks).Unmarshal(br)`: without an error, the bytes read are the body of a well-formed
`.acks fs ss`, which `t` represents (`swift.msgRepM`'s shape). -/
abbrev MAcks.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MAcks) (br : Loc) (rd : GoInterface) (I : List w8 → IProp netDistGF)
    (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 13)) ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MAcks.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (fs : List sp.FastAck) (ss : List sp.SlowAck) (fsl ssl : GoSlice)
          (fps : List (swift.MFastAck × sp.FastAck)),
          ⌜data = (sp.Msg.acks fs ss).body ∧ (sp.Msg.acks fs ss).wf ∧ fps.map Prod.snd = fs⌝ ∗
          t ↦ swift.MAcks.mk fsl ssl ∗ fsl ↦* fps.map Prod.fst ∗ ssl ↦* ss.map slowV ∗
          [∗list] p ∈ fps, swift.fastAckRepr p.1 p.2) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MAcks, t ↦ v')) }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [io.Assumptions] [io.ExtraAssumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [swift.Assumptions] [io.Assumptions] [io.ExtraAssumptions] [errors.Assumptions]
  [bufio.Assumptions] in
/-- The first 4 bytes of a 10-byte buffer, as the slice `b[:4]`. -/
theorem slice_take4 (p : Loc) (xs : List w8) (hl : xs.length = 10) :
    (slice.mk p (W64 10) (W64 10) ↦* xs : IProp netDistGF) ⊢
      slice.mk p (W64 4) (W64 10) ↦* xs.take 4 := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := H; simp [slice.nil] at h1
  iright
  simp only
  icases (array_split (V := w8) (W64 4) p (DFrac.own 1) _ _ (by word)).1 $$ H
    with ⟨H, -⟩
  isplitl [H]
  · iExactEq H; rfl
  · ipureintro; simp [hl]; decide

omit go_gctx hG sem [swift.Assumptions] [io.Assumptions] [io.ExtraAssumptions] [errors.Assumptions]
  [bufio.Assumptions] in
theorem acks_body (fs : List sp.FastAck) (ss : List sp.SlowAck) :
    (sp.Msg.acks fs ss).body = sp.varintLen fs.length ++ (fs.map sp.FastAck.enc).flatten ++
      sp.varintLen ss.length ++ (ss.map sp.SlowAck.enc).flatten := rfl

theorem four_of {data : List w8} {u : List w8} (hl : data.length ≤ u.length) (hu : u.length = 4)
    (he : sint.Z (W64 4) ≤ (data.length : Int)) : ∃ a b c d, data = [a, b, c, d] := by
  have : sint.Z (W64 4) = 4 := rfl
  match data with
  | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
  | [] | [_] | [_, _] | [_, _, _] => rw [this] at he; simp at he
  | _ :: _ :: _ :: _ :: _ :: _ => simp at hl; omega

set_option hygiene false in
/-- `ReadAtLeast(wire, bs, 4)` into `b[:4]` (an error returns), then the 4 bytes' loads. -/
macro "rd4" a:ident b:ident c:ident d:ident : tactic => `(tactic| (
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
    show W64 10 - W64 0 = W64 10 from rfl]
  try wp_auto
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ [_, _, _, _] (W64 4) (by simp; decide) $$
    [Hown Hb4] as %n0 %err ⟨%data0, %Hd0, Hb4, Hown, #He0⟩
  · iframe Hown Hb4 Hbr
  obtain ⟨-, hdl0, herr0⟩ := Hd0
  rcases err with e0 | _
  · subst hB
    wp_auto
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
  obtain ⟨$a, $b, $c, $d, rfl⟩ := four_of hdl0 rfl (herr0.1 rfl)
  try isimp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero,
    List.drop_nil, List.append_nil, Nat.reduceAdd] at Hb4
  try rw [List.append_assoc B _ [$a, $b, $c, $d]]
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem MAcks.Unmarshal.wp_proof (wp_FA : MFastAck.Unmarshal.specS (hG := hG)) :
    MAcks.Unmarshal.specS (hG := hG) := by
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
  -- the fast acks' count
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht1, hb1, hx1⟩ := Hx rfl
  icases streamLaw_use br rd I R vd1 _ $$ [$Hlaw $Hown] with ⟨Hown, %Hn1⟩
  obtain ⟨n, rfl, hn62⟩ := acks_v1 ht1 Hn1
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n hb1 hx1
  try wp_auto
  wp_apply wp_slice_make2 (V := swift.MFastAck) (W64 n) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  ihave %Hsllen := ownSlice_len $$ Hsl
  rw [show sint.nat (W64 n) = n by word]
  try wp_auto
  ihave HL : (∃ (k : Nat) (fps : List (swift.MFastAck × sp.FastAck)),
      "i" ∷ i_ptr ↦ W64 k ∗
      "Ht" ∷ t ↦ swift.MAcks.mk sl v.LightSlowAcks' ∗
      "Hsl" ∷ sl ↦* (fps.map Prod.fst ++ List.replicate (n - k) (zero_val swift.MFastAck)) ∗
      "Hreps" ∷ ([∗list] p ∈ fps, swift.fastAckRepr p.1 p.2) ∗
      "Hown" ∷ bufio.ownReader br rd I
        (R ++ sp.varintLen n ++ ((fps.map Prod.snd).map sp.FastAck.enc).flatten) ∗
      "%Hk" ∷ ⌜k ≤ n ∧ fps.length = k ∧ ∀ p ∈ fps, p.2.wf⌝ : IProp netDistGF) $$ [i Ht Hsl Hown]
  · iexists 0, []
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · -- the next fast ack
    have hkn : k < n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    obtain ⟨hkn', rfl, hok⟩ := Hk
    have hlook : (fps.map Prod.fst ++ List.replicate (n - fps.length) (zero_val swift.MFastAck))[
        ((fps.length : Nat) : Int).toNat]? = some (zero_val swift.MFastAck) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    have hbnd : 0 ≤ sint.Z (W64 (fps.length : Int)) ∧
        sint.Z (W64 (fps.length : Int)) < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hsllen
      have hn' : sint.nat (W64 (n : Int)) = n := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have : sint.Z (W64 (fps.length : Int)) = fps.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (fps.length : Int)) = fps.length := by word
    rw [ite_cond_eq_true _ _ (eq_true hbnd)]
    rw [hk64]
    icases ownSlice_elem_acc ((fps.length : Nat) : Int) (zero_val swift.MFastAck) sl _ _ (by omega)
      hlook $$ Hsl with ⟨He, Hsl⟩
    have hwf : ∀ f ∈ fps.map Prod.snd, f.wf := by
      intro f hf; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hf; exact hok p hp
    have hel : ∀ d, sp.nextOk (W8 13)
        ((sp.varintLen n ++ ((fps.map Prod.snd).map sp.FastAck.enc).flatten) ++ d) →
        fastAckNext d :=
      fun d hd => acks_elem (prev := fps.map Prod.snd) hwf (by simp; omega) hd
    ihave #Hlaw1 := streamLaw_shift br rd I R
      (sp.varintLen n ++ ((fps.map Prod.snd).map sp.FastAck.enc).flatten) _ $$ Hlaw
    ihave #Hlaw' := streamLaw_mono br rd I _ _ fastAckNext hel $$ Hlaw1
    wp_apply wp_FA _ _ br rd I _ $$ [$Hctx $Hrd $Hlaw' $He Hown]
      as %err ⟨%data, Hown, Hres⟩
    · iExactEq Hown; simp [List.append_assoc]
    icases Hres with (⟨%Hen, %f, %dsl, %csl, ⟨%Hd, %Hwf⟩, He, Hdsl, Hcsl⟩ | ⟨%Hen, %v', He⟩)
    · subst Hen Hd
      imod ownSlice_persist $$ Hdsl with #Hdsl
      imod ownSlice_persist $$ Hcsl with #Hcsl
      ihave Hsl := Hsl $$ He
      wp_auto
      wp_for_post
      iframe
      iexists fps.length + 1, fps ++ [(swift.MFastAck.mk f.rep f.bal (ofCmdId f.id) dsl csl f.seqnum, f)]
      isplitl [i]
      · iExactEq i; congr 1; word
      isplitl [Ht]
      · iexact Ht
      isplitl [Hsl]
      · iExactEq Hsl; congr 1
        rw [Int.toNat_natCast, swift.rd.set_slot Prod.fst fps _ _ (n - fps.length) (by omega)]
        simp [List.map_append, List.append_assoc, show n - (fps.length + 1) = n - fps.length - 1 by omega]
      isplitl [Hreps]
      · iapply (BigSepL.bigSepL_snoc).2
        iframe Hreps
        unfold swift.fastAckRepr
        iframe Hdsl Hcsl
        ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitl [Hown]
      · iExactEq Hown; congr 1
        simp [List.map_append, List.flatten_append, List.append_assoc]
      ipureintro
      refine ⟨by omega, by simp, ?_⟩
      intro p hp
      rcases List.mem_append.1 hp with h' | h'
      · exact hok p h'
      · simp at h'; subst h'; exact Hwf
    · -- an element's error: returned
      rcases err with eo | _
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
  · -- the slow acks
    obtain ⟨hkn', hlk, hok⟩ := Hk
    have hkn : k = n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    subst hkn
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at *
    wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x2 %err ⟨%vd2, Hown, %Hx2⟩
    · ipureintro; exact Hovn
    rcases err with e | _
    · wp_auto
      iapply HΦ
      iexists (sp.varintLen k ++ ((fps.map Prod.snd).map sp.FastAck.enc).flatten ++ vd2)
      isplitl [Hown]
      · iExactEq Hown; simp only [List.append_assoc]
      iright
      isplitr
      · ipureintro; intro h; cases h
      iexists _
      iexact Ht
    obtain ⟨ht2, hb2, hx2⟩ := Hx2 rfl
    subst hlk
    icases streamLaw_use br rd I R (sp.varintLen fps.length ++
      ((fps.map Prod.snd).map sp.FastAck.enc).flatten ++ vd2) _ $$ [$Hlaw Hown] with ⟨Hown, %Hn2⟩
    · iExactEq Hown; simp only [List.append_assoc]
    have hwf : ∀ f ∈ fps.map Prod.snd, f.wf := by
      intro f hf; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hf; exact hok p hp
    obtain ⟨m, rfl, hm62, -⟩ := acks_v2 (fs := fps.map Prod.snd) (n := fps.length) ht2
      hwf (by simp) Hn2
    obtain ⟨-, rfl⟩ := swift.rd.varint_count m hb2 hx2
    try wp_auto
    wp_apply wp_slice_make2 (V := swift.MLightSlowAck) (W64 m) as %sl2 ⟨Hsl2, -⟩
    · ipureintro; word
    ihave %Hsl2len := ownSlice_len $$ Hsl2
    rw [show sint.nat (W64 m) = m by word]
    try wp_auto
    ihave Hb := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
    rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl] at *
    ihave Hb4 := slice_take4 b_ptr _ (by simp) $$ Hb
    ihave HL2 : (∃ (j : Nat) (ss : List sp.SlowAck) (y0 y1 y2 y3 : w8) (bsv : GoSlice),
        "i" ∷ i_ptr ↦ W64 j ∗ "bs" ∷ bs_ptr ↦ bsv ∗
        "Ht" ∷ t ↦ swift.MAcks.mk sl sl2 ∗
        "Hsl2" ∷ sl2 ↦* (ss.map slowV ++ List.replicate (m - j) (zero_val swift.MLightSlowAck)) ∗
        "Hown" ∷ bufio.ownReader br rd I (R ++ ((sp.varintLen fps.length ++
          (List.map sp.FastAck.enc (List.map Prod.snd fps)).flatten ++ sp.varintLen m) ++
          (ss.map sp.SlowAck.enc).flatten)) ∗
        "Hb4" ∷ slice.mk b_ptr (W64 4) (W64 10) ↦* [y0, y1, y2, y3] ∗
        "%Hj" ∷ ⌜j ≤ m ∧ ss.length = j⌝ : IProp netDistGF) $$ [i bs Ht Hsl2 Hown Hb4]
    · iexists 0, [], W8 0, W8 0, W8 0, W8 0, _
      simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
      iframe
      ipureintro; simp
    wp_for HL2
    wp_if_destruct
    · obtain ⟨hjm', rfl⟩ := Hj
      have hjm : ss.length < m := by
        have h1 : sint.Z (W64 (ss.length : Int)) = ss.length := by word
        have h2 : sint.Z (W64 (m : Int)) = m := by word
        omega
      have hlook : (ss.map slowV ++ List.replicate (m - ss.length) (zero_val swift.MLightSlowAck))[
          ((ss.length : Nat) : Int).toNat]? = some (zero_val swift.MLightSlowAck) := by
        rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
        simp only [List.length_map, Nat.sub_self]
        rw [List.getElem?_replicate]; simp; omega
      have hbnd : 0 ≤ sint.Z (W64 (ss.length : Int)) ∧
          sint.Z (W64 (ss.length : Int)) < sint.Z sl2.len := by
        obtain ⟨h1, h2⟩ := Hsl2len
        have hm' : sint.nat (W64 (m : Int)) = m := by word
        simp only [List.length_replicate, hm'] at h1
        have h3 : sint.nat sl2.len = (sint.Z sl2.len).toNat := rfl
        have : sint.Z (W64 (ss.length : Int)) = ss.length := by word
        rw [this]; omega
      have hk64 : sint.Z (W64 (ss.length : Int)) = ss.length := by word
      icases ownSlice_elem_acc ((ss.length : Nat) : Int) (zero_val swift.MLightSlowAck) sl2 _ _
        (by omega) hlook $$ Hsl2 with ⟨He, Hsl2⟩
      rw [show R ++ ((sp.varintLen fps.length ++
          (List.map sp.FastAck.enc (List.map Prod.snd fps)).flatten ++ sp.varintLen m) ++
          (ss.map sp.SlowAck.enc).flatten) = (R ++ ((sp.varintLen fps.length ++
          (List.map sp.FastAck.enc (List.map Prod.snd fps)).flatten ++ sp.varintLen m) ++
          (ss.map sp.SlowAck.enc).flatten)) ++ [] from (List.append_nil _).symm]
      generalize hB : R ++ ((sp.varintLen fps.length ++
          (List.map sp.FastAck.enc (List.map Prod.snd fps)).flatten ++ sp.varintLen m) ++
          (ss.map sp.SlowAck.enc).flatten) = B
      rd4 a0 a1 a2 a3
      rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
      wp_auto
      rd4 b0 b1 b2 b3
      rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
      wp_auto
      rd4 c0 c1 c2 c3
      rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
      wp_auto
      rd4 d0 d1 d2 d3
      rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
      wp_auto
      let sa : sp.SlowAck := ⟨leToU32 [a0, a1, a2, a3], leToU32 [b0, b1, b2, b3],
        ⟨leToU32 [c0, c1, c2, c3], leToU32 [d0, d1, d2, d3]⟩⟩
      ihave Hsl2 := Hsl2 $$ %(slowV sa) [He]
      · iExactEq He; simp only [slowV, sa, ofCmdId, encoding.binary.leToU32_4]
      subst hB
      wp_for_post
      iframe
      iexists ss.length + 1, ss ++ [sa], d0, d1, d2, d3, _
      isplitl [i]
      · iExactEq i; congr 1; word
      isplitl [bs]
      · iexact bs
      isplitl [Ht]
      · iexact Ht
      isplitl [Hsl2]
      · iExactEq Hsl2; congr 1
        rw [Int.toNat_natCast, swift.rd.set_slot slowV ss _ _ (m - ss.length) (by omega)]
        simp [List.map_append, List.append_assoc, show m - (ss.length + 1) = m - ss.length - 1 by omega]
      isplitl [Hown]
      · iExactEq Hown; congr 1
        simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
          List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, List.nil_append]
        simp only [sa, sp.SlowAck.enc, sp.le32, sp.encCmdId]
        rw [leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl]
        simp
      isplitl [Hb4]
      · iexact Hb4
      ipureintro
      simp; omega
    · -- the end: the message
      obtain ⟨hjm', rfl⟩ := Hj
      have hjm : ss.length = m := by
        have h1 : sint.Z (W64 (ss.length : Int)) = ss.length := by word
        have h2 : sint.Z (W64 (m : Int)) = m := by word
        omega
      subst hjm
      iapply HΦ
      iexists (sp.Msg.acks (fps.map Prod.snd) ss).body
      isplitl [Hown]
      · iExactEq Hown; rw [acks_body]; simp only [List.length_map, List.append_assoc]
      ileft
      isplitr
      · ipureintro; rfl
      iexists fps.map Prod.snd, ss, sl, sl2, fps
      isplitr
      · ipureintro
        exact ⟨rfl, ⟨⟨by simpa using hn62, hwf⟩, hm62⟩, rfl⟩
      iframe Ht Hsl Hreps
      iExactEq Hsl2; simp

end proofs

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

theorem fastAck_of_next {d : List w8} (h : sp.nextOk (W8 9) d) : fastAckNext d := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  exact ⟨_, w, hw, hp⟩

section entries
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [io.Assumptions] [io.ExtraAssumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

theorem unmarshalOk_acks (wp_FA : MFastAck.Unmarshal.specS (hG := hG)) (l : Loc)
    (v : swift.MAcks) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 13) (swift.msgRep (W8 13))
      (interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  wp_apply MAcks.Unmarshal.wp_proof wp_FA l v br rd I R $$ [$Hctx $Hrd $Hlaw $Hown $Hl]
    as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %fs, %ss, %fsl, %ssl, %fps, ⟨%Hd, %Hwf, %Hf⟩, Ht, Hfsl, Hssl, Hreps⟩ |
    ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .acks fs ss
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hwf
    unfold swift.msgRep swift.msgRepM
    iexists l, fsl, ssl, fps, ss.map (fun s => (slowV s, s))
    isplitr
    · ipureintro
      refine ⟨rfl, Hf, by simp [Function.comp_def], ?_⟩
      intro p hp
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨rfl, rfl, rfl⟩
    iframe Ht Hfsl Hreps
    iExactEq Hssl; simp [Function.comp_def]
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem unmarshalOk_fastAck (wp_FA : MFastAck.Unmarshal.specS (hG := hG)) (l : Loc)
    (v : swift.MFastAck) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 9) (swift.msgRep (W8 9))
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  ihave #Hlaw' := streamLaw_mono br rd I R _ fastAckNext (fun d hd => fastAck_of_next hd) $$ Hlaw
  iapply Iris.wp_fupd
  wp_apply wp_FA l v br rd I R $$ [$Hctx $Hrd $Hlaw' $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %f, %dsl, %csl, ⟨%Hd, %Hwf⟩, Ht, Hdsl, Hcsl⟩ | ⟨%He, -⟩)
  · imod ownSlice_persist $$ Hdsl with #Hdsl
    imod ownSlice_persist $$ Hcsl with #Hcsl
    imodintro
    iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .fastAck f
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hwf
    unfold swift.msgRep swift.msgRepM
    iexists l, _
    iframe Ht
    isplitr
    · ipureintro; rfl
    unfold swift.fastAckRepr
    iframe Hdsl Hcsl
    ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  · imodintro
    iapply HΦ $$ Hown
    iright
    ipureintro; exact He

theorem wp_New_MAcks (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MAcks.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #l);
        l ↦ (zero_val swift.MAcks) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem newOk_acks (wp_FA : MFastAck.Unmarshal.specS (hG := hG)) (o : Loc) :
    ctxV ⊢ sp.newOk (W8 13) (swift.msgRep (W8 13))
      (interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #o) := by
  apply newOk_of _ _ _ o ctxV (fun l => iprop(l ↦ (zero_val swift.MAcks)))
  · iintro %Φ - HΦ
    iapply wp_New_MAcks o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_acks wp_FA l _

/-- The persistent facts `MFastAck`'s entry uses: `ctxV`, the package, the pool's switch. -/
def ctxFA (v : Bool) : IProp netDistGF :=
  iprop(ctxV ∗ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
    typedPointsto (globalAddr swift.useFastAckPool) v DFrac.discard)

instance ctxFA_persistent (v : Bool) : Persistent (ctxFA (hG := hG) v) := by
  unfold ctxFA; infer_instance

theorem wp_New_MFastAck (wp_newFA : newFastAck.specP' (hG := hG)) (v : Bool) (o : Loc) :
    {{ ctxFA v }}
      (App (Val (o @!! go.GoType.PointerType swift.MFastAck.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l);
        ∃ fa : swift.MFastAck, l ↦ fa }} := by
  wp_start as #Hctx
  iunfold ctxFA at Hctx
  icases Hctx with ⟨-, #Hpkg, #Hv⟩
  wp_auto
  wp_apply wp_newFA v $$ [$Hpkg $Hv] as %l Hl
  try wp_auto
  iapply HΦ $$ Hl

theorem newOk_fastAck (wp_FA : MFastAck.Unmarshal.specS (hG := hG))
    (wp_newFA : newFastAck.specP' (hG := hG)) (v : Bool) (o : Loc) :
    ctxFA v ⊢ sp.newOk (W8 9) (swift.msgRep (W8 9))
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #o) := by
  apply newOk_of _ _ _ o (ctxFA v) (fun l => iprop(∃ fa : swift.MFastAck, l ↦ fa))
    (wp_New_MFastAck wp_newFA v o)
  intro l
  iintro ⟨#Hctx, %fa, Hl⟩
  iunfold ctxFA at Hctx
  icases Hctx with ⟨#HV, -, -⟩
  iapply unmarshalOk_fastAck wp_FA l fa $$ [$HV $Hl]

end entries

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
