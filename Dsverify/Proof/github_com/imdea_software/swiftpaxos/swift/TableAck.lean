/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableAck.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*Ack).Unmarshal` (an `MOptAcks` element) on a `*bufio.Reader` whose next bytes are an `Ack`'s
encoding (`swift.tbl.ackNext`): `swift.tbl.Ack.Unmarshal.specS`. The proof is
`MFastAck.Unmarshal`'s (TableFastAck.lean) without the replica and ballot, over a 10-byte buffer;
its helpers are repeated here (namespace `swift.tbl.ackAux`) so that the two modules are
independent.
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

namespace ackAux

theorem count_at {X X' d u rest : List w8} {k : Nat} (hX : X.length = X'.length)
    (ht : sp.uvTerm d) (h : X ++ d ++ u = X' ++ (sp.varintLen k ++ rest)) :
    X = X' ∧ d = sp.varintLen k := by
  rw [List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj h hX
  unfold sp.varintLen at h2 ⊢
  exact ⟨h1, (sp.cw.uvTerm_peel ht h2).1⟩

/-- The first count after a header of the encoding's header's length. -/
theorem v1_gen {hdr hdr' d1 rest : List w8} {n : Nat} (hl : hdr.length = hdr'.length)
    (ht : sp.uvTerm d1) (h : hdr ++ d1 <+: hdr' ++ sp.varintLen n ++ rest) :
    d1 = sp.varintLen n := by
  obtain ⟨u, hu⟩ := h
  exact (count_at hl ht (by simpa [List.append_assoc] using hu)).2

/-- The second count after a header, a count and the dependencies. -/
theorem v2_gen {hdr hdr' d2 rest : List w8} {ds ds' : List sp.CmdId} {n m : Nat}
    (hl : hdr.length = hdr'.length) (hn : ds.length = n) (ht : sp.uvTerm d2)
    (h : hdr ++ sp.varintLen n ++ (ds.map sp.encCmdId).flatten ++ d2 <+:
      hdr' ++ sp.varintLen ds'.length ++ (ds'.map sp.encCmdId).flatten ++ sp.varintLen m ++ rest) :
    d2 = sp.varintLen m ∧ n = ds'.length := by
  obtain ⟨u, hu⟩ := h
  simp only [List.append_assoc] at hu
  obtain ⟨-, h2⟩ := List.append_inj hu hl
  obtain ⟨hnn, h3⟩ := sp.cw.varintLen_peel h2
  subst hnn
  have h4 := count_at (X := (ds.map sp.encCmdId).flatten) (X' := (ds'.map sp.encCmdId).flatten)
    (by rw [cmdIds_length, cmdIds_length, hn]) ht (by simpa [List.append_assoc] using h3)
  exact ⟨h4.2, rfl⟩

theorem data_len {data bs : List w8} {k : Nat} (hl : data.length ≤ bs.length)
    (hb : bs.length = k) (hk : k < 2 ^ 63) (he : sint.Z (W64 k) ≤ (data.length : Int)) :
    data.length = k := by
  have h : sint.Z (W64 (k : Int)) = k := by word
  omega

theorem data_four {data bs : List w8} (hl : data.length ≤ bs.length) (hb : bs.length = 4)
    (he : sint.Z (W64 4) ≤ (data.length : Int)) : ∃ a b c d, data = [a, b, c, d] := by
  have hlen := data_len hl hb (by omega) he
  match data, hlen with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem encCmdId_bytes (e0 e1 e2 e3 g0 g1 g2 g3 : w8) :
    sp.encCmdId ⟨leToU32 [e0, e1, e2, e3], leToU32 [g0, g1, g2, g3]⟩ =
      [e0, e1, e2, e3, g0, g1, g2, g3] := by
  simp only [sp.encCmdId, sp.le32]
  rw [leToU32_le _ rfl, leToU32_le _ rfl]
  rfl


theorem ack_enc (a : sp.Ack) (w : List w8) :
    a.enc ++ w = sp.encCmdId a.id ++
      sp.varintLen a.dep.length ++ (a.dep.map sp.encCmdId).flatten ++
      sp.varintLen a.cs.length ++ (a.cs.flatten ++ sp.le64 a.seqnum ++ w) := by
  simp [sp.Ack.enc, sp.encDep, sp.encHashes, List.append_assoc]

theorem cmdId8_len (x : sp.CmdId) : (sp.encCmdId x).length = 8 := by
  simp [sp.le32, sp.encCmdId, u32Le_length]

section slices
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- The buffer `b[:10]` as its prefix `b[:k]`, and back (any `k` bytes). -/
theorem slice10_sub (p : Loc) (l : List w8) (k : Nat) (hk : k ≤ 10) :
    (slice.mk p (W64 10) (W64 10) ↦* l : IProp netDistGF) ⊢
      slice.mk p (W64 k) (W64 10) ↦* l.take k ∗
      (∀ ys : List w8, slice.mk p (W64 k) (W64 10) ↦* ys -∗
        ∃ l' : List w8, slice.mk p (W64 10) (W64 10) ↦* l') := by
  have hk1 : sint.nat (W64 (k : Int)) = k := by word
  have hk2 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) ≤ sint.Z (W64 10) := by
    constructor <;> word
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := H; simp [slice.nil] at h1
  simp only
  icases (array_split (V := w8) (W64 k) p (DFrac.own 1) _ _ hk2).1 $$ H with ⟨H1, H2⟩
  rw [hk1]
  isplitl [H1]
  · iright; iframe H1; ipureintro; word
  iintro %ys (%Hys | ⟨Hys, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := Hys; simp [slice.nil] at h1
  simp only
  ihave %Hlen := array_len _ _ _ _ $$ Hys
  iexists ys ++ l.drop k
  iright
  isplitl [Hys H2]
  · iapply (array_split (V := w8) (W64 k) p (DFrac.own 1) _ (array.mk _ (ys ++ l.drop k)) hk2).2
    have hk3 : sint.Z (W64 (k : Int)) = k := by word
    have hy : ys.length = k := by omega
    rw [hk1, List.take_left' hy, List.drop_left' hy]
    iframe Hys H2
  · ipureintro; word

end slices

end ackAux

section proof
open swift.rd (wp_store_Hacc data_one set_slot)
open ackAux
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- Load `bs[0..7]` of the slice `Hb8`. -/
macro "ld8c" : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 4)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 5)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 6)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 7)) _ _ _ (by decide) $$ [Hb8] as Hb8
  · iframe Hb8; ipureintro; rfl
  try wp_auto))

set_option hygiene false in
/-- Load `bs[0..3]` of the slice `Hb4`. -/
macro "ld4c" : tactic => `(tactic| (
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
theorem Ack.Unmarshal.wp_proof : Ack.Unmarshal.specS (hG := hG) := by
  intro t v br rd I R
  wp_start as ⟨Hctx, #Hrd, #Hlaw, Hown, Ht⟩
  unfold ctxV
  icases Hctx with ⟨#Hpkg, #Hpkg2, #Hbin, %ov, #Hov, %Hovn⟩
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) swift.byteReader.ty = true := by
    go_type_set
  try wp_auto
  rw [hts]
  wp_auto
  ihave #Hbr := bufio.bufioReadsOk br rd I $$ [$Hpkg2 $Hrd]
  ihave Hb := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl]
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
    show W64 10 - W64 0 = W64 10 from rfl]
  icases slice10_sub b_ptr (List.replicate 10 (W8 0)) 8 (by omega) $$ Hb with ⟨Hb8, Hback⟩
  rw [show ((8 : Nat) : Int) = 8 from rfl]
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ ((List.replicate 10 (W8 0)).take 8) (W64 8) (by decide) $$
    [$Hpkg $Hbr $Hown $Hb8] as %n %err ⟨%data, %Hd, Hb8, Hown, #He⟩
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
  have h8 := data_len (k := 8) hdl (by simp) (by decide) (herr.1 rfl)
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ : ∃ d0 d1 d2 d3 d4 d5 d6 d7 : w8,
      data = [d0, d1, d2, d3, d4, d5, d6, d7] := by
    match data, h8 with
    | [d0, d1, d2, d3, d4, d5, d6, d7], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩
  rw [show List.drop [d0, d1, d2, d3, d4, d5, d6, d7].length (List.take 8 (List.replicate 10 (W8 0))) = []
    by simp, List.append_nil]
  wp_auto
  ld8c
  try wp_auto
  isimp only [← encoding.binary.leToU32_4] at Ht
  icases Hback $$ Hb8 with ⟨%l0, Hsl⟩
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · -- an error: returned
    wp_auto
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
  rw [← encCmdId_bytes, show (⟨leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7]⟩ : swift.CommandId) =
    ofCmdId ⟨leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7]⟩ from rfl]
  generalize hx : (⟨leToU32 [d0, d1, d2, d3], leToU32 [d4, d5, d6, d7]⟩ : sp.CmdId) = xid at *
  -- the count is the encoding's own
  icases streamLaw_use br rd I R ((sp.encCmdId xid) ++ vd1) ackNext
    $$ [$Hlaw Hown] with ⟨Hown, >%Hl1⟩
  · iExactEq Hown; simp only [List.append_assoc]
  obtain ⟨f1, w1, hw1, hp1⟩ := Hl1
  rw [ack_enc] at hp1
  have hv1 := v1_gen (hdr := sp.encCmdId xid) (hdr' := sp.encCmdId f1.id)
    (n := f1.dep.length) (rest := (f1.dep.map sp.encCmdId).flatten ++ sp.varintLen f1.cs.length ++
      (f1.cs.flatten ++ sp.le64 f1.seqnum ++ w1))
    (by simp only [cmdId8_len]) ht1 (by simpa only [List.append_assoc] using hp1)
  subst hv1
  obtain ⟨hn63, rfl⟩ := swift.rd.varint_count f1.dep.length hb1 hx1
  have hn62 : f1.dep.length < 2 ^ 62 := hw1.1
  generalize f1.dep.length = n at *
  clear hp1 hw1 w1 f1
  wp_auto
  wp_apply wp_slice_make2 (V := swift.CommandId) (W64 n) as %dsl ⟨Hdsl, -⟩
  · ipureintro; word
  ihave %Hdsllen := ownSlice_len $$ Hdsl
  rw [show sint.nat (W64 n) = n by word]
  ihave HL : (∃ (k : Nat) (ds : List sp.CmdId) (bsv : GoSlice) (l16 : List w8),
      "i" ∷ i_ptr ↦ W64 k ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "Ht" ∷ t ↦ swift.Ack.mk (ofCmdId xid) dsl v.Checksum' v.Seqnum' ∗
      "Hdsl" ∷ dsl ↦* (ds.map ofCmdId ++ List.replicate (n - k) (zero_val swift.CommandId)) ∗
      "Hown" ∷ bufio.ownReader br rd I
        (R ++ (sp.encCmdId xid ++ sp.varintLen n ++
          (ds.map sp.encCmdId).flatten)) ∗
      "Hb" ∷ slice.mk b_ptr (W64 10) (W64 10) ↦* l16 ∗
      "%Hk" ∷ ⌜k ≤ n ∧ ds.length = k⌝ : IProp netDistGF) $$ [i bs Ht Hdsl Hown Hsl]
  · iexists 0, [], _, _
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · have hkn : k < n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      have h3 : sint.Z (W64 (k : Int)) < sint.Z (W64 (n : Int)) := by simpa using Hif
      omega
    obtain ⟨hkn', rfl⟩ := Hk
    ihave %Hl16 := ownSlice_len $$ Hb
    have hl16 : l16.length = 10 := by rw [Hl16.1]; rfl
    try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
      show W64 10 - W64 0 = W64 10 from rfl]
    icases slice10_sub b_ptr l16 4 (by omega) $$ Hb with ⟨Hb4, Hback⟩
    wp_apply bufio.wp_ReadAtLeast _ _ _ _ (l16.take 4) (W64 4)
      (by rw [show sint.Z (W64 4) = 4 from rfl, List.length_take, hl16]; decide) $$
      [$Hpkg $Hbr $Hown $Hb4] as %n0 %err ⟨%data0, %Hd0, Hb4, Hown, #He0⟩
    obtain ⟨-, hdl0, herr0⟩ := Hd0
    rcases err with eo0 | _
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
    obtain ⟨e0, e1, e2, e3, rfl⟩ := data_four hdl0 (by simp [hl16]) (herr0.1 rfl)
    rw [show List.drop [e0, e1, e2, e3].length (List.take 4 l16) = [] by simp, List.append_nil]
    rw [show ((4 : Nat) : Int) = 4 from rfl]
    have hlook : (ds.map ofCmdId ++ List.replicate (n - ds.length) (zero_val swift.CommandId))[
        ((ds.length : Nat) : Int).toNat]? = some (zero_val swift.CommandId) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    icases ownSlice_elem_acc ((ds.length : Nat) : Int) (zero_val swift.CommandId) dsl _ _ (by omega)
      hlook $$ Hdsl with ⟨Hel, Hdsl⟩
    have hbnd : 0 ≤ sint.Z (W64 (ds.length : Int)) ∧ sint.Z (W64 (ds.length : Int)) < sint.Z dsl.len := by
      obtain ⟨h1, h2⟩ := Hdsllen
      simp only [List.length_replicate] at h1
      have hn' : sint.nat (W64 (n : Int)) = n := by word
      rw [hn'] at h1
      have h3 : sint.nat dsl.len = (sint.Z dsl.len).toNat := rfl
      have : sint.Z (W64 (ds.length : Int)) = ds.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (ds.length : Int)) = ds.length := by word
    wp_auto
    ld4c
    rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
    wp_auto
    wp_apply bufio.wp_ReadAtLeast _ _ _ _ [e0, e1, e2, e3] (W64 4)
      (by simp only [List.length_cons, List.length_nil]; decide) $$
      [$Hpkg $Hbr $Hown $Hb4] as %n1 %err ⟨%data1, %Hd1, Hb4, Hown, #He1⟩
    obtain ⟨-, hdl1, herr1⟩ := Hd1
    rcases err with e1' | _
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
    obtain ⟨g0, g1, g2, g3, rfl⟩ := data_four hdl1 rfl (herr1.1 rfl)
    rw [show List.drop [g0, g1, g2, g3].length [e0, e1, e2, e3] = [] by simp, List.append_nil]
    wp_auto
    ld4c
    rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
    wp_auto
    isimp only [← encoding.binary.leToU32_4] at Hel
    ihave Hdsl := Hdsl $$ Hel
    icases Hback $$ Hb4 with ⟨%l', Hb⟩
    wp_for_post
    iframe
    iexists ds.length + 1, ds ++ [⟨leToU32 [e0, e1, e2, e3], leToU32 [g0, g1, g2, g3]⟩], _, l'
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [bs]
    · iexact bs
    isplitl [Ht]
    · iexact Ht
    isplitl [Hdsl]
    · iExactEq Hdsl; congr 1
      rw [Int.toNat_natCast, swift.rd.set_slot ofCmdId ds _ _ (n - ds.length) (by omega)]
      simp [List.map_append, List.append_assoc, Nat.sub_add_eq]
      rfl
    isplitl [Hown]
    · iExactEq Hown; congr 1
      simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, encCmdId_bytes, List.append_assoc]
      rfl
    isplitl [Hb]
    · iexact Hb
    ipureintro
    simp; omega
  · -- the dependencies' end: `n` of them, then the checksum's count
    obtain ⟨hkn', hlk⟩ := Hk
    have hkn : k = n := by
      have h1 : sint.Z (W64 (k : Int)) = k := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      have h3 : ¬ (sint.Z (W64 (k : Int)) < sint.Z (W64 (n : Int))) := by simpa using Hif
      omega
    subst hkn
    rw [Nat.sub_self, List.replicate_zero, List.append_nil]
    try wp_auto
    wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x2 %err ⟨%vd2, Hown, %Hx2⟩
    · ipureintro; exact Hovn
    rcases err with eo2 | _
    · wp_auto
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
    icases streamLaw_use br rd I R ((sp.encCmdId xid ++ sp.varintLen k ++
        (ds.map sp.encCmdId).flatten) ++ vd2) ackNext $$ [$Hlaw Hown] with ⟨Hown, >%Hl2⟩
    · iExactEq Hown; simp only [List.append_assoc]
    obtain ⟨f2, w2, hw2, hp2⟩ := Hl2
    rw [ack_enc] at hp2
    obtain ⟨hv2, -⟩ := v2_gen (hdr := sp.encCmdId xid)
      (hdr' := sp.encCmdId f2.id) (ds := ds) (ds' := f2.dep)
      (n := k) (m := f2.cs.length) (rest := f2.cs.flatten ++ sp.le64 f2.seqnum ++ w2)
      (by simp only [cmdId8_len]) hlk ht2 (by simpa only [List.append_assoc] using hp2)
    subst hv2
    obtain ⟨hm63, rfl⟩ := swift.rd.varint_count f2.cs.length hb2 hx2
    have hm62 : f2.cs.length < 2 ^ 62 := hw2.2.1
    generalize f2.cs.length = m at *
    clear hp2 hw2 w2 f2
    wp_auto
    wp_apply wp_slice_make2 (V := swift.SHash) (W64 m) as %csl ⟨Hcsl, -⟩
    · ipureintro; word
    ihave %Hcsllen := ownSlice_len $$ Hcsl
    rw [show sint.nat (W64 m) = m by word]
    try wp_auto
    isimp only at Ht
    iclear He
    ihave %Hl16 := ownSlice_len $$ Hb
    have hl16 : l16.length = 10 := by rw [Hl16.1]; rfl
    obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, l16 = y0 :: rest := by
      cases l16 with
      | nil => simp at hl16
      | cons y0 rest => exact ⟨y0, rest, rfl⟩
    icases slice10_sub b_ptr (y0 :: rest) 1 (by omega) $$ Hb with ⟨Hb1, Hback⟩
    rw [show ((1 : Nat) : Int) = 1 from rfl, show List.take 1 (y0 :: rest) = [y0] by simp]
    ihave HL : (∃ (k' : Nat) (hs : List sp.Hash) (y : w8) (bsv : GoSlice),
        "i" ∷ i_ptr ↦ W64 k' ∗ "bs" ∷ bs_ptr ↦ bsv ∗
        "Ht" ∷ t ↦ swift.Ack.mk (ofCmdId xid) dsl csl v.Seqnum' ∗
        "Hsl" ∷ csl ↦* (hs.map swift.handler.shashOf ++
          List.replicate (m - k') (zero_val swift.SHash)) ∗
        "Hown" ∷ bufio.ownReader br rd I (R ++ (sp.encCmdId xid ++
          sp.varintLen k ++ (ds.map sp.encCmdId).flatten ++ sp.varintLen m ++ hs.flatten)) ∗
        "Hb1" ∷ slice.mk b_ptr (W64 1) (W64 10) ↦* [y] ∗
        "%Hk" ∷ ⌜k' ≤ m ∧ hs.length = k' ∧ sp.cw.hashOk hs⌝ : IProp netDistGF)
      $$ [i bs Ht Hcsl Hown Hb1]
    · iexists 0, [], y0, _
      simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
      iframe
      ipureintro; simp [sp.cw.hashOk]
    wp_for HL
    wp_if_destruct
    · have hkm : k' < m := by
        have h1 : sint.Z (W64 (k' : Int)) = k' := by word
        have h2 : sint.Z (W64 (m : Int)) = m := by word
        have h3 : sint.Z (W64 (k' : Int)) < sint.Z (W64 (m : Int)) := by simpa using Hif
        omega
      obtain ⟨hkm', rfl, hok⟩ := Hk
      have hlook : (hs.map swift.handler.shashOf ++ List.replicate (m - hs.length) (zero_val swift.SHash))[
          ((hs.length : Nat) : Int).toNat]? = some (zero_val swift.SHash) := by
        rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
        simp only [List.length_map, Nat.sub_self]
        rw [List.getElem?_replicate]; simp; omega
      icases ownSlice_elem_acc ((hs.length : Nat) : Int) (zero_val swift.SHash) csl _ _ (by omega)
        hlook $$ Hsl with ⟨He, Hsl⟩
      have hbnd : 0 ≤ sint.Z (W64 (hs.length : Int)) ∧ sint.Z (W64 (hs.length : Int)) < sint.Z csl.len := by
        obtain ⟨h1, h2⟩ := Hcsllen
        simp only [List.length_replicate] at h1
        have hn' : sint.nat (W64 (m : Int)) = m := by word
        rw [hn'] at h1
        have h3 : sint.nat csl.len = (sint.Z csl.len).toNat := rfl
        have : sint.Z (W64 (hs.length : Int)) = hs.length := by word
        rw [this]; omega
      have hk64 : sint.Z (W64 (hs.length : Int)) = hs.length := by word
      rw [show (zero_val swift.SHash) = swift.SHash.mk ⟨([] : List w8) ++
        List.replicate 32 (W8 0)⟩ from rfl] at *
      rw [show R ++ (sp.encCmdId xid ++ sp.varintLen k ++
          (ds.map sp.encCmdId).flatten ++ sp.varintLen m ++ hs.flatten) =
        (R ++ (sp.encCmdId xid ++ sp.varintLen k ++
          (ds.map sp.encCmdId).flatten ++ sp.varintLen m ++ hs.flatten)) ++ [] from
          (List.append_nil _).symm]
      generalize hB : R ++ (sp.encCmdId xid ++ sp.varintLen k ++
          (ds.map sp.encCmdId).flatten ++ sp.varintLen m ++ hs.flatten) = B
      try wp_auto
      try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 1 - W64 0 = W64 1 from rfl,
        show W64 10 - W64 0 = W64 10 from rfl]
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
        rw [Int.toNat_natCast, set_slot swift.handler.shashOf hs _ _ (m - hs.length) (by omega)]
        simp [swift.handler.shashOf, List.map_append, List.append_assoc]
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
    · -- the checksum's end: `m` hashes, then the sequence number
      obtain ⟨hkm', hlh, hok⟩ := Hk
      have hkm : k' = m := by
        have h1 : sint.Z (W64 (k' : Int)) = k' := by word
        have h2 : sint.Z (W64 (m : Int)) = m := by word
        have h3 : ¬ (sint.Z (W64 (k' : Int)) < sint.Z (W64 (m : Int))) := by simpa using Hif
        omega
      subst hkm
      rw [Nat.sub_self, List.replicate_zero, List.append_nil]
      icases Hback $$ Hb1 with ⟨%l2, Hb⟩
      ihave %Hl2 := ownSlice_len $$ Hb
      have hl2 : l2.length = 10 := by rw [Hl2.1]; rfl
      try wp_auto
      try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
        show W64 10 - W64 0 = W64 10 from rfl]
      icases slice10_sub b_ptr l2 8 (by omega) $$ Hb with ⟨Hb8, -⟩
      rw [show ((8 : Nat) : Int) = 8 from rfl]
      wp_apply bufio.wp_ReadAtLeast _ _ _ _ (l2.take 8) (W64 8)
        (by rw [show sint.Z (W64 8) = 8 from rfl, List.length_take, hl2]; decide) $$
        [$Hpkg $Hbr $Hown $Hb8] as %n8 %err ⟨%data8, %Hd8, Hb8, Hown, #He8⟩
      obtain ⟨-, hdl8, herr8⟩ := Hd8
      rcases err with eo8 | _
      · wp_auto
        iapply HΦ
        iexists _
        isplitl [Hown]
        · iExactEq Hown; simp only [List.append_assoc]; rfl
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists _
        iexact Ht
      have h8 := data_len (k := 8) hdl8 (by simp [hl2]) (by decide) (herr8.1 rfl)
      obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, rfl⟩ : ∃ s0 s1 s2 s3 s4 s5 s6 s7 : w8,
          data8 = [s0, s1, s2, s3, s4, s5, s6, s7] := by
        match data8, h8 with
        | [s0, s1, s2, s3, s4, s5, s6, s7], _ => exact ⟨s0, s1, s2, s3, s4, s5, s6, s7, rfl⟩
      rw [show List.drop [s0, s1, s2, s3, s4, s5, s6, s7].length (List.take 8 l2) = [] by simp [hl2],
        List.append_nil]
      wp_auto
      ld8c
      try wp_auto
      isimp only [← encoding.binary.leToU64_8] at Ht
      iapply HΦ
      iexists _
      isplitl [Hown]
      · iExactEq Hown; simp only [List.append_assoc]; rfl
      ileft
      isplitr
      · ipureintro; rfl
      iexists ⟨xid, ds, hs, leToU64 [s0, s1, s2, s3, s4, s5, s6, s7]⟩, dsl, csl
      isplitr
      · ipureintro
        refine ⟨?_, ?_, ?_, fun h hh => hok h hh⟩
        · simp only [sp.Ack.enc, sp.encDep, sp.encHashes, sp.le64]
          rw [leToU64_le _ rfl, hlk, hlh]
          simp only [List.append_assoc]
        · simp only [sp.depWf]; rw [hlk]; omega
        · rw [hlh]; exact hm62
      iframe


end proof

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
