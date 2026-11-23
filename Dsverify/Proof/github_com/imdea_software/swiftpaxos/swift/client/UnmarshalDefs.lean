/-
The definitions, specs and lemmas of `Unmarshal.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.ClientStream
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.Varint
public import Perennial.Proof.encoding.binary
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerInv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.rd

open swift.handler (shashOf)

/-- A wire command id as the Go struct. -/
def cmdIdV [GooseExts] (x : sp.CmdId) : swift.CommandId := ⟨x.cl, x.seq⟩

section specs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF] [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]

/-- `(*MLightSlowAck).Unmarshal(rd)`: the next 16 bytes. -/
abbrev MLightSlowAck.Unmarshal.specI : Prop :=
  ∀ (t : Loc) (v : swift.MLightSlowAck) (rd : GoInterface) (I : List w8 → IProp GF)
    (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ bufio.readsOk rd I ∗ I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MLightSlowAck.ty @!! go!"Unmarshal")) (Val #rd))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ s : sp.SlowAck, ⌜data = s.enc⌝ ∗
          t ↦ swift.MLightSlowAck.mk s.rep s.bal (cmdIdV s.id)) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MLightSlowAck, t ↦ v')) }}

end specs

section proofs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF] [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- Load `bs[0..15]` of the slice `Hsl`. -/
macro "rd_ld16" : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 4)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 5)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 6)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 7)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 8)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 9)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 10)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 11)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 12)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 13)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 14)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 15)) _ _ _ (by decide) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rfl
  try wp_auto))

end proofs

end swift.rd

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.rd

open swift.handler (shashOf)

section specs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- `(*MFastAckClient).Unmarshal(br)` on the client's reader of a replica's stream, after the
frames of `done` and the type byte `MFastAckClient` (10): without an error, the bytes read are
the body of an `MFastAckClient` (its hashes 32 bytes each). -/
abbrev MFastAckClient.Unmarshal.specI : Prop :=
  ∀ (t : Loc) (v : swift.MFastAckClient) (br : Loc) (srv : GoInterface) (c : Nat)
    (γ : sp.Names) (γc γm : GName) (cl : w32) (done : List sp.Msg) (ov : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗ isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      bufio.readerOk srv (recvTokL c false (sp.outQ γ γc γm)) ∗ sp.connKind γ c (.client cl) ∗
      bufio.ownReader br srv (recvTokL c false (sp.outQ γ γc γm)) (sp.framesOf done ++ [W8 10]) ∗
      typedPointsto (globalAddr swift.errVarintOverflow) ov DFrac.discard ∗
      ⌜ov ≠ interface.nil ∧ ∀ d ∈ done, sp.cw.cMsg cl d⌝ ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MFastAckClient.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8,
      bufio.ownReader br srv (recvTokL c false (sp.outQ γ γc γm)) (sp.framesOf done ++ [W8 10] ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b : w32) (x : sp.CmdId) (cs : List sp.Hash) (csl : GoSlice),
          ⌜data = (sp.Msg.fastAckClient r b x cs).body ∧ sp.cw.hashOk cs⌝ ∗
          t ↦ swift.MFastAckClient.mk r b (cmdIdV x) csl ∗ csl ↦* cs.map shashOf) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MFastAckClient, t ↦ v')) }}

/-- `(*MReply).Unmarshal(br)` on the client's reader of a replica's stream, after the
frames of `done` and the type byte `MReply` (15): without an error, the bytes read are
the body of an `MReply` (its hashes 32 bytes each, at least one). -/
abbrev MReply.Unmarshal.specI : Prop :=
  ∀ (t : Loc) (v : swift.MReply) (br : Loc) (srv : GoInterface) (c : Nat)
    (γ : sp.Names) (γc γm : GName) (cl : w32) (done : List sp.Msg) (ov : GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗ isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      bufio.readerOk srv (recvTokL c false (sp.outQ γ γc γm)) ∗ sp.connKind γ c (.client cl) ∗
      bufio.ownReader br srv (recvTokL c false (sp.outQ γ γc γm)) (sp.framesOf done ++ [W8 15]) ∗
      typedPointsto (globalAddr swift.errVarintOverflow) ov DFrac.discard ∗
      ⌜ov ≠ interface.nil ∧ ∀ d ∈ done, sp.cw.cMsg cl d⌝ ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MReply.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8,
      bufio.ownReader br srv (recvTokL c false (sp.outQ γ γc γm)) (sp.framesOf done ++ [W8 15] ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b : w32) (x : sp.CmdId) (cs : List sp.Hash) (val : List w8)
          (csl vsl : GoSlice),
          ⌜data = (sp.Msg.reply r b x cs val).body ∧ sp.cw.hashOk cs ∧ cs ≠ []⌝ ∗
          t ↦ swift.MReply.mk r b (cmdIdV x) csl vsl ∗ csl ↦* cs.map shashOf ∗ vsl ↦* val) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MReply, t ↦ v')) }}

end specs2

section proofs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
/-- The first byte of a 16-byte buffer, as the slice `b[:1]`. -/
theorem slice_take1 (p : Loc) (x : w8) (rest : List w8) (hl : rest.length = 15) :
    (slice.mk p (W64 16) (W64 16) ↦* (x :: rest) : IProp netDistGF) ⊢
      slice.mk p (W64 1) (W64 16) ↦* [x] := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨h1, -⟩ := H; simp [slice.nil] at h1
  iright
  simp only
  icases (array_split (V := w8) (W64 1) p (DFrac.own 1) _ _ (by simp; decide)).1 $$ H with ⟨H, -⟩
  isplitl [H]
  · iExactEq H; rfl
  · ipureintro; decide

/-- A count read as `varintLen n` (below `2 ^ 64` as decoded): `n` itself. -/
theorem varint_count (n : Nat) {x : w64} (hb : sp.uvDec (sp.varintLen n) < 2 ^ 64)
    (hx : x = unzigzag (W64 (sp.uvDec (sp.varintLen n) : Int))) : n < 2 ^ 63 ∧ x = W64 n := by
  unfold sp.varintLen at hb hx
  rw [sp.cw.uvDec_uvarint] at hb hx
  refine ⟨by omega, ?_⟩
  subst hx
  unfold unzigzag
  have : W64 ((2 * n : Nat) : Int) &&& W64 1 = W64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (W64 1).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp [W64]; omega
  rw [if_pos this]
  apply BitVec.eq_of_toNat_eq
  simp [W64, BitVec.toNat_ushiftRight]
  omega

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
/-- Storing byte `j` of an `SHash`'s array. -/
theorem wp_store_H (e : Loc) (arr : List w8) (j : Int) (hj : 0 ≤ j ∧ j < arr.length) (x : w8) :
    {{ (e ↦ (swift.SHash.mk ⟨arr⟩) : IProp netDistGF) }}
      (App (Val (GoInstruction (GoStore go.byte)))
        (Val (PairV #(arrayIndexRef w8 j (structFieldRef swift.SHash go!"H" e)) #x)))
    {{ RET #(); e ↦ (swift.SHash.mk ⟨arr.set j.toNat x⟩) }} := by
  iintro %Φ He HΦ
  icases typedPointsto_not_null_dup _ _ _ $$ He with ⟨He, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ He with He
  simp only [TypedPointsto.typedPointstoDef]
  icases He with ⟨H, -⟩
  obtain ⟨v, hv⟩ : ∃ v, arr[j.toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (V := w8) _ j _ 32 ⟨arr⟩ v hj.1 hv $$ H with ⟨Hv, Hw⟩
  wp_apply IntoValTyped.wp_store (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  ihave H := Hw $$ %x Hv
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe H

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions] [bufio.Assumptions] in
/-- Storing the next byte of a hash being read (`acc` read so far, `m` zeros after). -/
theorem wp_store_Hacc (e : Loc) (acc : List w8) (m : Nat) (j : w64) (x : w8) :
    {{ (e ↦ (swift.SHash.mk ⟨acc ++ List.replicate m (W8 0)⟩) : IProp netDistGF) ∗
        ⌜sint.Z j = acc.length ∧ acc.length + m = 32 ∧ 0 < m⌝ }}
      (App (Val (GoInstruction (GoStore go.byte)))
        (Val (PairV #(arrayIndexRef w8 (sint.Z j) (structFieldRef swift.SHash go!"H" e)) #x)))
    {{ RET #(); e ↦ (swift.SHash.mk ⟨(acc ++ [x]) ++ List.replicate (m - 1) (W8 0)⟩) }} := by
  iintro %Φ ⟨He, %Hjm⟩ HΦ
  obtain ⟨hj, hm⟩ := Hjm
  wp_apply wp_store_H e (acc ++ List.replicate m (W8 0)) (sint.Z j) (by rw [hj]; refine ⟨by omega, ?_⟩; simp only [List.length_append, List.length_replicate]; omega) x $$ [$He] as He
  iapply HΦ
  iExactEq He
  rw [hj, Int.toNat_natCast, List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [List.replicate_succ, List.set_cons_zero]
  simp

theorem set_slot {A B : Type} (f : A → B) (hs : List A) (z v : B) (m : Nat) (hm : 0 < m) :
    (hs.map f ++ List.replicate m z).set hs.length v = hs.map f ++ [v] ++ List.replicate (m - 1) z := by
  rw [List.set_append_right _ _ (by simp)]
  simp only [List.length_map, Nat.sub_self]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [List.replicate_succ]

theorem data_one {data : List w8} {u : w8} (hl : data.length ≤ [u].length)
    (he : sint.Z (W64 1) ≤ (data.length : Int)) : ∃ z, data = [z] := by
  have : sint.Z (W64 1) = 1 := rfl
  match data, hl with
  | [], _ => simp at he <;> omega
  | [z], _ => exact ⟨z, rfl⟩

/-- A literal length. -/
macro "rd_len_lit" : tactic => `(tactic| (
  simp only [List.length_append, List.length_cons, List.length_nil]; rfl))

set_option hygiene false in
/-- One byte of a hash: `ReadAtLeast(wire, bs, 1)` (an error returns), then
`t.Checksum[i].H[j] = bs[0]`. -/
macro "rd_hbyte" z:ident : tactic => `(tactic| (
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 1 - W64 0 = W64 1 from rfl,
    show W64 16 - W64 0 = W64 16 from rfl]
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ [_] (W64 1) (by simp) $$
    [Hown Hb1] as %n0 %err ⟨%data0, %Hd0, Hb1, Hown, #He0⟩
  · iframe Hown Hb1 Hbr
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
  obtain ⟨$z, rfl⟩ := data_one hdl0 (herr0.1 rfl)
  try isimp only [List.length_cons, List.length_nil, List.drop_one, List.drop_nil, List.append_nil,
    List.tail_cons, Nat.reduceAdd] at Hb1
  rw [List.append_assoc B _ [$z]]
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hb1] as Hb1
  · iframe Hb1; ipureintro; rfl
  rw [ite_cond_eq_true _ _ (eq_true hbnd)]
  try wp_auto
  try rw [hk64]
  wp_apply wp_store_Hacc _ _ _ _ $z $$ [He] as He
  · iframe He; ipureintro; exact ⟨by rd_len_lit, by simp⟩))

end proofs2

end swift.rd

end Perennial.github_com.imdea_software.swiftpaxos
