/- Lean-first (no Rocq counterpart).

Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/GetConfChange.lean` at the
store's `cf`, `kvConfRead`: on any bytes (`getUint64.specAny`: a short read is not `ok`, its rest the
nil slice), a `ConfChange` of a type and an id (its cells frozen: `t.Enum()`, `new(id)`), or a
`ConfChangeV2` of a transition `tr ≤ 2` (`t.Enum()`) whose changes are appended in a loop (each a
frozen `ConfChangeSingle`, `ccsRO`, as kvdurable's `randomChange`); the transition is defined
(`ccTransOk`), a `ConfChange`'s the automatic one.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.GetConfChange
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64Any
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeTransition__Enum
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ConfDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3
open raft_kvreconf (ccTransOk ccToV2 ccTransOk_v1)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `ConfChangeV2` of a defined transition is shaped, whatever its changes. -/
theorem ccTransOk_v2' (t : w32) (chs : List ConfChangeSingleM) (ctx : List w8)
    (ht : t = W32 0 ∨ t = W32 1 ∨ t = W32 2) : ccTransOk (.v2 ⟨t, chs, ctx⟩) := by
  simp only [ccTransOk, ccToV2, enterJointOf]
  rcases ht with h | h | h <;> subst h <;> by_cases hn : 1 < chs.length <;> simp [hn]

/-- `b[1:]` of `b0 :: pl'`: the tail. -/
theorem ownSlice_tail1 (b : GoSlice) (dq : DFrac) (b0 : w8) (pl' : List w8)
    (Hlen : (b0 :: pl').length = sint.nat b.len) (Hpos : 0 ≤ sint.Z b.len) :
    (b ↦*{dq} (b0 :: pl') : IProp GF) ⊢ slice.slice b w8 (W64 1) b.len ↦*{dq} pl' := by
  have Hrng : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.len := by
    simp only [List.length_cons] at Hlen
    refine ⟨by decide, by word, Int.le_refl _⟩
  have Hsub : subslice (sint.nat (W64 1)) (sint.nat b.len) (b0 :: pl') = pl' := by
    rw [show sint.nat (W64 1) = 1 from rfl, ← Hlen]
    simp [subslice]
  refine (ownSlice_slice (W64 1) b.len b dq _ Hrng).1.trans ?_
  rw [Hsub]
  iintro ⟨-, H, -⟩
  iexact H

/-- `getUint64` on any bytes, its rest's bytes named (the nil slice's `[]` on a short read). -/
theorem wp_getU (wp_getUint64 : getUint64.specAny (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac)
    (bs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
        b ↦*{dq} bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64)) (Val #b))
    {{ (x : w64) (rest : GoSlice) (ok : Bool), RET (PairV (PairV #x #rest) #ok);
        ∃ bs1 : List w8, rest ↦*{dq} bs1 ∗
          ⌜if ok then bs = u64Le x ++ bs1 else bs.length < 8 ∧ bs1 = []⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hb⟩ HΦ
  wp_apply wp_getUint64 b dq bs $$ [$Hpkg $Hb] as %x %rest %ok Hr
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hr with ⟨⟨%Hs, %Hn⟩, -⟩
    subst Hn
    iapply HΦ
    iexists []
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr
    · iapply ownSlice_nil
    ipureintro; exact ⟨Hs, by first | rfl | trivial⟩
  · simp only [↓reduceIte]
    icases Hr with ⟨%Hs, Hr, -⟩
    iapply HΦ
    iexists bs.drop 8
    simp only [↓reduceIte]
    iframe Hr
    ipureintro; exact Hs

theorem GetConfChange.wp_proof (wp_getUint64 : getUint64.specAny (GF := GF) (hG := hG))
    (wp_TypeEnum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (wp_TransEnum : raftpb.ConfChangeTransition.Enum.spec (GF := GF) (hG := hG)) :
    GetConfChange.spec (GF := GF) (hG := hG) kvConfRead := by
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  intro b pl dq
  wp_start as Hb
  -- read-only from here (the post does not give it back)
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hb with #Hb
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  obtain ⟨b0, pl', rfl⟩ : ∃ b0 pl', pl = b0 :: pl' := by
    cases pl with
    | nil => exfalso; simp only [List.length_nil] at Hlen; word
    | cons a l => exact ⟨a, l, rfl⟩
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
    simp only [List.length_cons] at Hlen; constructor <;> word
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ DFrac.discard b0 (by decide) $$ [Hb] as -
  · iframe Hb; ipureintro; rfl
  try wp_auto
  have Hsl1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap := by
    simp only [List.length_cons] at Hlen; refine ⟨by decide, by word, Hwf.2⟩
  ihave #Ht := ownSlice_tail1 b DFrac.discard b0 pl' Hlen.1 Hlen.2 $$ Hb
  wp_if_destruct
  · -- a `ConfChange`
    try rw [ite_eq_left Hsl1]
    try simp only [Hsl1, _root_.and_self, ↓reduceIte]
    wp_apply wp_getU wp_getUint64 _ DFrac.discard pl' $$ [$Hpkg $Ht] as %t %r1 %ok1 ⟨%bs1, #Hr1, %Hok1⟩
    try wp_auto
    wp_apply wp_getU wp_getUint64 _ DFrac.discard bs1 $$ [$Hpkg $Hr1] as %nid %r2 %ok2 ⟨%bs2, #Hr2, %Hok2⟩
    try wp_auto
    ihave %Hr2len := ownSlice_len _ _ _ $$ Hr2
    cases ok1 <;> cases ok2 <;> try wp_auto
    all_goals try (iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial; done)
    wp_if_destruct
    · try wp_auto
      iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    try wp_auto
    wp_if_destruct
    · wp_apply wp_TypeEnum (W32 (uint.Z t)) $$ [$Hpb] as %pty Hpty
      imod cellRO_alloc _ _ $$ Hpty with #cty
      try wp_auto
      imod cellRO_alloc _ _ $$ «$v1» with #cnd
      wp_alloc_auto
      rename_i l
      irename : (l ↦ (_ : raftpb.ConfChange) : IProp GF) => Hl
      ihave #cnull := cellRO_null (GF := GF) (V := w64)
      ihave #Hnilb : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod ownConfChange_of_struct l
        { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», Context' := slice.nil, Id' := null,
          unknownFields' := slice.nil, sizeCache' := 0 }
        { type := W32 (uint.Z t), nodeId := nid, context := [], id := zero_val w64 } ⊤ rfl
        $$ [Hl] with Hv1
      · dsimp only
        iframe Hl
        iframe cty cnd cnull Hnilb
      try wp_auto
      iapply HΦ
      simp only [↓reduceIte]
      unfold kvConfRead
      iexists ConfChangeIM.v1 { type := W32 (uint.Z t), nodeId := nid, context := [], id := zero_val w64 }
      isplitl
      · simp only [ownConfChangeI]
        iexists l
        iframe Hv1
        ipureintro; rfl
      ipureintro; exact ccTransOk_v1 _
    · try wp_auto
      iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · -- a `ConfChangeV2`
    try rw [ite_eq_left Hsl1]
    try simp only [Hsl1, _root_.and_self, ↓reduceIte]
    try wp_auto
    wp_apply wp_getU wp_getUint64 _ DFrac.discard pl' $$ [$Hpkg $Ht] as %tr %r1 %ok1 ⟨%bs1, #Hr1, %Hok1⟩
    try wp_auto
    wp_apply wp_getU wp_getUint64 _ DFrac.discard bs1 $$ [$Hpkg $Hr1] as %n %r2 %ok2 ⟨%bs2, #Hr2, %Hok2⟩
    try wp_auto
    simp only [Hb0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ DFrac.discard b0 (by decide) $$ [Hb] as -
    · iframe Hb; ipureintro; rfl
    try wp_auto
    by_cases Hb2 : b0 = W8 2
    rotate_left
    · simp only [Hb2, decide_false, Bool.not_false]
      try wp_auto
      iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    simp only [Hb2, decide_true, Bool.not_true]
    cases ok1 <;> cases ok2 <;> try wp_auto
    all_goals try (iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial; done)
    wp_if_destruct
    · try wp_auto
      iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    have Htr2 : uint.Z tr ≤ 2 := by
      first | (have := Hif; word) | (revert Hif; word)
    clear Hif
    try wp_auto
    wp_if_destruct
    · try wp_auto
      iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    clear Hif
    wp_apply wp_TransEnum (W32 (uint.Z tr)) $$ [$Hpb] as %ptr Hptr
    imod cellRO_alloc _ _ $$ Hptr with #cT
    try wp_auto
    ihave %Hnn := typedPointsto_not_null $$ «$r0»
    iStructNamed «$r0»
    irename : ("_" ∷ True : IProp GF) => Hjunk
    iclear Hjunk
    ihave IH : iprop(∃ (k : w64) (rs : GoSlice) (rb : List w8) (chs : GoSlice) (ls : List Loc)
        (ms : List ConfChangeSingleM),
        "i" ∷ i_ptr ↦ k ∗ "rest" ∷ rest_ptr ↦ rs ∗ "#Hrs" ∷ rs ↦*□ rb ∗
        "Changes" ∷ «$r0_ptr».[raftpb.ConfChangeV2, go!"Changes"] ↦ chs ∗
        "Hch" ∷ chs ↦* ls ∗ "Hchc" ∷ ownSliceCap Loc chs (DFrac.own 1) ∗
        "#Hccs" ∷ ([∗list] q;m ∈ ls;ms, ccsRO q m)) $$ [i rest Changes]
    · iexists W64 0, r2, bs2, slice.nil, [], []
      iframe i rest Changes Hr2
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      iapply BigSepL2.bigSepL2_nil.2; itrivial
    iapply wp_fupd
    wp_for IH
    wp_if_destruct
    · -- one more change
      wp_apply wp_getU wp_getUint64 _ DFrac.discard rb $$ [$Hpkg $Hrs] as %t %r3 %okt ⟨%bs3, #Hr3, -⟩
      try wp_auto
      wp_apply wp_getU wp_getUint64 _ DFrac.discard bs3 $$ [$Hpkg $Hr3] as %nid %r4 %oki ⟨%bs4, #Hr4, -⟩
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_for_post
        imodintro
        iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      wp_apply wp_TypeEnum (W32 (uint.Z t)) $$ [$Hpb] as %pty Hpty
      imod cellRO_alloc _ _ $$ Hpty with #cty
      try wp_auto
      imod cellRO_alloc _ _ $$ «$v1» with #cnd
      imod ccsRO_of_struct «$sl0_ptr»
        { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
          sizeCache' := 0 }
        (ConfChangeSingleM.mk (W32 (uint.Z t)) nid) ⊤ rfl $$ [«$sl0»] with #Hq
      · dsimp only
        iframe
        iframe cty cnd
      wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hch $Hchc $Hsl1] as %chs' ⟨Hch, Hchc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, r4, bs4, chs', ls ++ [«$sl0_ptr»], ms ++ [ConfChangeSingleM.mk (W32 (uint.Z t)) nid]
      iframe
      iframe Hr4
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hccs Hq
    · -- the change, its transition defined
      ihave #Hnilb : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      ihave Hl := typedPointsto_combine «$r0_ptr»
        ({ state' := zeroValDef, Transition' := ptr, Changes' := chs, Context' := slice.nil,
           unknownFields' := slice.nil, sizeCache' := 0 } : raftpb.ConfChangeV2) (DFrac.own 1)
        Hnn $$ [state Transition Changes Context unknownFields sizeCache]
      · simp only [TypedPointsto.typedPointstoDef]
        iframe
      imod ownConfChangeV2_of_struct «$r0_ptr»
        { state' := zeroValDef, Transition' := ptr, Changes' := chs, Context' := slice.nil,
          unknownFields' := slice.nil, sizeCache' := 0 }
        ⟨W32 (uint.Z tr), ms, []⟩ ls ⊤ rfl $$ [Hl Hch] with Hv2
      · dsimp only
        iframe Hl Hch
        iframe cT Hccs Hnilb
      try wp_auto
      imodintro
      iapply HΦ
      split
      · unfold kvConfRead
        iexists ConfChangeIM.v2 ⟨W32 (uint.Z tr), ms, []⟩
        isplitl
        · simp only [ownConfChangeI]
          iexists «$r0_ptr»
          iframe Hv2
          ipureintro; rfl
        ipureintro
        apply ccTransOk_v2'
        have : uint.Z tr = 0 ∨ uint.Z tr = 1 ∨ uint.Z tr = 2 := by word
        rcases this with h | h | h
        · left; word
        · right; left; word
        · right; right; word
      · itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
