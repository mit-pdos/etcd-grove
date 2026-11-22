/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/getMsg.lean`: the eight
words read into `f` (`getUint64`, a loop over the array), the type looked up in raftpb's
`MessageType_name` (raftpb's package fact: `msgTypeNames`), reject, the hint, the context (`getBytes`,
frozen: a message's context is read-only), the entries' number; then the entries (`getMsgEntry`, on
the bytes frozen: the case with no snapshot) or none (the case with no entries: the bytes stay
owned); the message built (`msgPtsC_of_struct`), then its snapshot (`getSnapshot`) or none.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsg
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getUint64
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getBytes
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsgEntry
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getSnapshot
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbMsg
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbLog
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbSnapSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The message's eight words, in `putMsg`'s order. -/
def msgWords [GooseExts] (st : MsgSt) : List w64 :=
  [W64 (sint.Z st.msg.Type'), st.msg.To', st.msg.From', st.msg.Term', st.msg.LogTerm',
    st.msg.Index', st.msg.Commit', st.msg.Vote']

/-- What follows the eight words. -/
def msgTail [GooseExts] (st : MsgSt) : List w8 :=
  boolB st.msg.Reject' :: (u64Le st.msg.RejectHint' ++ (putB st.ctx ++
    (u64Le (W64 st.ents.length) ++ (encEntries st.ents ++ encSnapOpt st.snap))))

theorem encMsg_words [GooseExts] (st : MsgSt) : encMsg st = u64sLe (msgWords st) ++ msgTail st := by
  simp [encMsg, msgWords, msgTail, u64sLe, List.append_assoc]

theorem u64sLe_drop [GooseExts] (ws : List w64) (i : Nat) (h : i < ws.length) :
    u64sLe (ws.drop i) = u64Le ws[i] ++ u64sLe (ws.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons h]; rfl

theorem arr_step (W : List w64) (i : Nat) (hW : W.length = 8) (hi : i < 8) :
    (W.take i ++ List.replicate (8 - i) (W64 0)).set i W[i] =
      W.take (i + 1) ++ List.replicate (8 - (i + 1)) (W64 0) := by
  match W, hW with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl

theorem type_rt (t : w32) : W32 (uint.Z (W64 (sint.Z t))) = t := by
  word

theorem type_rt' (t : w32) : W32 (sint.Z t) = t := by
  word

theorem type_small (t : w32) (h : 0 ≤ sint.Z t) :
    ¬ uint.Z (W64 2147483648) < uint.Z (W64 (sint.Z t)) := by
  word

theorem encEntries_length_ge [GooseExts] (es : List EntryM) : es.length ≤ (encEntries es).length := by
  induction es with
  | nil => simp [encEntries]
  | cons e r ih =>
    simp only [encEntries, encEntry, List.length_append, List.length_cons, u64Le_length, putB_length]
    omega

theorem tail_len [GooseExts] (st : MsgSt) : 1 ≤ (msgTail st).length := by
  simp [msgTail]

theorem boolB_eq (r : Bool) : decide (boolB r = W8 1) = r := by
  cases r <;> simp [boolB, autoB]

theorem n_fits (n L : Nat) (r3len : w64) (h1 : L = sint.nat r3len) (h2 : 0 ≤ sint.Z r3len)
    (hn : n ≤ L) (hn63 : (n : Int) < 2 ^ 63) : ¬ uint.Z r3len < uint.Z (W64 n) := by
  word

theorem n_nonneg (n : Nat) (hn63 : (n : Int) < 2 ^ 63) : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 n) := by
  word

theorem loop_in (j : w64) (n : Nat) (hn : (n : Int) < 2 ^ 63) (Hif : uint.Z j < uint.Z (W64 n)) :
    uint.nat j < n ∧ uint.nat (j + W64 1) = uint.nat j + 1 := by
  constructor <;> word

theorem loop_out (j : w64) (n : Nat) (hn : (n : Int) < 2 ^ 63) (Hj : uint.nat j ≤ n)
    (Hif : ¬ uint.Z j < uint.Z (W64 n)) : uint.nat j = n := by
  word

theorem snapOpt_len (o : Option SnapshotM) (rl : w64) (h1 : (encSnapOpt o).length = sint.nat rl)
    (h2 : 0 ≤ sint.Z rl) : ¬ sint.Z rl < sint.Z (W64 1) := by
  have : 1 ≤ (encSnapOpt o).length := by cases o <;> simp [encSnapOpt]
  word

theorem len_one (rl : w64) (h1 : 1 = sint.nat rl) (h2 : 0 ≤ sint.Z rl) : rl - W64 1 = W64 0 := by
  word

theorem word_exit (j : w64) (Hj : 0 ≤ sint.Z j ∧ sint.Z j ≤ 8) (Hif : ¬ sint.Z j < sint.Z (W64 8)) :
    sint.nat j = 8 := by
  word

theorem word_step (j : w64) (Hj : 0 ≤ sint.Z j ∧ sint.Z j ≤ 8) (Hif : sint.Z j < sint.Z (W64 8)) :
    sint.nat j < 8 ∧ (0 ≤ sint.Z j ∧ sint.Z j < 8) ∧ sint.nat (j + W64 1) = sint.nat j + 1 ∧
      (0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- The `Snapshot` field of a message, lent, and set to another snapshot (`m.Snapshot = snap`). -/
private theorem msgPtsC_Snapshot_set (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Snapshot"] ↦{dq} p ∗ snapOpt p dq ms.snap ∗
        (∀ (p' : Loc) (o : Option SnapshotM), l.[raftpb.Message, go!"Snapshot"] ↦{dq} p' -∗
          snapOpt p' dq o -∗ msgPtsC l dq dqe cap { ms with snap := o }) := by
  iintro H
  iunfold msgPtsC at H
  iNamed H
  iexists ps
  iframe HSn Hsn
  iintro %p' %o HSn Hsn
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, p', cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

theorem getMsg.wp_proof (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_getBytes : getBytes.spec (GF := GF) (hG := hG))
    (wp_getMsgEntry : getMsgEntry.spec (GF := GF) (hG := hG))
    (wp_getSnapshot : getSnapshot.spec (GF := GF) (hG := hG))
    (wp_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    getMsg.spec (GF := GF) (hG := hG) := by
  intro b st Hwf
  wp_start as Hb
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  rw [encMsg_words] at *
  try wp_auto
  rename_i ip0
  have HW8 : (msgWords st).length = 8 := rfl
  -- the eight words, into `f`
  ihave IH : iprop(∃ (j : w64) (rv : GoSlice) (k0 : w64),
      "i" ∷ i_ptr ↦ j ∗ "iv" ∷ ip0 ↦ k0 ∗
      "f" ∷ f_ptr ↦ (array.mk 8 ((msgWords st).take (sint.nat j) ++
        List.replicate (8 - sint.nat j) (W64 0)) : GoArray w64 8) ∗
      "rest" ∷ rest_ptr ↦ rv ∗
      "Hb" ∷ rv ↦* (u64sLe ((msgWords st).drop (sint.nat j)) ++ msgTail st) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 8⌝)
    $$ [-HΦ «$res0» «$res1»]
  · iexists W64 0, b, W64 0
    iframe
    ipureintro; decide
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hj8, Hjr, Hj1, Hjn⟩ := word_step j Hj Hif
    rw [u64sLe_drop _ _ (by rw [HW8]; exact Hj8), List.append_assoc]
    try wp_auto
    wp_apply wp_getUint64 rv _ _ _ $$ [$Hb] as %r ⟨Hr, -⟩
    try wp_auto
    rw [ite_eq_left Hjr]
    have Hlk : (array.mk 8 ((msgWords st).take (sint.nat j) ++
        List.replicate (8 - sint.nat j) (W64 0)) : GoArray w64 8).arr[(sint.Z j).toNat]? =
          some (W64 0) := by
      show ((msgWords st).take (sint.nat j) ++ List.replicate (8 - sint.nat j) (W64 0))[sint.nat j]? = _
      rw [List.getElem?_append_right (by simp only [List.length_take]; exact Nat.min_le_left _ _)]
      simp only [List.length_take, HW8, Nat.min_eq_left (Nat.le_of_lt Hj8), Nat.sub_self,
        List.getElem?_replicate]
      have h8 : 0 < 8 - sint.nat j := Nat.sub_pos_of_lt Hj8
      simp only [h8, ↓reduceIte]
    icases array_acc f_ptr (sint.Z j) (DFrac.own 1) 8 _ (W64 0) Hj.1 Hlk $$ f with ⟨Hfe, Hfb⟩
    try wp_auto
    ihave f := Hfb $$ %((msgWords st)[sint.nat j]) Hfe
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, r, j
    rw [Hj1]
    simp only [show (sint.Z j).toNat = sint.nat j from rfl]
    rw [arr_step _ _ HW8 Hj8]
    iframe
    ipureintro; exact Hjn
  · have Hj8 := word_exit j Hj Hif
    rw [Hj8] at *
    simp only [List.take_of_length_le (show (msgWords st).length ≤ 8 from Nat.le_of_eq HW8),
      List.drop_of_length_le (show (msgWords st).length ≤ 8 from Nat.le_of_eq HW8), Nat.sub_self,
      List.replicate_zero, List.append_nil, u64sLe, List.nil_append]
    ihave #Hfact : iprop(∃ m : Loc,
        (globalAddr go_etcd_io.raft.v3.raftpb.MessageType_name ↦□ m : IProp GF) ∗
        m ↦$□ go_etcd_io.raft.v3.raftpb.msgTypeNames) $$ []
    · iapply (isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb).trans sep_elim_left $$ Hpb
    icases Hfact with ⟨%mt, #Hg, #Hmt⟩
    -- `f`, one cell per word
    icases typedPointsto_split _ _ _ $$ f with Hf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hf with ⟨-, Hf⟩
    simp only [arrayElems, msgWords]
    icases Hf with ⟨F0, F1, F2, F3, F4, F5, F6, F7, -⟩
    rw [show ((0 : Nat) : Int) = sint.Z (W64 0) from rfl,
      show ((0 + 1 : Nat) : Int) = sint.Z (W64 1) from rfl,
      show ((0 + 1 + 1 : Nat) : Int) = sint.Z (W64 2) from rfl,
      show ((0 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 3) from rfl,
      show ((0 + 1 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 4) from rfl,
      show ((0 + 1 + 1 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 5) from rfl,
      show ((0 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 6) from rfl,
      show ((0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 7) from rfl]
    try wp_auto
    rw [type_rt]
    obtain ⟨Hknown, Hnn, Hewf, Henl, Hctxl, Hswf⟩ := Hwf
    rw [type_rt'] at Hknown
    obtain ⟨tn, Htn⟩ := Option.isSome_iff_exists.mp Hknown
    generalize raftpb.msgTypeNames = M at Htn ⊢
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string mt
      M st.msg.Type' DFrac.discard) $$ Hmt as -
    rw [Htn]
    simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
    try wp_auto
    rw [decide_eq_false (type_small _ Hnn)]
    try wp_auto
    ihave %Hlr := ownSlice_len _ _ _ $$ Hb
    have Hlr' : 1 ≤ sint.Z rv.len := by have := tail_len st; have := Hlr.1; have := Hlr.2; word
    rw [decide_eq_false (show ¬ sint.Z rv.len < sint.Z (W64 1) by word)]
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rv.len by word)]
    simp only [msgTail]
    wp_apply wp_load_slice_index rv (sint.Z (W64 0)) _ _ (boolB st.msg.Reject') (by decide)
      $$ [$Hb] as Hb
    · ipureintro; rfl
    try wp_auto
    ihave %Hw := ownSlice_wf _ _ _ $$ Hb
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z rv.len ∧
      sint.Z rv.len ≤ sint.Z rv.cap by refine ⟨by decide, by word, Hw.2⟩)]
    icases (ownSlice_split_all (W64 1) rv (DFrac.own 1) _
      ⟨by decide, by word⟩).1 $$ Hb with ⟨-, Hb⟩
    simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
    wp_apply wp_getUint64 _ _ _ _ $$ [$Hb] as %r1 ⟨Hr1, -⟩
    try wp_auto
    wp_apply wp_getBytes r1 _ _ _ Hctxl $$ [$Hr1] as %cv %r2 ⟨Hcv, Hr2, -⟩
    try wp_auto
    wp_apply wp_getUint64 r2 _ _ _ $$ [$Hr2] as %r3 ⟨Hr3, -⟩
    try wp_auto
    ihave %Hl3 := ownSlice_len _ _ _ $$ Hr3
    rw [decide_eq_false (n_fits st.ents.length _ r3.len (by rw [← Hl3.1]) Hl3.2
      (by simp only [List.length_append]; have := encEntries_length_ge st.ents; omega) Henl)]
    try wp_auto
    imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hcv with #Hcv
    wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 st.ents.length) (n_nonneg _ Henl))
      as %sv0 ⟨Hsv0, Hcap0, -⟩
    try wp_auto
    ihave IH : iprop(∃ (j : w64) (sv rv : GoSlice) (ls : List Loc),
        "i" ∷ i_ptr ↦ j ∗ "ents" ∷ ents_ptr ↦ sv ∗ "rest" ∷ rest_ptr ↦ rv ∗
        "Hsv" ∷ sv ↦* ls ∗ "Hcap" ∷ ownSliceCap Loc sv (DFrac.own 1) ∗
        "#Hls" ∷ ([∗list] l;e ∈ ls;st.ents.take (uint.nat j), entRO l e) ∗
        "Hrv" ∷ rv ↦* (encEntries (st.ents.drop (uint.nat j)) ++ encSnapOpt st.snap) ∗
        "%Hj" ∷ ⌜uint.nat j ≤ st.ents.length⌝)
      $$ [i ents rest Hsv0 Hcap0 Hr3]
    · iexists W64 0, sv0, r3, []
      simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero,
        List.replicate_zero]
      iframe
      isplitl []
      · iapply BigSepL2.bigSepL2_nil.2; iempintro
      ipureintro; exact Nat.zero_le _
    wp_for IH
    wp_if_destruct
    · obtain ⟨Hin, Hj1⟩ := loop_in j _ Henl Hif
      obtain ⟨e0, He0⟩ : ∃ e0, st.ents[uint.nat j]? = some e0 :=
        ⟨_, List.getElem?_eq_getElem Hin⟩
      have Hdrop : st.ents.drop (uint.nat j) = e0 :: st.ents.drop (uint.nat j + 1) := by
        rw [List.drop_eq_getElem_cons Hin]
        rw [List.getElem?_eq_getElem Hin] at He0
        rw [Option.some.inj He0]
      have Hwf0 : MsgEntWf e0 := Hewf e0 (List.mem_of_getElem? He0)
      rw [Hdrop]
      simp only [encEntries, List.append_assoc]
      try wp_auto
      wp_apply wp_getMsgEntry rv (DFrac.own 1) e0 _ Hwf0 $$ [$Hrv] as %le %rest2 ⟨Hle, Hrest2⟩
      try wp_auto
      imod entOwn_freeze _ _ $$ Hle with #Hle
      wp_apply wp_slice_literal (V := Loc) [le]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsv $Hcap $Hsl2] as %sv' ⟨Hsv, Hcap, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, sv', rest2, ls ++ [le]
      have Htk : st.ents.take (uint.nat j + 1) = st.ents.take (uint.nat j) ++ [e0] := by
        rw [List.take_add_one, He0]; rfl
      rw [Hj1, Htk]
      iframe
      isplitl []
      · iapply entsBig_app
        iframe Hls
        iapply BigSepL2.bigSepL2_singleton.2; iexact Hle
      ipureintro; omega
    · have Hjk := loop_out j _ Henl Hj Hif
      rw [Hjk, List.take_length, List.drop_length] at *
      simp only [encEntries, List.nil_append]
      try wp_auto
      ihave %Hlv := ownSlice_len _ _ _ $$ Hrv
      rw [decide_eq_false (snapOpt_len st.snap rv.len Hlv.1 Hlv.2)]
      try wp_auto
      rw [type_rt]
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      try wp_auto
      iapply wp_fupd
      wp_apply wp_Enum st.msg.Type' $$ [$Hpb] as %pty Hpty
      try wp_auto
      rw [boolB_eq]
      imod cellRO_alloc _ _ $$ Hpty with #cTy
      imod cellRO_alloc _ _ $$ «$v1» with #cTo
      imod cellRO_alloc _ _ $$ «$v2» with #cFr
      imod cellRO_alloc _ _ $$ «$v3» with #cTe
      imod cellRO_alloc _ _ $$ «$v4» with #cLt
      imod cellRO_alloc _ _ $$ «$v5» with #cIx
      imod cellRO_alloc _ _ $$ «$v6» with #cCo
      imod cellRO_alloc _ _ $$ «$v7» with #cVo
      imod cellRO_alloc _ _ $$ «$v8» with #cRj
      imod cellRO_alloc _ _ $$ «$v9» with #cRh
      ihave Hrnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod msgPtsC_of_struct «$r0_ptr» (⟨zeroValDef, pty, «$v1_ptr», «$v2_ptr», «$v3_ptr», «$v4_ptr»,
          «$v5_ptr», sv, «$v6_ptr», «$v7_ptr», null, «$v8_ptr», «$v9_ptr», cv, slice.nil, slice.nil, 0⟩ :
          raftpb.Message) (DFrac.own 1) true ls ⟨st.msg, st.ents, none, st.ctx, []⟩ ⊤ rfl
        $$ [«$r0» Hsv Hcap Hrnil] with Hm
      · iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hls Hcv
        simp only [snapOpt, ↓reduceIte]
        iframe
      cases Hs : st.snap with
      | none =>
        simp only [Hs, encSnapOpt, List.length_singleton] at Hlv ⊢
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rv.len by word)]
        wp_apply wp_load_slice_index rv (sint.Z (W64 0)) _ _ (W8 0) (by decide) $$ [$Hrv] as Hrv
        · ipureintro; rfl
        try wp_auto
        ihave %Hw := ownSlice_wf _ _ _ $$ Hrv
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z rv.len ∧
          sint.Z rv.len ≤ sint.Z rv.cap by refine ⟨by decide, by word, Hw.2⟩)]
        try wp_auto
        rw [decide_eq_true (len_one rv.len Hlv.1 Hlv.2)]
        imodintro
        iapply HΦ
        iexact Hm
      | some s =>
        simp only [Hs, encSnapOpt, List.length_cons] at Hlv ⊢
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rv.len by word)]
        wp_apply wp_load_slice_index rv (sint.Z (W64 0)) _ _ (W8 1) (by decide) $$ [$Hrv] as Hrv
        · ipureintro; rfl
        try wp_auto
        ihave %Hw := ownSlice_wf _ _ _ $$ Hrv
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z rv.len ∧
          sint.Z rv.len ≤ sint.Z rv.cap by refine ⟨by decide, by word, Hw.2⟩)]
        icases (ownSlice_split_all (W64 1) rv (DFrac.own 1) _
          ⟨by decide, by word⟩).1 $$ Hrv with ⟨-, Hrv⟩
        simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
        rw [← List.append_nil (encSnap s)]
        wp_apply wp_getSnapshot _ s [] (Hswf s Hs) $$ [$Hrv] as %sp %r7 ⟨Hsn, Hr7⟩
        try wp_auto
        icases msgPtsC_Snapshot_set _ _ _ _ _ $$ Hm with ⟨%p0, HSn, -, Hset⟩
        try wp_auto
        ihave Hsn := ownSnapS_M _ _ _ $$ Hsn
        ihave Hm := Hset $$ %sp %(some s) HSn [Hsn]
        · simp only [snapOpt]; iexact Hsn
        try wp_auto
        ihave %Hl7 := ownSlice_len _ _ _ $$ Hr7
        rw [decide_eq_true (show r7.len = W64 0 by simp at Hl7; word)]
        imodintro
        iapply HΦ
        simp only
        iexact Hm

end proof

end raft_kvnet
end EtcdGrove
end Perennial
