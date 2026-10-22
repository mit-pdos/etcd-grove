/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/msgAppV2Decoder__decode.lean`.
Lean-first.

What the decoder reads is a prefix of a frame or extends one (`V2Compat`, from what is known of
the bytes, `B`), so each length it reads is the frame's, and the bytes it unmarshals are an
encoding (`pbutil.MustUnmarshalMessage` would panic otherwise): `entFrames_prefix`, `chunk_eq`,
`append8_eq`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder__decode
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Spec.google_golang_org.protobuf.proto.ClonePb
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessagePb
public import Spec.encoding.binary.ReadUint64
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- An error returned: the reader at its bytes, the decoder at the state `cs`, its buffers holding
`zs`, `x8`, `x1`. -/
local macro "dec_err" cs:term "," zs:term "," x8:term "," x1:term : tactic => `(tactic| (
  wp_auto
  iapply HΦ
  iexists _, $cs
  iframe HRd
  isplitl
  · iunfold v2DecOwn
    iexists buf, s8, s1, $zs, $x8, $x1
    iframe; iframe #; iframe %
    try (ipureintro; simp only [List.length_append, List.length_drop] at *; omega)
  iintro %h0; cases h0))

set_option hygiene false in
/-- An error returned from inside the entries' loop (`dec_err`, through the loop's return). -/
local macro "dec_err_l" cs:term "," zs:term "," x8:term "," x1:term : tactic => `(tactic| (
  wp_auto
  wp_for_post
  iapply HΦ
  iexists _, $cs
  iframe HRd
  isplitl
  · iunfold v2DecOwn
    iexists buf, s8, s1, $zs, $x8, $x1
    iframe; iframe #; iframe %
    try (ipureintro; simp only [List.length_append, List.length_drop] at *; omega)
  iintro %h0; cases h0))

set_option maxHeartbeats 2000000 in
theorem rafthttp.msgAppV2Decoder.decode.wp_proof
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG))
    (wp_MustUnmarshalMessage : pbutil.MustUnmarshalMessagePb.spec (GF := GF) (hG := hG))
    (wp_ReadUint64 : binary.ReadUint64.spec (GF := GF) (hG := hG)) :
    rafthttp.msgAppV2Decoder.decode.spec (GF := GF) (hG := hG) := by
  intro dec r frm to cst Rd B rs
  wp_start as ⟨Hdec, #Hrf, HRd, #HC⟩
  iunfold readFullAt at Hrf
  iunfold v2DecOwn at Hdec
  iNamed Hdec
  wp_auto
  wp_apply Hrf $$ %s1 %x1 %rs [$Hs1s $HRd] as %n %err ⟨%ys, Hs1s, HRd, #HB, %Hys⟩
  (try wp_auto)
  cases err with
  | ok ei => dec_err cst, zs, x8, (ys ++ x1.drop ys.length)
  | nil =>
  have hys1 : ys.length = 1 := by have := Hys.2.2 rfl; omega
  rw [List.drop_of_length_le (by omega), List.append_nil]
  ihave %Hc1 := HC $$ %ys HB
  obtain ⟨t, rfl⟩ : ∃ t, ys = [t] := by
    match ys, hys1 with
    | [t], _ => exact ⟨t, rfl⟩
  wp_auto
  ihave %Hs1l := ownSlice_len _ _ _ $$ Hs1s
  rw [if_pos (by simp at Hs1l; word)]
  wp_apply (wp_load_slice_index (V := w8) s1 (sint.Z (W64 0)) [t] (DFrac.own 1) t (by word))
    $$ [Hs1s] as Hs1s
  · iframe; ipureintro; rfl
  (try wp_auto)
  rcases Hc1.head with ⟨rfl, hF0⟩ | rfl | rfl
  · -- the link heartbeat: a clone of `linkHeartbeatMessage`
    rw [decide_eq_true (p := W8 0 = W8 0) rfl]
    wp_auto
    ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hei with ⟨-, #Hhb⟩
    have wpC := wp_Clone pbMessage (globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.linkHeartbeatMessage)
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.hbSt
    simp only [pbMessage_ty, pbMessage_ro, pbMessage_dec, pbMessage_eqv] at wpC
    wp_apply wpC $$ [] as %l' ⟨%m', Hl', %Heqv⟩
    · iexact Hhb
    (try wp_auto)
    iapply HΦ
    iexists _, cst
    iframe HRd
    isplitl [Hterm Hindex Hbufs Hbufc Hs8s Hs1s]
    · iunfold v2DecOwn
      iexists buf, s8, s1, zs, x8, [W8 0]
      iframe; iframe #; iframe %
    iintro -
    iexists hbWire, [W8 0], m'
    iframe Hl' HB
    ipureintro
    exact ⟨hF0, rfl, Heqv.symm⟩
  · -- AppEntries
    wp_auto
    rw [show _root_.Perennial.go_etcd_io.raft.v3.raftpb.MsgApp =
      #((W32 3 : _root_.Perennial.go_etcd_io.raft.v3.raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_Enum (W32 3) as %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    (try wp_auto)
    -- the count
    wp_apply Hrf $$ %s8 %x8 %(rs ++ [W8 1]) [$Hs8s $HRd] as %n0 %err ⟨%c8, Hs8s, HRd, #HB8, %Hc8⟩
    (try wp_auto)
    cases err with
    | ok ei => dec_err cst, zs, (c8 ++ x8.drop c8.length), [W8 1]
    | nil =>
    have hc8 : c8.length = 8 := by have := Hc8.2.2 rfl; omega
    rw [List.drop_of_length_le (by omega), List.append_nil]
    rw [show rs ++ [W8 1] ++ c8 = rs ++ (W8 1 :: c8) by simp]
    ihave %Hcc := HC $$ %(W8 1 :: c8) HB8
    obtain ⟨n, hn, rfl⟩ := Hcc.short_count hc8
    wp_auto
    wp_apply encoding.binary.wp_BigEndian_Uint64 s8 (u64Be (W64 n)) (DFrac.own 1) []
      (u64Be_length _) $$ [Hs8s] as Hs8s
    · simp only [List.append_nil]; iexact Hs8s
    simp only [List.append_nil]
    rw [show leToU64 (u64Be (W64 n)).reverse = W64 n from beToU64_u64Be _]
    (try wp_auto)
    imod cellRO_alloc $$ «$v1» with #cFr
    imod cellRO_alloc $$ «$v2» with #cTo
    imod cellRO_alloc $$ «$v3» with #cTe
    imod cellRO_alloc $$ «$v4» with #cLt
    imod cellRO_alloc $$ «$v5» with #cIx
    wp_apply wp_slice_make2 (V := Loc) $$ [] as %esl ⟨Hesl, Hcap⟩
    · ipureintro; word
    (try wp_auto)
    have hnn : sint.nat (W64 n) = n := by unfold sint.nat; word
    rw [hnn]
    -- the entries
    ihave HI : (∃ (j : Nat) (pre : List (List w8)) (des : List EntryM) (ps : List Loc)
        (zs' x8' : List w8),
        "i" ∷ i_ptr ↦ W64 j ∗
        "HRd" ∷ Rd (rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre)) ∗
        "Hesl" ∷ esl ↦* (ps ++ List.replicate (n - j) (zero_val Loc)) ∗
        "Hents" ∷ ([∗list] p;e ∈ ps;des, entRO p e) ∗
        "Hindex" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"index"] ↦ (cst.index + W64 j) ∗
        "Hbufs" ∷ buf ↦* zs' ∗ "Hbufc" ∷ ownSliceCap w8 buf (DFrac.own 1) ∗
        "Hs8s" ∷ s8 ↦* x8' ∗
        "%Hinv" ∷ ⌜x8'.length = 8 ∧ j ≤ n ∧ pre.length = j ∧ ps.length = j ∧
          List.Forall₂ EntEnc des pre⌝ : IProp GF) $$ [i HRd Hesl Hindex Hbufs Hbufc Hs8s]
    · iexists 0, [], [], [], zs, u64Be (W64 n)
      simp only [entFrames, List.append_nil, List.nil_append, Nat.sub_zero]
      rw [show cst.index + W64 ((0 : Nat) : Int) = cst.index by word]
      iframe
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; iempintro
      ipureintro
      exact ⟨u64Be_length _, Nat.zero_le _, rfl, rfl, .nil⟩
    wp_for HI
    obtain ⟨Hx8', Hjn, Hprel, Hpsl, Hdes⟩ := Hinv
    wp_if_destruct
    · -- the `j`-th entry
      have hj : j < n := by
        have : sint.Z (W64 (j : Int)) = j := by word
        have : sint.Z (W64 (n : Int)) = n := by word
        omega
      wp_apply Hrf $$ %s8 %x8' %(rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre)) [$Hs8s $HRd]
        as %n0 %err ⟨%ys8, Hs8s, HRd, #HB8, %Hy8⟩
      (try wp_auto)
      cases err with
      | ok ei => dec_err_l ⟨cst.term, cst.index + W64 j⟩, zs', (ys8 ++ x8'.drop ys8.length), [W8 1]
      | nil =>
      have hy8 : ys8.length = 8 := by have := Hy8.2.2 rfl; omega
      rw [List.drop_of_length_le (by omega), List.append_nil]
      rw [show rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre) ++ ys8 =
        rs ++ (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ ys8)) by simp]
      ihave %Hcl := HC $$ %(W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ ys8)) HB8
      obtain ⟨sz, hsz, rfl⟩ := Hcl.short_len hn (Forall₂_EntEnc_len Hdes) (by omega) hy8
      wp_auto
      wp_apply encoding.binary.wp_BigEndian_Uint64 s8 (u64Be (W64 sz)) (DFrac.own 1) []
        (u64Be_length _) $$ [Hs8s] as Hs8s
      · simp only [List.append_nil]; iexact Hs8s
      simp only [List.append_nil]
      rw [show leToU64 (u64Be (W64 sz)).reverse = W64 sz from beToU64_u64Be _]
      (try wp_auto)
      ihave %Hzl := ownSlice_len _ _ _ $$ Hbufs
      ihave %Hbwf := ownSliceCap_wf _ _ $$ Hbufc
      have hszz : sint.Z (W64 (sz : Int)) = sz := by word
      have hszn : sint.nat (W64 (sz : Int)) = sz := by unfold sint.nat; word
      wp_if_destruct
      · -- a small entry: read into the decoder's buffer
        have hsz1 : sz < 1048576 := by
          have : uint.Z (W64 (1048576 : Int)) = 1048576 := by word
          have : uint.Z (W64 (sz : Int)) = sz := by word
          omega
        unfold v2BufSize at Hbuflen
        have h0 : sint.Z (W64 0) = 0 := rfl
        rw [if_pos (by rw [h0, hszz]; omega)]
        icases (ownSlice_slice (V := w8) (W64 0) (W64 sz) buf (DFrac.own 1) zs'
          ⟨by simp only [h0]; omega, by rw [h0, hszz]; omega, by rw [hszz]; omega⟩).1 $$ Hbufs
          with ⟨Hb0, Hbm, Hbr⟩
        (try wp_auto)
        wp_apply Hrf $$ %(slice.slice buf w8 (W64 0) (W64 sz))
          %(subslice (sint.nat (W64 0)) (sint.nat (W64 sz)) zs')
          %(rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ u64Be (W64 sz))) [$Hbm $HRd]
          as %n1 %err1 ⟨%eb, Hbm, HRd, #HBe, %Heb⟩
        (try wp_auto)
        have hzl : zs'.length = 1048576 := by
          rw [Hzl.1]; show (sint.Z buf.len).toNat = 1048576; rw [Hbuflen]; rfl
        have hsub : (subslice 0 (sint.nat (W64 sz)) zs').length = sz := by
          simp only [subslice, hszn, List.drop_zero, List.length_take]
          omega
        have hsub' : (subslice (sint.nat (W64 0)) (sint.nat (W64 sz)) zs').length = sz := hsub
        have hbnd : 0 ≤ sint.Z (W64 (sz : Int)) ∧ sint.Z (W64 (sz : Int)) ≤ sint.Z buf.len := by
          rw [hszz]; omega
        cases err1 with
        | ok ei =>
          have hmid : (eb ++ List.drop eb.length
              (subslice 0 (sint.nat (W64 sz)) zs')).length = sint.nat (W64 sz) := by
            have := Heb.2.1; rw [hsub'] at this
            rw [List.length_append, List.length_drop, hsub, hszn]; omega
          ihave Hbufs := ownSlice_rejoin buf zs'
            (eb ++ List.drop eb.length (subslice 0 (sint.nat (W64 sz)) zs')) (W64 sz)
            hbnd hmid $$ [Hb0 Hbm Hbr]
          · rw [show zs'.take (sint.nat (W64 0)) = [] from rfl]; iframe
          dec_err_l ⟨cst.term, cst.index + W64 j⟩,
            (eb ++ List.drop eb.length (subslice 0 (sint.nat (W64 sz)) zs') ++
              zs'.drop (sint.nat (W64 sz))), u64Be (W64 sz), [W8 1]
        | nil =>
        have hebl : eb.length = sz := by have := Heb.2.2 rfl; rw [hsub'] at this; exact this
        rw [List.drop_of_length_le (l := subslice 0 (sint.nat (W64 sz)) zs')
          (by rw [hsub]; omega), List.append_nil]
        rw [show rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ u64Be (W64 sz)) ++ eb =
          rs ++ (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ (u64Be (W64 sz) ++ eb))) by simp]
        ihave %Hce := HC $$ %(W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ (u64Be (W64 sz) ++ eb))) HBe
        obtain ⟨e0, He0⟩ := Hce.short_ent hn (Forall₂_EntEnc_len Hdes) (by omega) hsz hebl
        (try wp_auto)
        ihave %Heslen := ownSlice_len _ _ _ $$ Hesl
        have hesl : sint.Z esl.len = n := by
          have h1 := Heslen.1
          simp only [List.length_append, List.length_replicate, Hpsl] at h1
          have h3 : (sint.Z esl.len).toNat = n := by
            show sint.nat esl.len = n; omega
          have h2 := Heslen.2
          omega
        have hjz : sint.Z (W64 (j : Int)) = j := by word
        rw [if_pos (by rw [hjz, hesl]; omega)]
        wp_apply wp_store_slice_index (V := Loc) esl (sint.Z (W64 (j : Int)))
          (ps ++ List.replicate (n - j) (zero_val Loc)) «$r0_ptr» $$ [$Hesl] as Hesl
        · ipureintro; rw [hjz]; simp [Hpsl]; omega
        rw [show (sint.Z (W64 (j : Int))).toNat = ps.length by rw [hjz, Hpsl]; rfl,
          list_set_snoc_replicate ps (zero_val Loc) «$r0_ptr» (n - j) (by omega)]
        (try wp_auto)
        rw [if_pos (by rw [hjz, hesl]; omega)]
        wp_apply (wp_load_slice_index (V := Loc) esl (sint.Z (W64 (j : Int)))
          ((ps ++ [«$r0_ptr»]) ++ List.replicate (n - j - 1) (zero_val Loc)) (DFrac.own 1) «$r0_ptr»
          (by rw [hjz]; omega)) $$ [Hesl] as Hesl
        · iframe; ipureintro; rw [hjz, ← Hpsl]; simp
        (try wp_auto)
        have wpUE := wp_MustUnmarshalMessage pbEntry «$r0_ptr» (slice.slice buf w8 (W64 0) (W64 sz)) eb (DFrac.own 1) e0 He0.1
        simp only [pbEntry_ty, pbEntry_blank, pbEntry_dec, pbEntry_wire, pbEntry_M] at wpUE
        wp_apply wpUE $$ [$Hbm $«$r0»] as ⟨Hbm, %e1, He1, %Hw1⟩
        (try wp_auto)
        ihave Hbufs := ownSlice_rejoin buf zs' eb (W64 sz) hbnd (by rw [hebl, hszn]) $$ [Hb0 Hbm Hbr]
        · rw [show zs'.take (sint.nat (W64 0)) = [] from rfl]; iframe
        wp_for_post
        iframe
        iexists (j + 1), pre ++ [eb], des ++ [e1], ps ++ [«$r0_ptr»], (eb ++ zs'.drop (sint.nat (W64 sz))), u64Be (W64 sz)
        rw [show W64 ((j + 1 : Nat) : Int) = W64 j + W64 1 by word,
          show cst.index + (W64 j + W64 1) = cst.index + W64 j + W64 1 by word,
          show n - (j + 1) = n - j - 1 by omega, entFrames_snoc, hebl]
        simp only [List.append_assoc] at *
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; iempintro
        ipureintro
        refine ⟨u64Be_length _, by omega, by simp [Hprel], by simp [Hpsl],
          Forall₂_EntEnc_snoc Hdes ⟨Hw1, by omega⟩⟩
      · -- a large entry: read into a fresh slice
        wp_apply wp_slice_make2 (V := w8) $$ [] as %mb ⟨Hbm, -⟩
        · ipureintro; word
        (try wp_auto)
        wp_apply Hrf $$ %mb %(List.replicate (sint.nat (W64 sz)) (zero_val w8))
          %(rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ u64Be (W64 sz))) [$Hbm $HRd]
          as %n1 %err1 ⟨%eb, Hbm, HRd, #HBe, %Heb⟩
        (try wp_auto)
        cases err1 with
        | ok ei => dec_err_l ⟨cst.term, cst.index + W64 j⟩, zs', u64Be (W64 sz), [W8 1]
        | nil =>
        have hebl : eb.length = sz := by
          have := Heb.2.2 rfl; rw [List.length_replicate, hszn] at this; exact this
        rw [List.drop_of_length_le (by rw [List.length_replicate, hszn]; omega), List.append_nil]
        rw [show rs ++ W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ u64Be (W64 sz)) ++ eb =
          rs ++ (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ (u64Be (W64 sz) ++ eb))) by simp]
        ihave %Hce := HC $$ %(W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ (u64Be (W64 sz) ++ eb))) HBe
        obtain ⟨e0, He0⟩ := Hce.short_ent hn (Forall₂_EntEnc_len Hdes) (by omega) hsz hebl
        (try wp_auto)
        ihave %Heslen := ownSlice_len _ _ _ $$ Hesl
        have hesl : sint.Z esl.len = n := by
          have h1 := Heslen.1
          simp only [List.length_append, List.length_replicate, Hpsl] at h1
          have h3 : (sint.Z esl.len).toNat = n := by
            show sint.nat esl.len = n; omega
          have h2 := Heslen.2
          omega
        have hjz : sint.Z (W64 (j : Int)) = j := by word
        rw [if_pos (by rw [hjz, hesl]; omega)]
        wp_apply wp_store_slice_index (V := Loc) esl (sint.Z (W64 (j : Int)))
          (ps ++ List.replicate (n - j) (zero_val Loc)) «$r0_ptr» $$ [$Hesl] as Hesl
        · ipureintro; rw [hjz]; simp [Hpsl]; omega
        rw [show (sint.Z (W64 (j : Int))).toNat = ps.length by rw [hjz, Hpsl]; rfl,
          list_set_snoc_replicate ps (zero_val Loc) «$r0_ptr» (n - j) (by omega)]
        (try wp_auto)
        rw [if_pos (by rw [hjz, hesl]; omega)]
        wp_apply (wp_load_slice_index (V := Loc) esl (sint.Z (W64 (j : Int)))
          ((ps ++ [«$r0_ptr»]) ++ List.replicate (n - j - 1) (zero_val Loc)) (DFrac.own 1) «$r0_ptr»
          (by rw [hjz]; omega)) $$ [Hesl] as Hesl
        · iframe; ipureintro; rw [hjz, ← Hpsl]; simp
        (try wp_auto)
        have wpUE := wp_MustUnmarshalMessage pbEntry «$r0_ptr» mb eb (DFrac.own 1) e0 He0.1
        simp only [pbEntry_ty, pbEntry_blank, pbEntry_dec, pbEntry_wire, pbEntry_M] at wpUE
        wp_apply wpUE $$ [$Hbm $«$r0»] as ⟨Hbm, %e1, He1, %Hw1⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists (j + 1), pre ++ [eb], des ++ [e1], ps ++ [«$r0_ptr»], zs', u64Be (W64 sz)
        rw [show W64 ((j + 1 : Nat) : Int) = W64 j + W64 1 by word,
          show cst.index + (W64 j + W64 1) = cst.index + W64 j + W64 1 by word,
          show n - (j + 1) = n - j - 1 by omega, entFrames_snoc, hebl]
        simp only [List.append_assoc] at *
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; iempintro
        ipureintro
        refine ⟨u64Be_length _, by omega, by simp [Hprel], by simp [Hpsl],
          Forall₂_EntEnc_snoc Hdes ⟨Hw1, by omega⟩⟩
    · -- all entries read: the commit index
      have hjn : j = n := by
        have : sint.Z (W64 (j : Int)) = j := by word
        have : sint.Z (W64 (n : Int)) = n := by word
        omega
      subst hjn
      rw [Nat.sub_self, List.replicate_zero, List.append_nil]
      wp_apply Hrf $$ %s8 %x8' %(rs ++ W8 1 :: (u64Be (W64 j) ++ entFrames pre)) [$Hs8s $HRd]
        as %n0 %err ⟨%c8, Hs8s, HRd, #HBc, %Hc8⟩
      (try wp_auto)
      cases err with
      | ok ei => dec_err ⟨cst.term, cst.index + W64 j⟩, zs', (c8 ++ x8'.drop c8.length), [W8 1]
      | nil =>
      have hc8 : c8.length = 8 := by have := Hc8.2.2 rfl; omega
      rw [List.drop_of_length_le (by omega), List.append_nil]
      rw [show rs ++ W8 1 :: (u64Be (W64 j) ++ entFrames pre) ++ c8 =
        rs ++ (W8 1 :: (u64Be (W64 j) ++ entFrames pre ++ c8)) by simp]
      ihave %Hce := HC $$ %(W8 1 :: (u64Be (W64 j) ++ entFrames pre ++ c8)) HBc
      obtain ⟨c, rfl, Hfr⟩ := Hce.short_end hn (Forall₂_EntEnc_len Hdes) Hprel hc8 Hdes
      wp_auto
      iapply wp_fupd
      wp_apply encoding.binary.wp_BigEndian_Uint64 s8 (u64Be c) (DFrac.own 1) []
        (u64Be_length _) $$ [Hs8s] as Hs8s
      · simp only [List.append_nil]; iexact Hs8s
      simp only [List.append_nil]
      rw [show leToU64 (u64Be c).reverse = c from beToU64_u64Be _]
      (try wp_auto)
      imod cellRO_alloc $$ «$r0» with #cCo
      ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      imod msgPtsC_of_struct m_ptr (⟨zero_val _, pty, «$v2_ptr», «$v1_ptr», «$v3_ptr», «$v4_ptr»,
          «$v5_ptr», esl, «$r0_ptr», null, null, null, null, slice.nil, slice.nil, slice.nil, 0⟩ :
          raftpb.Message) (DFrac.own 1) true ps
          ⟨⟨W32 3, to, frm, cst.term, cst.term, cst.index, c, 0, false, 0⟩, des, none, [], []⟩ ⊤ rfl
          $$ [m Hesl Hcap Hents] with Hmsg
      · simp only [↓reduceIte, snapOpt]
        iframe m Hesl Hcap Hents
        iframe #
        repeat (first
          | (isplitr; · (iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩))
          | (iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩))
        iapply ownSlice_nil
      imodintro
      iapply HΦ
      iexists _, ⟨cst.term, cst.index + W64 j⟩
      iframe HRd
      isplitl [Hterm Hindex Hbufs Hbufc Hs8s Hs1s]
      · iunfold v2DecOwn
        iexists buf, s8, s1, zs', u64Be c, [W8 1]
        iframe; iframe #; iframe %
      iintro -
      iexists shortWire frm to cst des c, shortBytes pre c, _
      iframe Hmsg HBc
      ipureintro
      refine ⟨Hfr, by simp [shortBytes, Hprel, List.append_assoc], rfl⟩
  · -- App: the length, then the message
    wp_auto
    ihave Hbr := wp_ReadUint64 r size_ptr _ iprop(Rd (rs ++ [W8 2]))
      (fun ys _ _ => iprop(Rd (rs ++ [W8 2] ++ ys) ∗ □ B (rs ++ [W8 2] ++ ys))) $$ []
    · iintro !> %sl %xs !> %Φ ⟨Hsl, %Hxs, HRd⟩ HΦ
      wp_apply Hrf $$ %sl %xs %(rs ++ [W8 2]) [$Hsl $HRd] as %n %err ⟨%ys, Hsl, HRd, #HB, %Hys⟩
      iapply HΦ
      iexists ys
      iframe Hsl HRd HB
      ipureintro
      exact ⟨by omega, fun h => by have := Hys.2.2 h; omega⟩
    wp_apply (encoding.binary.wp_load_struct_nofields (V := encoding.binary.bigEndian)
      (globalAddr encoding.binary.BigEndian))
    iintro -
    wp_auto
    wp_apply Hbr $$ [$HRd $size] as %err ⟨%ys8, %n, ⟨HRd, #HB8⟩, Hsz⟩
    icases Hsz with (⟨%Hok8, size⟩ | ⟨%Herr, %x', size⟩)
    · obtain ⟨rfl, hl8⟩ := Hok8
      rw [show rs ++ [W8 2] ++ ys8 = rs ++ (W8 2 :: ys8) by simp]
      ihave %Hc8 := HC $$ %(W8 2 :: ys8) HB8
      obtain ⟨nn, hnn, rfl⟩ := Hc8.app_len hl8
      rw [beToU64_u64Be]
      wp_auto
      wp_apply wp_slice_make2 (V := w8) $$ [] as %mb ⟨Hmb, -⟩
      · ipureintro; word
      (try wp_auto)
      wp_apply Hrf $$ %mb %(List.replicate (sint.nat (W64 nn)) (zero_val w8))
        %(rs ++ W8 2 :: u64Be (W64 nn)) [$Hmb $HRd] as %n2 %err2 ⟨%yb, Hmb, HRd, #HBb, %Hyb⟩
      (try wp_auto)
      cases err2 with
      | ok ei => dec_err cst, zs, x8, [W8 2]
      | nil =>
      have hyl : yb.length = nn := by
        have := Hyb.2.2 rfl; simp at this; rw [this]; unfold sint.nat; word
      rw [List.drop_of_length_le (by rw [List.length_replicate, hyl]; unfold sint.nat; word),
        List.append_nil]
      rw [show rs ++ W8 2 :: u64Be (W64 nn) ++ yb = rs ++ (W8 2 :: (u64Be (W64 nn) ++ yb)) by simp]
      ihave %Hcb := HC $$ %(W8 2 :: (u64Be (W64 nn) ++ yb)) HBb
      obtain ⟨st0, Hw0, Hfr⟩ := Hcb.app hnn hyl
      have wpU := wp_MustUnmarshalMessage pbMessage m_ptr mb yb (DFrac.own 1) st0 Hw0
      simp only [pbMessage_ty, pbMessage_blank, pbMessage_dec, pbMessage_wire] at wpU
      (try wp_auto)
      wp_apply wpU $$ [$Hmb $m] as ⟨Hmb, %st', Hm', %Hw'⟩
      have Heq := pbMessage_wire_eq Hw0 Hw'
      have Hwo : wireOf st' = wireOf st0 := by
        obtain ⟨a, b, c, d⟩ := Heq
        simp only [wireOf, a, b, c, d]
      (try wp_auto)
      wp_apply wp_GetTerm.1 m_ptr (DFrac.own 1) (DFrac.own 1) true st' $$ [$Hm'] as Hm'
      (try wp_auto)
      wp_apply wp_GetIndex.1 m_ptr (DFrac.own 1) (DFrac.own 1) true st' $$ [$Hm'] as Hm'
      (try wp_auto)
      ihave ⟨%es, %els, HEs, Hes, #Hents, Hclose⟩ :=
        msgPtsC_ents_acc m_ptr (DFrac.own 1) (DFrac.own 1) true st' $$ Hm'
      ihave %Hesl := ownSlice_len _ _ _ $$ Hes
      ihave %Hel := BigSepL2.bigSepL2_length $$ Hents
      (try wp_auto)
      wp_join iprop(∃ ix : w64, dec_ptr ↦ dec ∗ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"index"] ↦ ix ∗
          ⌜ix = lastIdx (wireOf st')⌝ ∗
          m_ptr.[raftpb.Message, go!"Entries"] ↦ es ∗ es ↦* els) with [dec Hindex HEs Hes l]
          as ⟨%ix, dec, Hindex, %Hix, HEs, Hes⟩
      · (try wp_auto)
        · have hlen : 0 < sint.Z es.len := Hif
          have hpos : 0 < sint.nat es.len := by
            have h0 : sint.Z (W64 0) = 0 := rfl
            word
          obtain ⟨p, Hp⟩ : ∃ p, els[sint.nat es.len - 1]? = some p :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨e, He⟩ : ∃ e, st'.ents[sint.nat es.len - 1]? = some e :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          ihave #Hep := BigSepL2.bigSepL2_lookup Hp He $$ Hents
          (try wp_auto)
          rw [if_pos (sint_sub_one_bounds hlen)]
          wp_apply (wp_load_slice_index (V := Loc) es _ els (DFrac.own 1) p
            (sint_sub_one_bounds hlen).1) $$ [Hes] as Hes
          · iframe; ipureintro; rw [sint_sub_one_toNat hlen]; exact Hp
          (try wp_auto)
          wp_apply wp_Entry_GetIndex.1 p DFrac.discard e $$ [] as -
          · iexact Hep
          (try wp_auto)
          iframe
          ipureintro
          refine ⟨rfl, ?_⟩
          simp only [lastIdx, wireOf]
          rw [List.getLast?_eq_getElem?, show st'.ents.length - 1 = sint.nat es.len - 1 by omega, He]
      · iexists _; iframe
        ipureintro
        have h0 : sint.Z (W64 0) = 0 := rfl
        have : st'.ents = [] := List.eq_nil_of_length_eq_zero (by word)
        simp [lastIdx, wireOf, this]
      (try wp_auto)
      subst Hix
      ihave Hm' := Hclose $$ HEs Hes
      iapply HΦ
      iexists _, ⟨st'.msg.Term', lastIdx (wireOf st')⟩
      iframe HRd
      isplitl [Hterm Hindex Hbufs Hbufc Hs8s Hs1s]
      · iunfold v2DecOwn
        iexists buf, s8, s1, zs, x8, [W8 2]
        iframe; iframe #; iframe %
      iintro -
      iexists _, _, st'
      iframe Hm' HBb
      ipureintro
      have hmsg : st'.msg = st0.msg := Heq.1
      refine ⟨?_, ?_, rfl⟩
      · rw [Hwo, hmsg]; exact Hfr
      · simp [msgFrame, hyl]
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => dec_err cst, zs, x8, [W8 2]

end proof

end EtcdGrove
end Perennial
