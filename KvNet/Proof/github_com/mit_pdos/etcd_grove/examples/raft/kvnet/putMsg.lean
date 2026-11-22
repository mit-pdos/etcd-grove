/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/putMsg.lean`: the getters
read the message's scalars, reject and context, each written with `putUint64`/`putBytes`; the
entries' number, then each entry (`putEntry`, read-only: `entRO`) in a loop over `GetEntries`'
slice, given back after; the `Snapshot` field read directly (`msgPtsC`'s `snapOpt`): `0`, or `1`
and `putSnapshot`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putMsg
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putUint64
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putBytes
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putEntry
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putSnapshot
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetVote
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetRejectHint
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- The `Snapshot` field of a message, lent (`putMsg` reads the pointer, then the snapshot
behind it). -/
private theorem msgPtsC_Snapshot_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Snapshot"] ↦{dq} p ∗ snapOpt p dq ms.snap ∗
        (l.[raftpb.Message, go!"Snapshot"] ↦{dq} p -∗ snapOpt p dq ms.snap -∗
          msgPtsC l dq dqe cap ms) := by
  iintro H
  iunfold msgPtsC at H
  iNamed H
  iexists ps
  iframe HSn Hsn
  iintro HSn Hsn
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- A snapshot's pointer is not `nil` (kept). -/
private theorem ownSnapM_nn (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapM (GF := GF) p dq s ⊢ ⌜p ≠ null⌝ ∗ ownSnapM p dq s := by
  iintro H
  iunfold ownSnapM at H
  iNamed H
  isplitr
  · ipureintro; exact Hnn
  iunfold ownSnapM
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hm Hpb

theorem putMsg.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG))
    (wp_putBytes : putBytes.spec (GF := GF) (hG := hG))
    (wp_putEntry : putEntry.spec (GF := GF) (hG := hG))
    (wp_putSnapshot : putSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.Message.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_GetRejectHint : raftpb.Message.GetRejectHint.spec (GF := GF) (hG := hG))
    (wp_GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG))
    (wp_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG)) :
    putMsg.spec (GF := GF) (hG := hG) := by
  intro buf B l dq dqe cap st
  wp_start as ⟨Hbuf, Hcap, Hm⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_GetType.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  try wp_auto
  wp_apply wp_putUint64 buf B _ $$ [$Hbuf $Hcap] as %b1 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetTo.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b1 _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetFrom.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b2 _ _ $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetTerm.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b3 _ _ $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetLogTerm.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b4 _ _ $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetIndex.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b5 _ _ $$ [$Hb $Hcap] as %b6 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetCommit.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b6 _ _ $$ [$Hb $Hcap] as %b7 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetVote.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_apply wp_putUint64 b7 _ _ $$ [$Hb $Hcap] as %b8 ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply wp_GetReject.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
  cases Hrj : st.msg.Reject'
  all_goals (
    try wp_auto
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b9 ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_GetRejectHint.1 l dq dqe cap st $$ [$Hpb $Hm] as Hm
    wp_apply wp_putUint64 b9 _ _ $$ [$Hb $Hcap] as %b10 ⟨Hb, Hcap⟩
    try wp_auto
    wp_apply wp_GetContext.1 l dq dqe cap st $$ [$Hpb $Hm] as %cs ⟨#Hcs, Hm⟩
    wp_apply wp_putBytes b10 cs _ _ DFrac.discard $$ [$Hb $Hcap $Hcs] as %b11 ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_GetEntries.1 l dq dqe cap st $$ [$Hpb $Hm] as %es %els ⟨Hes, #Hbig, Hesc, Hback⟩
    ihave %Hbl := entsBig_length $$ Hbig
    ihave %Hlen := ownSlice_len $$ Hes
    ihave Hm := Hback $$ %cap %els %st.ents Hes Hbig Hesc
    try wp_auto
    wp_apply wp_putUint64 b11 _ _ $$ [$Hb $Hcap] as %b12 ⟨Hb, Hcap⟩
    first
      | rw [show ([W8 0] : List w8) = [boolB st.msg.Reject'] by simp [Hrj, boolB, autoB]]
      | rw [show ([W8 1] : List w8) = [boolB st.msg.Reject'] by simp [Hrj, boolB, autoB]]
    generalize HB0 : B ++ u64Le (W64 (sint.Z st.msg.Type')) ++ u64Le st.msg.To' ++
      u64Le st.msg.From' ++ u64Le st.msg.Term' ++ u64Le st.msg.LogTerm' ++ u64Le st.msg.Index' ++
      u64Le st.msg.Commit' ++ u64Le st.msg.Vote' ++ [boolB st.msg.Reject'] ++
      u64Le st.msg.RejectHint' ++ putB st.ctx ++ u64Le es.len = B0
    try wp_auto
    wp_apply wp_GetEntries.1 l dq dqe cap st $$ [$Hpb $Hm] as %es2 %els2 ⟨Hes2, #Hbig2, Hesc2, Hback2⟩
    ihave %Hbl2 := entsBig_length $$ Hbig2
    ihave %Hlen2 := ownSlice_len $$ Hes2
    try wp_auto
    -- the entries, in order
    ihave IH : iprop(∃ (j : w64) (bv : GoSlice) (x : Loc),
        "i" ∷ i_ptr ↦ j ∗ "buf" ∷ buf_ptr ↦ bv ∗
        "Hb" ∷ bv ↦* (B0 ++ encEntries (st.ents.take (sint.nat j))) ∗
        "Hcap" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "e" ∷ e_ptr ↦ x ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z es2.len⌝)
      $$ [i buf Hb Hcap e]
    · iexists W64 0, b12, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, encEntries, List.append_nil]
      iframe
      ipureintro; exact ⟨by decide, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.Z j < sint.Z es2.len := by
        exact Hif
      have Hjl : sint.nat j < st.ents.length := by rw [← Hbl2, Hlen2.1]; word
      obtain ⟨x0, Hx0⟩ : ∃ x0, st.ents[sint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
      icases entsBig_lookup els2 st.ents (sint.nat j) x0 Hx0 $$ Hbig2 with ⟨%le, %Hle, #Hel⟩
      try wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z es2.len from ⟨Hj.1, Hlt⟩)]
      wp_apply wp_load_slice_index es2 (sint.Z j) els2 dqe le Hj.1 $$ [$Hes2] as Hes2
      · ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hle
      try wp_auto
      wp_apply wp_putEntry bv _ le DFrac.discard x0 $$ [$Hb $Hcap $Hel] as %b13 ⟨Hb, Hcap, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, b13, le
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have Htk : st.ents.take (sint.nat j + 1) = st.ents.take (sint.nat j) ++ [x0] := by
        rw [List.take_add_one, Hx0]; rfl
      rw [Hj1, Htk, encEntries_snoc]
      simp only [List.append_assoc]
      iframe
      ipureintro; constructor <;> word
    · have Hge : ¬ sint.Z j < sint.Z es2.len := by
        exact Hif
      try simp only [decide_eq_false Hge, _root_.decide_true, ↓reduceIte]
      have Hjk : sint.nat j = st.ents.length := by rw [← Hbl2, Hlen2.1]; word
      rw [Hjk, List.take_length]
      ihave Hm := Hback2 $$ %cap %els2 %st.ents Hes2 Hbig2 Hesc2
      icases msgPtsC_Snapshot_acc _ _ _ _ _ $$ Hm with ⟨%ps, HSn, Hsn, Hmb⟩
      have Hxl : es.len = W64 st.ents.length := by rw [← Hbl, Hlen.1]; have := Hlen.2; word
      subst HB0
      cases Hs : st.snap with
      | none =>
        simp only [Hs, snapOpt]
        icases Hsn with %Hps
        subst Hps
        try wp_auto
        wp_apply wp_slice_literal (V := w8) [_]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b14 ⟨Hb, Hcap, -⟩
        try wp_auto
        iapply HΦ
        ihave Hm := Hmb $$ HSn []
        · simp only [Hs, snapOpt]
          first | (ipureintro; rfl) | ipureintro; trivial
        iframe Hcap
        isplitl [Hb]
        · simp only [encMsg, encSnapOpt, Hs, Hxl, List.append_assoc, List.cons_append, List.nil_append]
          iexact Hb
        rw [show (⟨st.msg, st.ents, none, st.ctx, st.resps⟩ : MsgSt) = st from by rw [← Hs]] at *
        iexact Hm
      | some s =>
        simp only [Hs, snapOpt]
        icases ownSnapM_nn _ _ _ $$ Hsn with ⟨%Hpn, Hsn⟩
        try wp_auto
        rw [decide_eq_false Hpn]
        try wp_auto
        wp_apply wp_slice_literal (V := w8) [_]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl2] as %b14 ⟨Hb, Hcap, -⟩
        try wp_auto
        wp_apply wp_putSnapshot b14 _ ps dq s $$ [$Hb $Hcap $Hsn] as %b15 ⟨Hb, Hcap, Hsn⟩
        try wp_auto
        iapply HΦ
        ihave Hm := Hmb $$ HSn Hsn
        iframe Hcap
        isplitl [Hb]
        · simp only [encMsg, encSnapOpt, Hs, Hxl, List.append_assoc, List.cons_append, List.nil_append]
          iexact Hb
        rw [show (⟨st.msg, st.ents, some s, st.ctx, st.resps⟩ : MsgSt) = st from by rw [← Hs]] at *
        iexact Hm)

end proof

end raft_kvnet
end EtcdGrove
end Perennial
