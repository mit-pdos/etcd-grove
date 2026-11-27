/-
The size check's soundness (the hraft kit transport, notes/dsv-hraft.md, S4): a request whose
wire-size bound (`Wire.lean`'s `*BoundN`, what `*ReqBound` computes) is at most `MaxRequest` has an
encoding (`WireEnc.lean`, the generated codec's) that fits the net/rpc model's frame (`maxFrameN`),
so `Conn.Call` may send it.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireEnc
public import Net.Proof.net.rpc.Base

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-! ## Lengths of the pieces -/

theorem flat8 (s : List w8) :
    ((s.map fun b => u64Le (W64 (uint.Z b))).flatten).length = 8 * s.length := by
  induction s with
  | nil => simp
  | cons b s ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, u64Le_length, ih,
      List.length_cons]
    omega

theorem fld_le (sent : Bool) (b : List w8) : (fld sent b).length ≤ b.length + 1 := by
  unfold fld; split <;> simp

theorem fU64_le (x : w64) : (fU64 x).length ≤ 9 :=
  Nat.le_trans (fld_le _ _) (by simp only [encU64, u64Le_length]; omega)

theorem fU8_le (x : w8) : (fU8 x).length ≤ 9 :=
  Nat.le_trans (fld_le _ _) (by simp only [encU64, u64Le_length]; omega)

theorem fBool_le (b : Bool) : (fBool b).length ≤ 2 :=
  Nat.le_trans (fld_le _ _) (by simp only [encBool, List.length_cons, List.length_nil]; omega)

theorem fBytes_le (s : List w8) : (fBytes s).length ≤ 9 + 8 * s.length :=
  Nat.le_trans (fld_le _ _) (by simp only [encBytes, List.length_append, u64Le_length, flat8]; omega)

theorem fStruct_len (b : List w8) : (fStruct b).length = b.length + 1 := by
  simp [fStruct, fld]

theorem encHdr_le (h : HdrV) : (encHdr h).length ≤ 28 + 8 * h.id.length + 8 * h.addr.length := by
  have := fU64_le h.pv
  have := fBytes_le h.id
  have := fBytes_le h.addr
  simp only [encHdr, strct, List.flatten_cons, List.flatten_nil, List.length_cons,
    List.length_append, List.length_nil, List.append_nil]
  omega

theorem encEnt_le (e : EntV) : (encEnt e).length ≤ 46 + 8 * e.data.length + 8 * e.ext.length := by
  have := fU64_le e.index
  have := fU64_le e.term
  have := fU8_le e.ty
  have := fBytes_le e.data
  have := fBytes_le e.ext
  simp only [encEnt, strct, List.flatten_cons, List.flatten_nil, List.length_cons,
    List.length_append, List.length_nil, List.append_nil]
  omega

theorem fEnts_le (es : List EntV) : (fEnts es).length ≤ 9 + ((es.map encEnt).flatten).length :=
  Nat.le_trans (fld_le _ _) (by simp only [encU64, List.length_append, u64Le_length]; omega)

/-! ## The bounds -/

theorem bb_small (n : Nat) (h : bytesBoundN n ≤ maxReqN) : bytesBoundN n = 17 + 8 * n := by
  by_cases hn : maxReqN < n
  · simp only [bytesBoundN, if_pos hn] at h; omega
  · simp only [bytesBoundN, if_neg hn]

theorem entsBoundN_ge (n : Nat) (vs : List EntV) : n ≤ entsBoundN n vs := by
  induction vs generalizing n with
  | nil => exact Nat.le_refl _
  | cons v vs ih =>
    rw [entsBoundN_cons]
    split
    · exact Nat.le_refl _
    · have := ih (n + 64 + bytesBoundN v.data.length + bytesBoundN v.ext.length)
      omega

theorem entsLen_le (n : Nat) (vs : List EntV) (h : entsBoundN n vs ≤ maxReqN) :
    n + ((vs.map encEnt).flatten).length ≤ entsBoundN n vs := by
  induction vs generalizing n with
  | nil => simp [entsBoundN]
  | cons v vs ih =>
    rw [entsBoundN_cons] at h ⊢
    by_cases hn : maxReqN < n
    · rw [if_pos hn] at h; omega
    · rw [if_neg hn] at h ⊢
      have hge := entsBoundN_ge (n + 64 + bytesBoundN v.data.length + bytesBoundN v.ext.length) vs
      have hd := bb_small v.data.length (by omega)
      have hx := bb_small v.ext.length (by omega)
      have := ih _ h
      have := encEnt_le v
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      omega

theorem maxReqN_eq : maxReqN = 1073741824 := rfl
theorem maxFrameN_eq : net.rpc.maxFrameN = 1073741824 := rfl

/-! ## The size check -/

theorem encAEReq_length (v : AEReqV)
    (h : aeBoundN v.hdr.id v.hdr.addr v.leader v.ents ≤ maxReqN) :
    (encAEReq v).length ≤ net.rpc.maxFrameN := by
  have hM := maxReqN_eq
  have hF := maxFrameN_eq
  unfold aeBoundN at h
  have hge := entsBoundN_ge (128 + hdrBoundN v.hdr.id v.hdr.addr + bytesBoundN v.leader.length + 64) v.ents
  have hE := entsLen_le _ v.ents h
  unfold hdrBoundN at h hge hE
  have ha := bb_small v.hdr.id.length (by omega)
  have hb := bb_small v.hdr.addr.length (by omega)
  have hl := bb_small v.leader.length (by omega)
  have := encHdr_le v.hdr
  have := fU64_le v.term
  have := fBytes_le v.leader
  have := fU64_le v.prev
  have := fU64_le v.prevTerm
  have := fEnts_le v.ents
  have := fU64_le v.lci
  simp only [encAEReq, tagged, encStr, strct, fStruct_len, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil, u64Le_length, List.append_nil]
  omega

theorem encVoteReq_length (v : VoteReqV)
    (h : voteBoundN v.hdr.id v.hdr.addr v.cand ≤ maxReqN) :
    (encVoteReq v).length ≤ net.rpc.maxFrameN := by
  have hM := maxReqN_eq
  have hF := maxFrameN_eq
  unfold voteBoundN hdrBoundN at h
  have ha := bb_small v.hdr.id.length (by omega)
  have hb := bb_small v.hdr.addr.length (by omega)
  have hl := bb_small v.cand.length (by omega)
  have := encHdr_le v.hdr
  have := fU64_le v.term
  have := fBytes_le v.cand
  have := fU64_le v.lastIdx
  have := fU64_le v.lastTerm
  have := fBool_le v.transfer
  simp only [encVoteReq, tagged, encStr, strct, fStruct_len, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil, u64Le_length, List.append_nil]
  omega

theorem encPreVoteReq_length (v : PreVoteReqV)
    (h : preVoteBoundN v.hdr.id v.hdr.addr ≤ maxReqN) :
    (encPreVoteReq v).length ≤ net.rpc.maxFrameN := by
  have hM := maxReqN_eq
  have hF := maxFrameN_eq
  unfold preVoteBoundN hdrBoundN at h
  have ha := bb_small v.hdr.id.length (by omega)
  have hb := bb_small v.hdr.addr.length (by omega)
  have := encHdr_le v.hdr
  have := fU64_le v.term
  have := fU64_le v.lastIdx
  have := fU64_le v.lastTerm
  simp only [encPreVoteReq, tagged, encStr, strct, fStruct_len, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil, u64Le_length, List.append_nil]
  omega

theorem encSnapReq_length (v : SnapReqV)
    (h : snapBoundN v.hdr.id v.hdr.addr v.leader v.peers v.cfg v.data ≤ maxReqN) :
    (encSnapReq v).length ≤ net.rpc.maxFrameN := by
  have hM := maxReqN_eq
  have hF := maxFrameN_eq
  unfold snapBoundN hdrBoundN at h
  have ha := bb_small v.hdr.id.length (by omega)
  have hb := bb_small v.hdr.addr.length (by omega)
  have hl := bb_small v.leader.length (by omega)
  have hp := bb_small v.peers.length (by omega)
  have hc := bb_small v.cfg.length (by omega)
  have hd := bb_small v.data.length (by omega)
  have := encHdr_le v.hdr
  have := fU64_le v.version
  have := fU64_le v.term
  have := fBytes_le v.leader
  have := fU64_le v.lastIdx
  have := fU64_le v.lastTerm
  have := fBytes_le v.peers
  have := fBytes_le v.cfg
  have := fU64_le v.cfgIdx
  have := fU64_le v.size
  have := fBytes_le v.data
  simp only [encSnapReq, tagged, encStr, strct, fStruct_len, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil, u64Le_length, List.append_nil]
  omega

theorem encTimeoutReq_length (hd : HdrV) (h : timeoutBoundN hd.id hd.addr ≤ maxReqN) :
    (encTimeoutReq hd).length ≤ net.rpc.maxFrameN := by
  have hM := maxReqN_eq
  have hF := maxFrameN_eq
  unfold timeoutBoundN hdrBoundN at h
  have ha := bb_small hd.id.length (by omega)
  have hb := bb_small hd.addr.length (by omega)
  have := encHdr_le hd
  simp only [encTimeoutReq, tagged, encStr, strct, fStruct_len, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil, u64Le_length, List.append_nil]
  omega

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
