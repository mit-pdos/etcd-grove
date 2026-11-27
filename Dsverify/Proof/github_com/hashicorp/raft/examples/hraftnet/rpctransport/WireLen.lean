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

theorem encAEReq_length (v : AEReqV)
    (h : aeBoundN v.hdr.id v.hdr.addr v.leader v.ents ≤ maxReqN) :
    (encAEReq v).length ≤ net.rpc.maxFrameN := by
  sorry

theorem encVoteReq_length (v : VoteReqV)
    (h : voteBoundN v.hdr.id v.hdr.addr v.cand ≤ maxReqN) :
    (encVoteReq v).length ≤ net.rpc.maxFrameN := by
  sorry

theorem encPreVoteReq_length (v : PreVoteReqV)
    (h : preVoteBoundN v.hdr.id v.hdr.addr ≤ maxReqN) :
    (encPreVoteReq v).length ≤ net.rpc.maxFrameN := by
  sorry

theorem encSnapReq_length (v : SnapReqV)
    (h : snapBoundN v.hdr.id v.hdr.addr v.leader v.peers v.cfg v.data ≤ maxReqN) :
    (encSnapReq v).length ≤ net.rpc.maxFrameN := by
  sorry

theorem encTimeoutReq_length (hd : HdrV) (h : timeoutBoundN hd.id hd.addr ≤ maxReqN) :
    (encTimeoutReq hd).length ≤ net.rpc.maxFrameN := by
  sorry

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
