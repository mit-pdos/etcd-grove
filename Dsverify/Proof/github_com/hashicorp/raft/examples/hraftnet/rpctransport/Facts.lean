/-
The facts the hraft kit transport's RPCs carry across the network (`rpctransport`, notes/dsv-hraft.md,
S4): the lab's message predicates (`iface/Net.lean`: `aeReq`, `aeResp`, `rvReq`, ...) restated over the
wire values (`WireEnc.lean`) instead of raft's heap structs, and **the service spec of a server's
`RaftRPC` receiver** (`raftSvc`), the net/rpc world's spec at that server's address: each method's
deposit is the encoding of a valid request with its facts, and the answers the receiving raft's
response facts or an error. A receiver rebuilds the lab's predicates over the fresh structs it decodes
into; a sender gets the responder's facts back from the reply's encoding.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireEnc
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net
public import Net.Proof.net.rpc.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-! ## Pure facts -/

/-- The wire entries `vs` are the protocol entries `ents` at Raft indexes `prev+1..` (`logIs`'s
pure part: index, term, type, data). -/
def entsMatch (vs : List EntV) (prev : Nat) (ents : RLog) : Prop :=
  vs.length = ents.length ∧ ∀ j v e, vs[j]? = some v → ents[j]? = some e →
    uint.nat v.index = prev + 1 + j ∧ uint.nat v.term = e.term ∧ uint.nat v.ty = e.kind ∧ v.data = e.data

/-- A wire header of sender `snd` (`hdrOk`'s pure part: version 3, `ID` and `Addr` its id). -/
def hdrIs (h : HdrV) (snd : SID) : Prop := h.pv = W64 3 ∧ h.id = snd ∧ h.addr = snd

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-! ## Requests and responses on the wire -/

/-- `aeReq` over the wire request `v`. -/
def aeReqW (γ : GNames) (v : AEReqV) (snd : SID) (T prev pt : Nat) (ents : RLog) (lci : Nat)
    (ss : Snap) : IProp GF :=
  iprop(⌜uint.nat v.term = T ∧ uint.nat v.prev = prev ∧ uint.nat v.prevTerm = pt ∧
      uint.nat v.lci = lci ∧ hdrIs v.hdr snd ∧ v.leader = snd ∧ entsMatch v.ents prev ents⌝ ∗
    aeValid γ T prev pt ents lci ∗ histLb γ ss)

/-- `aeResp` over the wire answer `r` (any failure: the receiver's error). -/
def aeRespW (γ : GNames) (r : AERespV) (j : SID) (T k : Nat) (hb : Prop) (ss : Snap) : IProp GF :=
  iprop(⌜r.failed = true⌝ ∨ ⌜r.failed = false⌝ ∗ termOk γ (uint.nat r.term) ∗
    (⌜r.success = false⌝ ∨ (⌜hb⌝ ∨ ackIs γ j T k) ∗ respWit γ j T ss) ∗
    ⌜∃ snd : SID, hdrIs r.hdr snd⌝)

/-- `rvReq` over the wire request `v`. -/
def rvReqW (γ : GNames) (v : VoteReqV) (c : SID) (T li lt : Nat) : IProp GF :=
  iprop(⌜uint.nat v.term = T ∧ uint.nat v.lastIdx = li ∧ uint.nat v.lastTerm = lt ∧ hdrIs v.hdr c ∧
      v.cand = c⌝ ∗ candIs γ c T li lt)

/-- `rvResp` over the wire answer `r`. -/
def rvRespW (γ : GNames) (r : VoteRespV) (j c : SID) (T : Nat) : IProp GF :=
  iprop(⌜r.failed = true⌝ ∨ ⌜r.failed = false⌝ ∗ termOk γ (uint.nat r.term) ∗
    (⌜r.granted = false⌝ ∨ voteIs γ j T c) ∗ ⌜∃ snd : SID, hdrIs r.hdr snd⌝)

/-- `pvReq` over the wire request `v`. -/
def pvReqW (v : PreVoteReqV) (c : SID) (T : Nat) : Prop := uint.nat v.term = T ∧ hdrIs v.hdr c

/-- `pvResp` over the wire answer `r`. -/
def pvRespW (γ : GNames) (r : PreVoteRespV) (T : Nat) : IProp GF :=
  iprop(⌜r.failed = true⌝ ∨ ⌜r.failed = false⌝ ∗
    (⌜uint.nat r.term = T⌝ ∨ termOk γ (uint.nat r.term)) ∗ ⌜∃ snd : SID, hdrIs r.hdr snd⌝)

/-- `isReq` over the wire request `v` (the snapshot's bytes `v.data`, with their meaning `snapP`). -/
def isReqW (γ : GNames) (snapP : Nat → List w8 → IProp GF) (v : SnapReqV) (snd j : SID)
    (T s st : Nat) : IProp GF :=
  iprop(⌜uint.nat v.term = T ∧ uint.nat v.lastIdx = s ∧ uint.nat v.lastTerm = st ∧
      v.version = W64 1 ∧ uint.nat v.size = v.data.length ∧ snd ≠ j ∧ 1 ≤ s ∧ hdrIs v.hdr snd ∧
      v.leader = snd ∧ v.data.length < 2 ^ 63⌝ ∗
    (∃ ss : List Server, ⌜v.cfg = encodeServers ss⌝ ∗ snapCfg γ s (uint.nat v.cfgIdx) ss) ∗
    leaderIs γ T snd ∗ aeValid γ T s st [] s ∗ snapP s v.data)

/-- `isResp` over the wire answer `r`. -/
def isRespW (γ : GNames) (r : SnapRespV) : IProp GF :=
  iprop(⌜r.failed = true⌝ ∨ ⌜r.failed = false⌝ ∗ termOk γ (uint.nat r.term))

/-- `tnReq` over the wire header `h`. -/
def tnReqW (h : HdrV) (c : SID) : Prop := hdrIs h c

/-! ## The service spec of server `j`'s `RaftRPC` -/

/-- A deposit's answers: the success answers `ok` (a reply encoding and its facts), or any
error message (the server's own errors, net/rpc's `errOk`). -/
def answers (ok : List w8 → IProp GF) (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop((∀ rep, ok rep -∗ Φ rep []) ∗ (∀ msg : GoString, ⌜msg ≠ []⌝ -∗ Φ [] msg))

/-- **The service spec of server `j`'s `RaftRPC` receiver** (`snapP`, the FSMs' snapshot meaning):
per method, the deposit of a valid request's encoding, whose success answers are the encodings of
`j`'s answers with their facts. -/
def raftSvc (γ : GNames) (snapP : Nat → List w8 → IProp GF) (j : SID) : net.rpc.MethodSpec GF :=
  fun m bs Φ =>
    if m = go!"AppendEntries" then
      iprop(∃ (v : AEReqV) (snd : SID) (T prev pt : Nat) (ents : RLog) (lci : Nat) (ss : Snap),
        ⌜bs = encAEReq v⌝ ∗ aeReqW γ v snd T prev pt ents lci ss ∗
        answers (fun rep => iprop(∃ r : AERespV, ⌜rep = encAEResp r⌝ ∗
          aeRespW γ r j T (prev + ents.length) (isHb prev ents lci) ss)) Φ)
    else if m = go!"RequestVote" then
      iprop(∃ (v : VoteReqV) (c : SID) (T li lt : Nat),
        ⌜bs = encVoteReq v⌝ ∗ rvReqW γ v c T li lt ∗
        answers (fun rep => iprop(∃ r : VoteRespV, ⌜rep = encVoteResp r⌝ ∗ rvRespW γ r j c T)) Φ)
    else if m = go!"RequestPreVote" then
      iprop(∃ (v : PreVoteReqV) (c : SID) (T : Nat),
        ⌜bs = encPreVoteReq v ∧ pvReqW v c T⌝ ∗
        answers (fun rep => iprop(∃ r : PreVoteRespV, ⌜rep = encPreVoteResp r⌝ ∗ pvRespW γ r T)) Φ)
    else if m = go!"InstallSnapshot" then
      iprop(∃ (v : SnapReqV) (snd : SID) (T s st : Nat),
        ⌜bs = encSnapReq v⌝ ∗ isReqW γ snapP v snd j T s st ∗
        answers (fun rep => iprop(∃ r : SnapRespV, ⌜rep = encSnapResp r⌝ ∗ isRespW γ r)) Φ)
    else if m = go!"TimeoutNow" then
      iprop(∃ (h : HdrV) (c : SID),
        ⌜bs = encTimeoutReq h ∧ tnReqW h c⌝ ∗
        answers (fun rep => iprop(∃ r : TimeoutRespV, ⌜rep = encTimeoutResp r⌝)) Φ)
    else iprop(False)

end facts

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
