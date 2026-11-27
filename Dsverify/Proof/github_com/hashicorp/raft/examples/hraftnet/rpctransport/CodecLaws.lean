/-
What the hraft kit transport's sender needs of the program's net/rpc codec (`rpctransport`,
notes/dsv-hraft.md, S4): a request struct encodes to its wire value's encoding (`WireEnc.lean`), and
an answer's encoding decodes into a fresh reply struct as that answer. The codec is the kit's
generated one (`examples/hraftnet/rpc_gen.go`), registered by package `hraftnet`; these laws are
stated over any `CodecSpec`, taken by the transport's specs, and proved of the generated codec in
`hraftnet`'s proofs (the receiver's side, decoding the requests and encoding the answers, is part of
the receiver's `methodOk`, also `hraftnet`'s).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireEnc
public import Net.Proof.net.rpc.Codec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Ownership of the wire structs, by their values -/

def hdrOwn (h : Header) (dq : DFrac) (v : HdrV) : IProp GF :=
  iprop(⌜h.ProtocolVersion' = v.pv⌝ ∗ h.ID' ↦*{dq} v.id ∗ h.Addr' ↦*{dq} v.addr)

def aeReqOwn (w : AppendReq) (dq : DFrac) (v : AEReqV) : IProp GF :=
  iprop(⌜w.Term' = v.term ∧ w.PrevLogEntry' = v.prev ∧ w.PrevLogTerm' = v.prevTerm ∧
      w.LeaderCommitIndex' = v.lci⌝ ∗
    hdrOwn w.Hdr' dq v.hdr ∗ w.Leader' ↦*{dq} v.leader ∗ entsOwn w.Entries' dq v.ents)

def aeRespOwn (w : AppendResp) (dq : DFrac) (v : AERespV) : IProp GF :=
  iprop(⌜w.Failed' = v.failed ∧ w.Err' = v.err ∧ w.Term' = v.term ∧ w.LastLog' = v.lastLog ∧
      w.Success' = v.success ∧ w.NoRetryBackoff' = v.noRetry⌝ ∗ hdrOwn w.Hdr' dq v.hdr)

def voteReqOwn (w : VoteReq) (dq : DFrac) (v : VoteReqV) : IProp GF :=
  iprop(⌜w.Term' = v.term ∧ w.LastLogIndex' = v.lastIdx ∧ w.LastLogTerm' = v.lastTerm ∧
      w.LeadershipTransfer' = v.transfer⌝ ∗ hdrOwn w.Hdr' dq v.hdr ∗ w.Candidate' ↦*{dq} v.cand)

def voteRespOwn (w : VoteResp) (dq : DFrac) (v : VoteRespV) : IProp GF :=
  iprop(⌜w.Failed' = v.failed ∧ w.Err' = v.err ∧ w.Term' = v.term ∧ w.Granted' = v.granted⌝ ∗
    hdrOwn w.Hdr' dq v.hdr ∗ w.Peers' ↦*{dq} v.peers)

def preVoteReqOwn (w : PreVoteReq) (dq : DFrac) (v : PreVoteReqV) : IProp GF :=
  iprop(⌜w.Term' = v.term ∧ w.LastLogIndex' = v.lastIdx ∧ w.LastLogTerm' = v.lastTerm⌝ ∗
    hdrOwn w.Hdr' dq v.hdr)

def preVoteRespOwn (w : PreVoteResp) (dq : DFrac) (v : PreVoteRespV) : IProp GF :=
  iprop(⌜w.Failed' = v.failed ∧ w.Err' = v.err ∧ w.Term' = v.term ∧ w.Granted' = v.granted⌝ ∗
    hdrOwn w.Hdr' dq v.hdr)

def snapReqOwn (w : SnapReq) (dq : DFrac) (v : SnapReqV) : IProp GF :=
  iprop(⌜w.SnapshotVersion' = v.version ∧ w.Term' = v.term ∧ w.LastLogIndex' = v.lastIdx ∧
      w.LastLogTerm' = v.lastTerm ∧ w.ConfigurationIndex' = v.cfgIdx ∧ w.Size' = v.size⌝ ∗
    hdrOwn w.Hdr' dq v.hdr ∗ w.Leader' ↦*{dq} v.leader ∗ w.Peers' ↦*{dq} v.peers ∗
    w.Configuration' ↦*{dq} v.cfg ∗ w.Data' ↦*{dq} v.data)

def snapRespOwn (w : SnapResp) (dq : DFrac) (v : SnapRespV) : IProp GF :=
  iprop(⌜w.Failed' = v.failed ∧ w.Err' = v.err ∧ w.Term' = v.term ∧ w.Success' = v.success⌝ ∗
    hdrOwn w.Hdr' dq v.hdr)

def timeoutRespOwn (w : TimeoutResp) (dq : DFrac) (v : TimeoutRespV) : IProp GF :=
  iprop(⌜w.Failed' = v.failed ∧ w.Err' = v.err⌝ ∗ hdrOwn w.Hdr' dq v.hdr)

/-! ## The laws -/

/-- A pointer to a struct as an interface value. -/
abbrev ptrI (t : go.GoType) (p : Loc) : GoInterface := interface.mkOk (go.GoType.PointerType t) #p

/-- Encoding a request struct gives its value's encoding (its memory untouched). -/
abbrev encLaw {T V : Type} [TypedPointsto (GF := GF) T] (C : net.rpc.CodecSpec GF) (t : go.GoType)
    (own : T → DFrac → V → IProp GF) (enc : V → List w8) : Prop :=
  ∀ (p : Loc) (dq : DFrac) (w : T) (v : V) (Ψ : List w8 → IProp GF),
    p ↦{dq} w ∗ own w dq v ∗ (p ↦{dq} w -∗ own w dq v -∗ Ψ (enc v)) ⊢ C.enc (ptrI t p) Ψ

/-- Decoding an answer's encoding into a zero reply struct succeeds, with that answer. -/
abbrev decLaw {T V : Type} [TypedPointsto (GF := GF) T] [ZeroVal T] (C : net.rpc.CodecSpec GF)
    (t : go.GoType) (own : T → DFrac → V → IProp GF) (enc : V → List w8) : Prop :=
  ∀ (p : Loc) (v : V) (Ψ : Bool → IProp GF),
    p ↦ (zero_val T) ∗ (∀ w : T, p ↦ w -∗ own w (DFrac.own 1) v -∗ Ψ true) ⊢
      C.dec (enc v) (ptrI t p) Ψ

/-- **The sender's codec laws** of the codec `C`. -/
structure CodecLaws (C : net.rpc.CodecSpec GF) : Prop where
  enc_AppendReq : encLaw C AppendReq.ty aeReqOwn encAEReq
  enc_VoteReq : encLaw C VoteReq.ty voteReqOwn encVoteReq
  enc_PreVoteReq : encLaw C PreVoteReq.ty preVoteReqOwn encPreVoteReq
  enc_SnapReq : encLaw C SnapReq.ty snapReqOwn encSnapReq
  enc_TimeoutReq : encLaw C TimeoutReq.ty (fun (w : TimeoutReq) dq h => hdrOwn (GF := GF) w.Hdr' dq h) encTimeoutReq
  dec_AppendResp : decLaw C AppendResp.ty aeRespOwn encAEResp
  dec_VoteResp : decLaw C VoteResp.ty voteRespOwn encVoteResp
  dec_PreVoteResp : decLaw C PreVoteResp.ty preVoteRespOwn encPreVoteResp
  dec_SnapResp : decLaw C SnapResp.ty snapRespOwn encSnapResp
  dec_TimeoutResp : decLaw C TimeoutResp.ty timeoutRespOwn encTimeoutResp

end laws

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
