/-
# `v3electionpb`'s messages (batch 3h, round 1: 2e's request 2)

The election service's messages (`server/etcdserver/api/v3election/v3electionpb`, translated with
its getters), owned as 2e's provisional predicates in `V3election`'s `Api.lean` said, same
signatures: the read-only requests `campaignReq`, `proclaimReq`, `resignReq`, `leaderReq`
(persistent, as gRPC hands them to the handler) and the fresh replies `campaignResp`, `proclaimResp`,
`resignResp`, `leaderResp`. `LeaderKeyM` (2e's) moves here with them. Each predicate is
`Proto.msgAt` of a content holding its model; the relations are functional in the content.

Mapping for integration: `V3election.LeaderKeyM` becomes `V3electionpb.LeaderKeyM`; the eight
predicates become these. Intended realization: as `etcdserverpb/Api.lean`'s.
-/
module

public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.go_etcd_io.etcd.api.v3.Wire
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.v3electionpb
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.v3electionpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3electionpb

open Iris Iris.BI EtcdWire
open go_etcd_io.etcd.server.v3.etcdserver.api.v3election

/-- `v3electionpb.LeaderKey` (2e's, moved). -/
structure LeaderKeyM where
  name : GoString
  key : GoString
  rev : w64
  lease : w64

opaque campaignReqHolds (c : Proto.Content) (name : GoString) (lease : w64) (value : GoString) : Prop
opaque proclaimReqHolds (c : Proto.Content) (lk : Option LeaderKeyM) (value : GoString) : Prop
opaque resignReqHolds (c : Proto.Content) (lk : Option LeaderKeyM) : Prop
opaque leaderReqHolds (c : Proto.Content) (name : GoString) : Prop
opaque campaignRespHolds (c : Proto.Content) (lk : LeaderKeyM) : Prop
opaque leaderRespHolds (c : Proto.Content) (v : EtcdModel.KV) : Prop

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def campaignReq (p : Loc) (name : GoString) (lease : w64) (value : GoString) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.CampaignRequest.ty p DFrac.discard c ∗
    ⌜campaignReqHolds c name lease value⌝)
def proclaimReq (p : Loc) (lk : Option LeaderKeyM) (value : GoString) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.ProclaimRequest.ty p DFrac.discard c ∗
    ⌜proclaimReqHolds c lk value⌝)
def resignReq (p : Loc) (lk : Option LeaderKeyM) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.ResignRequest.ty p DFrac.discard c ∗ ⌜resignReqHolds c lk⌝)
def leaderReq (p : Loc) (name : GoString) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.LeaderRequest.ty p DFrac.discard c ∗ ⌜leaderReqHolds c name⌝)
def campaignResp (p : Loc) (lk : LeaderKeyM) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.CampaignResponse.ty p (DFrac.own 1) c ∗ ⌜campaignRespHolds c lk⌝)
def proclaimResp (p : Loc) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.ProclaimResponse.ty p (DFrac.own 1) c)
def resignResp (p : Loc) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.ResignResponse.ty p (DFrac.own 1) c)
def leaderResp (p : Loc) (v : EtcdModel.KV) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3electionpb.LeaderResponse.ty p (DFrac.own 1) c ∗ ⌜leaderRespHolds c v⌝)

/-- A read-only `*LeaderKey` holding `lk` (`nil` for `none`). -/
def leaderKeyRO (p : Loc) : Option LeaderKeyM → IProp GF
  | none => iprop(⌜p = null⌝)
  | some lk => iprop(∃ (ns ks : GoSlice), protoRest v3electionpb.LeaderKey p DFrac.discard ∗
      p.[v3electionpb.LeaderKey, go!"Name"] ↦□ ns ∗ ns ↦*□ lk.name ∗
      p.[v3electionpb.LeaderKey, go!"Key"] ↦□ ks ∗ ks ↦*□ lk.key ∗
      p.[v3electionpb.LeaderKey, go!"Rev"] ↦□ lk.rev ∗
      p.[v3electionpb.LeaderKey, go!"Lease"] ↦□ lk.lease)

def holds_fun.spec : Prop :=
  (∀ c n l v n' l' v', campaignReqHolds c n l v → campaignReqHolds c n' l' v' →
    n = n' ∧ l = l' ∧ v = v') ∧
  (∀ c lk v lk' v', proclaimReqHolds c lk v → proclaimReqHolds c lk' v' → lk = lk' ∧ v = v') ∧
  (∀ c lk lk', resignReqHolds c lk → resignReqHolds c lk' → lk = lk') ∧
  (∀ c n n', leaderReqHolds c n → leaderReqHolds c n' → n = n') ∧
  (∀ c lk lk', campaignRespHolds c lk → campaignRespHolds c lk' → lk = lk') ∧
  (∀ c v v', leaderRespHolds c v → leaderRespHolds c v' → v = v')

/-- **The requests' fields** (the handlers read `req.Name`, `req.Lease`, `req.Value`, `req.Leader`). -/
def reqFields.spec : Prop :=
  (∀ p n l v, campaignReq (GF := GF) p n l v ⊢
    ∃ (ns vs : GoSlice), p.[v3electionpb.CampaignRequest, go!"Name"] ↦□ ns ∗ ns ↦*□ n ∗
      p.[v3electionpb.CampaignRequest, go!"Lease"] ↦□ l ∗
      p.[v3electionpb.CampaignRequest, go!"Value"] ↦□ vs ∗ vs ↦*□ v) ∧
  (∀ p lk v, proclaimReq (GF := GF) p lk v ⊢
    ∃ (lp : Loc) (vs : GoSlice), p.[v3electionpb.ProclaimRequest, go!"Leader"] ↦□ lp ∗
      leaderKeyRO lp lk ∗ p.[v3electionpb.ProclaimRequest, go!"Value"] ↦□ vs ∗ vs ↦*□ v) ∧
  (∀ p lk, resignReq (GF := GF) p lk ⊢
    ∃ lp : Loc, p.[v3electionpb.ResignRequest, go!"Leader"] ↦□ lp ∗ leaderKeyRO lp lk) ∧
  (∀ p n, leaderReq (GF := GF) p n ⊢
    ∃ ns : GoSlice, p.[v3electionpb.LeaderRequest, go!"Name"] ↦□ ns ∗ ns ↦*□ n)

/-- **Building the replies** (`&v3electionpb.CampaignResponse{Header: ..., Leader: &LeaderKey{...}}`,
`LeaderResponse{Header, Kv}`, `ProclaimResponse{Header}`, `ResignResponse{Header}`): fresh
bookkeeping, an owned header or `nil`, the leader key or key-value as read-only messages. -/
def resp_fold.spec : Prop :=
  (∀ (p h lp : Loc) (ho : Option HeaderM) (lk : LeaderKeyM),
    protoRest (GF := GF) v3electionpb.CampaignResponse p (DFrac.own 1) ∗
      p.[v3electionpb.CampaignResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[v3electionpb.CampaignResponse, go!"Leader"] ↦ lp ∗ leaderKeyRO lp (some lk) ⊢
    campaignResp p lk) ∧
  (∀ (p h kp : Loc) (ho : Option HeaderM) (v : EtcdModel.KV),
    protoRest (GF := GF) v3electionpb.LeaderResponse p (DFrac.own 1) ∗
      p.[v3electionpb.LeaderResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[v3electionpb.LeaderResponse, go!"Kv"] ↦ kp ∗ keyValueOwn kp DFrac.discard (KeyValueM.ofKV v) ⊢
    leaderResp p v) ∧
  (∀ (p h : Loc) (ho : Option HeaderM),
    protoRest (GF := GF) v3electionpb.ProclaimResponse p (DFrac.own 1) ∗
      p.[v3electionpb.ProclaimResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ⊢
    proclaimResp p) ∧
  (∀ (p h : Loc) (ho : Option HeaderM),
    protoRest (GF := GF) v3electionpb.ResignResponse p (DFrac.own 1) ∗
      p.[v3electionpb.ResignResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ⊢
    resignResp p)

end res

end V3electionpb
end EtcdGrove
end Perennial
