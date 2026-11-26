/-
**The vocabulary of `WatchOn_dist`** (the auth-on cross-machine watch, `Spec/.../dist/WatchOnDist.lean`;
`notes/etcd-dist-plan.md` §29): what its caller gives of the members' auth state and of its context's
tokens, and what a response with events tells it of the watch's check. Written in F7's vocabulary
(`AuthViewDist.lean`: `servedBy`, `userOk`, `outTokOk`, `authFloorD`). Definitions only. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist
public import Proof.go_etcd_io.etcd.client.v3.StreamKey
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **No context of the watch's stream key carries an issued token** (pure): `outTokOk` of every outgoing
metadata `m` with the stream key of the watch's own `om`. The watcher shares one gRPC stream among the
watches whose contexts have the same stream key (`streamKeyFromCtx`, `streamKeyOf`), and the server checks a
create for the token of the stream's metadata, which is some context's of that key, not necessarily the
watch's: the key is `fmt`'s `%+v` of the map and collides (`nonissues/etcd-watch-stream-key-collision.md`:
`{"x": ["1] token:[t"]}` prints as `{"x": ["1"], "token": ["t"]}` does), so `outTokOk P om` alone would let a
watch join a stream another watch opened with an issued token of another user. -/
def outTokOkS [GooseExts] (P : Option GoString) (om : GrpcMd) : Prop :=
  ∀ m : GrpcMd, streamKeyOf m = streamKeyOf om → outTokOk P m

/-- No outgoing metadata: only `none` has its stream key (`streamKeyOf_none`), and it sends no token. -/
theorem outTokOkS_none [GooseExts] (P : Option GoString) : outTokOkS P none := by
  intro m hm
  rw [streamKeyOf_none m hm]
  exact outTokOk_none P

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Every endpoint's member has applied the requested prefix `L₀`** (persistent): at each endpoint `a`,
the member `mid` of `Γ` it serves has a published auth index `m` whose floor is above `L₀`
(`authFloorD Γ γR mid L₀ m`: every auth state it records from the floor's index on is the history's after a
committed prefix extending `L₀`). What a linearizable read through that endpoint leaves (`KV_GetOn_dist`'s
`readCheckedD`): the auth workload's barriers, one per member. -/
def watchFloorsD [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (L₀ : List EntryModel) : IProp GF :=
  iprop([∗list] a ∈ eps, ∃ (mid : w64) (m : Nat),
    etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid ∗ authFloorD Γ γR mid L₀ m)

instance watchFloorsD_persistent [NetProtoGS] (eps : List GoString) (Γ : DistView)
    (γR : ServerRaftNames) (L₀ : List EntryModel) :
    Persistent (watchFloorsD (GF := GF) eps Γ γR L₀) := by
  unfold watchFloorsD authFloorD; infer_instance

/-- **A watch's check, at the cluster** (persistent; `watchCheckOk` across machines, at the view): the
create that the response's gRPC stream carried was checked by member `mid` of the endpoints, for an
`AuthInfo` whose user principal `P` may be bound to (`userOk`: the empty user or `P`'s name; no token or TLS
identity named), and the check passed at the auth history after a committed prefix `L` extending the caller's
`L₀` (`srvReqLogLb γR L`): that state permits `info` to read the watch's range as the server checks it
(`apply.watchPerms`: the key with `""` read as `"\x00"`, `apply.watchKey`, and the request's own range end). -/
def watchCheckedD [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (P : Option GoString) (L₀ : List EntryModel) (key rangeEnd : GoString) : IProp GF :=
  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (L : List EntryModel),
    servedBy eps Γ mid ∗ srvReqLogLb γR L ∗
    ⌜userOk P info.Username' ∧ L₀ <+: L ∧
      auth.permitted (srvAuthAtLog Γ.kv srvAuthSt0 L) (auth.authInfoM info) (apply.watchKey key)
        rangeEnd .read⌝)

instance watchCheckedD_persistent [NetProtoGS] (eps : List GoString) (Γ : DistView)
    (γR : ServerRaftNames) (P : Option GoString) (L₀ : List EntryModel) (key rangeEnd : GoString) :
    Persistent (watchCheckedD (GF := GF) eps Γ γR P L₀ key rangeEnd) := by
  unfold watchCheckedD servedBy; infer_instance

end defs

end authd
end etcd_dist
end EtcdGrove
end Perennial
