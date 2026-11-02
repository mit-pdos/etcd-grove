/-
**The lease read rows' entry points: their vocabulary** (the lease-read plan, 2026-10-31;
`notes/lease-read-plan.md`). Lean-first (no Rocq counterpart).

`LeaseTimeToLive` and `LeaseLeases` (`v3_server.go`) run on a gRPC goroutine, with the resources of
their key checks (`LeaseCheck.lean`: the auth store's reader `E.RD` and a lower bound `n` of its
published index, a reader slot of the lessor's lock, a lower bound `m` of its history, a thread
token).

- `srvHeaderFacts s cid mid` (persistent): what `newHeader()` reads of the server besides its
  read side: the cluster's id `cid`, the member's `mid`, the leader's invariant.
- `srvHeaderAt E h cid mid`: `newHeader()`'s fresh header `h`, owned, its ids the cluster's and the
  member's, its revision the last of a certified log.
- `leasesListIs v ids`, `leasesRespIs E resp cid mid ids`: `LeaseLeases`' response, owned: its
  header, and one `LeaseStatus` per id of `ids`, in order.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck
public import Code.net.http

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's header fields** (persistent): `newHeader()`'s premises besides the read side,
the cluster `cl` of id `cid` (`s.cluster`), the member id `mid`, the leader's invariant. -/
def srvHeaderFacts (s : Loc) (cid mid : w64) : IProp GF :=
  iprop(∃ cl : Loc, srvClusterAddr s ↦□ cl ∗ membership.clusterCid cl cid ∗
    srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s)

instance srvHeaderFacts_persistent (s : Loc) (cid mid : w64) :
    Persistent (srvHeaderFacts (GF := GF) s cid mid) := by
  unfold srvHeaderFacts; infer_instance

/-- **The server's peer round tripper** (persistent; the keep-alive stage, 2026-11-01): its
`peerRt` field (set by `NewServer` from `bootstrap`'s `prt` and never written again) a
`*http.Transport` (what `rafthttp.NewRoundTripper` returns), which `LeaseRenew` forwards a
follower's renewal through. -/
def srvPeerRt (s : Loc) : IProp GF :=
  iprop(∃ (rt : GoInterface), structFieldRef EtcdServer go!"peerRt" s ↦□ rt ∗
    ⌜∃ t : Loc,
      rt = GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.net.http.Transport.ty, #t⟩⌝)

instance srvPeerRt_persistent (s : Loc) : Persistent (srvPeerRt (GF := GF) s) := by
  unfold srvPeerRt; infer_instance

/-- **`newHeader()`'s header `h`** (owned): the cluster's id `cid`, the member's `mid`, the
revision the last of a certified log (`newHeader.spec`'s post). -/
def srvHeaderAt (E : apply.AEnv GF) (h : Loc) (cid mid : w64) : IProp GF :=
  iprop(∃ (v : etcdserverpb.ResponseHeader) (log : mvcc.Log), h ↦ v ∗ mvcc.idxCert E.γ.idx log ∗
    ⌜log ≠ [] ∧ v.ClusterId' = cid ∧ v.MemberId' = mid ∧ v.Revision' = W64 ((log.length : Int) - 1)⌝)

/-- **A `LeaseLeasesResponse` value's listing of the lease ids `ids`** (owned): its `Leases` a
slice of fresh `LeaseStatus`es, the `k`-th with the `k`-th id. -/
def leasesListIs (v : etcdserverpb.LeaseLeasesResponse) (ids : List w64) : IProp GF :=
  iprop(∃ ps : List Loc, v.Leases' ↦* ps ∗ ⌜ps.length = ids.length⌝ ∗
    [∗list] k ↦ p ∈ ps, ∃ (st : etcdserverpb.LeaseStatus) (id : w64),
      ⌜ids[k]? = some id ∧ st.ID' = id⌝ ∗ p ↦ st)

/-- **`LeaseLeases`' response `resp` for the lease ids `ids`** (owned): its header
(`srvHeaderAt`) and its listing (`leasesListIs`). -/
def leasesRespIs (E : apply.AEnv GF) (resp : Loc) (cid mid : w64) (ids : List w64) : IProp GF :=
  iprop(∃ v : etcdserverpb.LeaseLeasesResponse, resp ↦ v ∗ srvHeaderAt E v.Header' cid mid ∗
    leasesListIs v ids)

end defs

end EtcdGrove
end Perennial
