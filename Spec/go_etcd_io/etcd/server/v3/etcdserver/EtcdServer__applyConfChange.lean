/-
`(*EtcdServer).applyConfChange(cc, ep, shouldApplyV3)` (server.go): what a membership change
writes (D43 M5e, 2026-10-26: proved; until then the trust boundary). Lean-first (no Rocq counterpart); see `InvApplier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The membership change** (D43 M5e, 2026-10-26: a theorem, proved from the translated body;
until then an axiom, its statement the trust boundary). Two cases, by `v3` (R2d'a, swap batch 1,
2026-11-06: until then the `v3 = false` case was vacuous, its premises `dv ≠ none` and `dv = some n
→ v3 = true`, and the replay had a second spec, `specRep`).

**With `v3`** (`ApplyBoth`), `s.applyConfChange(cc, ep, true)` validates
the change `cc` (`ValidateConfigurationChange`, reading the member backend: its read contract over
the tracked buckets) and applies it to the cluster (`s.cluster`, whose backend is the server's:
the batch lock `E.P` with the post-lock hook `E.f`, `mvcc.hookOk` from the uber applier), to raft
(`s.r.ApplyConfChange`: raft's static mode's clause of `srvRaftNode`, or the dynamic contract
`srvRaftNodeDyn`), to `ep.confState` and the backend hooks' conf state (`s.beHooks`,
`isBackendHooks`), and to the transport (`s.r.transport`, `ccMembRes`). Its backend write happens
in one critical section of the batch lock, after the hook (the
caller's hook triple and update, a write session's token spent), or, if the validation fails,
there is none and it stores the applying index `(i, t)` into the consistent index (read from
`ciApplying`, which the caller's `Pre` lends). It may change `cc` (`NodeId` on a failed
validation), but not its `Id`, and hands it to raft read-only. (2026-10-31, the snapshot track's
S5) `ep.confState` after it is raft's answer, which reports the voters (`epCsVoters`: the cluster's
membership is the voters' at every committed index, `srv_confAt_simple`), or, if the validation
fails, as before.

**Scope** (`ccApplyOkM`): an `AddNode` of a member of raft's configuration whose context
unmarshals to it, not a promotion (`ccApplyOk`, the boot entries'), and, in raft's dynamic mode
(D43 M5d, the user's decision), a `RemoveNode` of a member of the configuration other than the
local one (`lid`; the stopping server is M6's), so it returns `removed = false`. An `AddNode`'s
node is the local member or one of the transport's peers (`prs`: `AddPeer` of a known peer
returns at once, `AddPeer_known`); the members map stays within its bound.

**Its effect on the rest buckets and the members**: `E.RO` (`srvRestOwnH γB cl H`, the cluster's
`be` field among `H`, `clusterBeOn`) at `rs` goes to `ccRest true m rs` (the member saved and added
or deleted and recorded removed, when the change validates, `ccValidOn rs.bk m`); the
transport's peers to `ccPeersAfter true m rs.bk prs`; the cluster's removed map in the dynamic mode
with them (`ccMembRes`).

**Raft's dynamic mode** (D43 M3): `dv` is the driver's view, `none` in raft's static mode, or
`some γn`; with `v3` it is `some γn`, the node meets the dynamic contract, and the change Go hands
raft (D43 M5d: `ccRaftEff`, the change if it validates, else with `NodeId` `0`; until then both
had to) meets raft's premise (`DynCCPreOp`, the view `(ca, cfg)` to `(k + 1, cs')`).

(2026-11-02, the backend-auth-split stage) It takes the members' buckets as the apply thread writes
them (`membership.membersDecode rs.bk`: its caller's `rs` is an applied log's,
`membersDecode_restModel`), and the current backend's reader pool and the apply thread's token
(`backend.bkRPool`, `threadTok`), which it gives back: for the member backend's reads (the next
stage's pooled readers); and the backend's facts (`srvBeRO d`: its `isBackend`, which the member
backend's read and writes take; 2026-11-02, the backend-auth-split stage).

**Without `v3`, a replayed `AddNode`** (an entry at or below the consistent index, at a restart; at
the pin `673da07c8`, `server.go:2037-2083`): the validation passes without reading
(`membership/cluster.go:306-309`), raft is not called and `ep.confState` is kept
(`server.go:2053-2059`), `beHooks.SetConfState(ep.confState)`, the context unmarshalled and checked
against the node (`ccApplyOkM`: it unmarshals to the node's member), `AddMember(…, false)` only logs
(`membership/cluster.go:402-424`: under the cluster's lock, so it takes the in-memory members, which
`E.RO rs` holds, with their size bound), and `AddPeer` of the node unless it is the local member (a
known peer: `AddPeer_known`). It returns `removed = false`, writes no backend bucket and no member in
memory (`E.RO rs` back, `ccRest false` being the identity), and keeps `ep.confState` and the
transport's peers; it takes none of the `v3` case's resources but those. -/
abbrev EtcdServer.applyConfChange.spec : Prop :=
  ∀ (s cc ep : Loc) (m : ConfChangeM) (cs : Loc) (v3 : Bool) (ci : Loc) (ua : GoInterface)
    (E : apply.AEnv GF) (γs : ServerRaftNames) (Pre Q Post Adv : IProp GF) (i t : w64)
    (γB : backend.BNames) (cl : Loc) (rs : apply.RestM) (d : mvcc.KBReal) (al st lp : Loc)
    (dv : Option Loc) (ds : List LogEntry) (v : ConfigView) (k : Nat)
    (m' : Membership) (e : LogEntry)
    (lg bh : Loc) (ix : GoInterfaceOk) (lgh tl : Loc) (lid : w64) (prs : trIds) (lgc : Loc)
    (cid : w64),
  ccApplyOkM γs m → E.RO = srvRestOwnH E.authMode γB cl (srvObjsOn al st lp cl d.be) →
  (m.type = W32 0 → m.nodeId ≠ lid → m.nodeId ∈ prs) →
  (m.type = W32 1 → m.nodeId ≠ lid) →
  (m.type = W32 0 →
    GMap.size (GMap.insert m.nodeId (membership.ccMemberAt m) rs.mem) ≤ 2 ^ 62) →
  -- with `v3` only: the backend, raft's view (2026-10-30, the repair: raft's one mode, a conf
  -- entry's batch hands the view over; until then, without a view, a static cluster) and the
  -- members' buckets
  (v3 = true → E.γ.kb = some d ∧ d.γB = γB ∧ dv ≠ none ∧
    (∀ n, dv = some n → srvCCPre γs.raft.rule ds v (.v1 (membership.ccRaftEff rs.bk m)) k e m') ∧
    (rs.bk.lookup go!"members").isSome ∧ (rs.bk.lookup go!"members_removed").isSome) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      (if v3 then iprop(
        srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
        srvCIAddr s ↦□ ciIface ci ∗ srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
        srvRaftNode s γs ∗ srvClusterAddr s ↦□ cl ∗ E.RO rs ∗
        membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗ membership.rcCidAddr cl ↦□ cid ∗
        dvCCPre s γs dv v ds ∗
        ownConfChange cc (DFrac.own 1) m ∗ epConfState ep cs ∗
        srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
        srvTransportAddr s ↦□ srvTrIface tl ∗
        srvMemberIDAddr s ↦□ lid ∗ ccMembRes γs cl tl lid prs ∗ mvcc.storeRT E.γ ∗
        ⌜membership.membersDecode rs.bk⌝ ∗ backend.bkRPool d.γB d.P d.be ∗ threadTok ∗ srvBeRO d ∗
        mvcc.storeWT E.γ ∗
        □ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
        (Q ={⊤}=∗ E.P ∗ Post) ∗
        (Pre -∗ ciApplying ci i t ∗ (ciApplying ci i t -∗ Pre)) ∗
        (Pre -∗ WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!!
          go!"SetConsistentIndex")) (Val #i)) (Val #t)) {{ v, ⌜v = #()⌝ ∗ Adv }}) ∗
        Pre)
      else iprop(
        srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
        srvClusterAddr s ↦□ cl ∗ membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗
        membership.rcCidAddr cl ↦□ cid ∗
        ownConfChange cc (DFrac.own 1) m ∗ epConfState ep cs ∗
        srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
        srvTransportAddr s ↦□ srvTrIface tl ∗ srvMemberIDAddr s ↦□ lid ∗
        ccMembRes γs cl tl lid prs ∗ E.RO rs)) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyConfChange"))
      (Val #cc)) (Val #ep)) (Val #v3))
  {{ (removed : Bool) (err : GoInterface), RET (PairV #removed #err);
      ⌜removed = false⌝ ∗ srvLgReader s ∗
      (if v3 then iprop(
        srvUberApplyAddr s ↦ ua ∗
        (∃ (m' : ConfChangeM) (csl : Loc), ownConfChange cc DFrac.discard m' ∗ ⌜m'.id = m.id⌝ ∗
          epConfState ep csl ∗
          (epCsVoters γs csl ∨ ⌜membership.ccValidOn rs.bk m = false ∧ csl = cs⌝)) ∗
        E.RO (ccRest true m rs) ∗ (Post ∨ Adv) ∗
        dvCCPost γs dv k m' ∗ ccMembRes γs cl tl lid (ccPeersAfter true m rs.bk prs) ∗
        mvcc.storeRT E.γ ∗ backend.bkRPool d.γB d.P d.be ∗ threadTok)
      else iprop(
        (∃ m' : ConfChangeM, ownConfChange cc DFrac.discard m' ∗ ⌜m'.id = m.id⌝) ∗
        epConfState ep cs ∗ ccMembRes γs cl tl lid prs ∗ E.RO rs)) }}

end spec

end EtcdGrove
end Perennial
