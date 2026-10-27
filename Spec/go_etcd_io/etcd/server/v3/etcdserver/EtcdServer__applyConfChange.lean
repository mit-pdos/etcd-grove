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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The membership change** (D43 M5e, 2026-10-26: a theorem, proved from the translated body;
until then an axiom, its statement the trust boundary). `s.applyConfChange(cc, ep, v3)` validates
the change `cc` (`ValidateConfigurationChange`, reading the member backend: its read contract over
the tracked buckets) and applies it to the cluster (`s.cluster`, whose backend is the server's:
the batch lock `E.P` with the post-lock hook `E.f`, `mvcc.hookOk` from the uber applier), to raft
(`s.r.ApplyConfChange`: raft's static mode's clause of `srvRaftNode`, or the dynamic contract
`srvRaftNodeDyn`), to `ep.confState` and the backend hooks' conf state (`s.beHooks`,
`isBackendHooks`), and to the transport (`s.r.transport`, `ccMembRes`). For `v3` (`ApplyBoth`)
its backend write happens in one critical section of the batch lock, after the hook (the
caller's hook triple and update, a write session's token spent), or, if the validation fails,
there is none and it stores the applying index `(i, t)` into the consistent index (read from
`ciApplying`, which the caller's `Pre` lends). Without `v3` it writes nothing to the backend and
does not call raft. It may change `cc` (`NodeId` on a failed validation), but not its `Id`, and
hands it to raft read-only.

**Scope** (`ccApplyOkM`): an `AddNode` of a member of raft's configuration whose context
unmarshals to it, not a promotion (`ccApplyOk`, the boot entries'), and, in raft's dynamic mode
(D43 M5d, the user's decision), a `RemoveNode` of a member of the configuration other than the
local one (`lid`; the stopping server is M6's), so it returns `removed = false`. An `AddNode`'s
node is the local member or one of the transport's peers (`prs`: `AddPeer` of a known peer
returns at once, `AddPeer_frozen`, `AddPeer_known`); the members map stays within its bound.

**Its effect on the rest buckets and the members**: `E.RO` (`srvRestOwnH γB cl H`, the cluster's
`be` field among `H`, `clusterBeOn`) at `rs` goes to `ccRest v3 m rs` (the member saved and added
or deleted and recorded removed, with `v3`, when the change validates, `ccValidOn rs.bk m`); the
transport's peers to `ccPeersAfter v3 m rs.bk prs`; the cluster's removed map in the dynamic mode
with them (`ccMembRes`).

**Raft's dynamic mode** (D43 M3): `dv` is the driver's view, `none` in raft's static mode, or
`some γn`; then it is `ApplyBoth`, the node meets the dynamic contract, and the change Go hands
raft (D43 M5d: `ccRaftEff`, the change if it validates, else with `NodeId` `0`; until then both
had to) meets raft's premise (`DynCCPreOp`, the view `(ca, cfg)` to `(k + 1, cs')`). -/
abbrev EtcdServer.applyConfChange.spec : Prop :=
  ∀ (s cc ep : Loc) (m : CCV1M) (cs : Loc) (v3 : Bool) (ci : Loc) (ua : GoInterface)
    (E : apply.AEnv GF) (γs : ServerRaftNames) (Pre Q Post Adv : IProp GF) (i t : w64)
    (γB : backend.BNames) (cl : Loc) (rs : apply.RestM) (d : mvcc.KBReal) (al st lp : Loc)
    (dv : Option NodeNames) (ds : List EntryM) (ca k : Nat) (cfg cs' : CCState) (e : EntryM)
    (lg bh : Loc) (ix : GoInterfaceOk) (lgh tl : Loc) (lid : w64) (prs : trIds) (lgc : Loc)
    (cid : w64),
  ccApplyOkM γs m → E.RO = srvRestOwnH γB cl (srvObjsOn al st lp cl d.be) →
  E.γ.kb = some d → d.γB = γB →
  (dv = none → γs.raft.reDyn = none) →
  (∀ γn, dv = some γn → v3 = true ∧ ∀ dec c0 h0 h1, γn.mode = .dyn dec c0 h0 h1 →
    DynCCPreOp dec ds ca cfg (ccV2Of (.v1 (membership.ccRaftEff rs.bk m))) k e cs') →
  (m.type = W32 0 → m.nodeId ≠ lid → m.nodeId ∈ prs) →
  (m.type = W32 1 → m.nodeId ≠ lid) →
  (m.type = W32 0 →
    GMap.size (GMap.insert m.nodeId (membership.ccMemberAt m) rs.mem) ≤ 2 ^ 62) →
  (rs.bk.lookup go!"members").isSome → (rs.bk.lookup go!"members_removed").isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvCIAddr s ↦□ ciIface ci ∗ srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      srvRaftNode s γs ∗ srvClusterAddr s ↦□ cl ∗ E.RO rs ∗
      membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗ membership.rcCidAddr cl ↦□ cid ∗
      dvCCPre s dv ca cfg ds ∗
      ownCCV1 cc (DFrac.own 1) m ∗ epConfState ep cs ∗
      srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
      srvTransportAddr s ↦□ srvTrIface tl ∗
      srvMemberIDAddr s ↦□ lid ∗ ccMembRes γs cl tl lid prs ∗ mvcc.storeRT E.γ ∗
      (if v3 then iprop(mvcc.storeWT E.γ ∗
          □ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post) ∗
          (Pre -∗ ciApplying ci i t ∗ (ciApplying ci i t -∗ Pre)) ∗
          (Pre -∗ WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!!
            go!"SetConsistentIndex")) (Val #i)) (Val #t)) {{ v, ⌜v = #()⌝ ∗ Adv }}))
       else iprop(True)) ∗ Pre }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyConfChange"))
      (Val #cc)) (Val #ep)) (Val #v3))
  {{ (removed : Bool) (err : GoInterface), RET (PairV #removed #err);
      ⌜removed = false⌝ ∗ srvLgReader s ∗ srvUberApplyAddr s ↦ ua ∗
      (∃ (m' : CCV1M) (csl : Loc), ownCCV1 cc DFrac.discard m' ∗ ⌜m'.id = m.id⌝ ∗
        epConfState ep csl) ∗
      E.RO (ccRest v3 m rs) ∗ (if v3 then iprop(Post ∨ Adv) else Pre) ∗
      dvCCPost dv k cs' ∗ ccMembRes γs cl tl lid (ccPeersAfter v3 m rs.bk prs) ∗
      mvcc.storeRT E.γ }}

end spec

end EtcdGrove
end Perennial
