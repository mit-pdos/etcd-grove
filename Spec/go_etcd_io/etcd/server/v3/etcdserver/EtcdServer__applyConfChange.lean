/-
`(*EtcdServer).applyConfChange(cc, ep, shouldApplyV3)` (server.go): the trust boundary for
what a membership change writes. Lean-first (no Rocq counterpart); see `InvApplier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

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

/-- **The membership change's contract.** `s.applyConfChange(cc, ep, v3)` validates the
change `cc` and applies it to the cluster (`s.cluster`, whose backend is the server's: the
batch lock `E.P` with the post-lock hook `E.f`: the environment `E` of `s.uberApply`,
`apply.applierFor`; D22 receiver epochs, S7a, 2026-10-23: the field the apply thread's, given
back), to raft (`s.r.ApplyConfChange`, the server's raft node's contract in
`srvRaftNode`) and to `ep.confState`. For `v3` (`ApplyBoth`) its writes to the backend happen in
one critical section of the batch lock, after the hook (as `apply.Apply`'s: the caller's hook
triple and writes update), or, if the validation fails, there are none and it stores the
applying index `(i, t)` into the consistent index `s.consistIndex = ci` (the caller's triple for
that store, `Pre -∗ WP ci.SetConsistentIndex(i, t) {Adv}`). Without `v3` it writes nothing to
the backend and does not call raft. It may change `cc` (it sets `NodeId` on a failed
validation), but not its `Id`, and it hands it to raft read-only (`DFrac.discard`): the change
is raft's `ownCCV1` (as `pbutil.MustUnmarshalMessage` decoded it; since stage R6 of the raft
v3.7 retarget, 2026-10-16, the struct value with its `Id` cell), some record `m'` after with
`m`'s id.

(D19i part 1, 2026-10-18) `ep.confState` (`epConfState`) stays `nil` or a read-only
`*pb.ConfState`: raft's `ApplyConfChange` answers a fresh one (`node.ApplyConfChange.spec`'s
`confstateP`, owned), which the server only reads afterwards (`CreateSnapshot`, the backend
hooks' `SetConfState`).

**Scope** (audit phase B3, 2026-10-18; until then stated for every change, which was false: it
handed raft a change without `node.ApplyConfChange`'s premise, panicked on a malformed context or
an unknown type, and removed the local member on its `RemoveNode`, against
`membership.localKept`): a change `applyConfChange` takes, `ccApplyOk` at raft's configuration
(`ρ.raft.raft.reCfg`): an `AddNode` of a member of the configuration, whose context unmarshals to
that member, not a promotion. Then neither it nor `ValidateConfigurationChange` panics, it
removes no member (`AddMember` of a member; for a member other than the local one, the
transport's `AddPeer`, which returns at once for a member the construction added as a peer,
`transport.go`'s known-peer check; until D21 M2 named with the transport's other effects,
`transportEffectsOk`), and what it hands raft
(the change, or on a failed validation the change with `NodeId` `0`) leaves raft's configuration
as it is (`ccRaftOk`, `raftPropose`'s premise for `ApplyConfChange`). The server's policy admits
no other conf change (`srvCCPolicy`, `ccBootOk`).

**Its effect on the rest buckets and the members** (D22, 2026-10-23: the backend over every
bucket): the environment's `RO` is the server's (`srvRestOwnH γB cl H`, D22 receiver epochs,
S7e: `H` the server's objects on the store's backend `d`, `srvObjsOn`, the cluster's `be` field among
them, which names the backend its writes go to: `E`'s, whose batch lock is `E.P`; the backend's tracked
buckets' half and the in-memory members of `s.cluster = cl`), taken at `rs` and given back at
`ccRest v3 m rs` (D22 receiver epochs, S7c: with the server's objects' backend parts `H`, which it
leaves, a frame), with `v3`, `ValidateConfigurationChange` reads the `members` and
`members_removed` buckets (`MustReadMembersFromBackend`, a read transaction: what the apply
thread, their only writer, last wrote, `Unlock` having written back) and returns `nil` iff
`membership.ccValidOn rs.bk m`; then `AddMember` saves the context's member
(`membership.ccMemberOf m.context`: `members/<id> := json(m)`) and puts it in `c.members`; on a
failed validation, or without `v3`, nothing.

**Raft's dynamic mode** (D43 M3, 2026-10-25, the user's decision: the axiom restated): `dv` is the
driver's view, `none` in raft's static mode (`reDyn = none`, the call through `raftPropose`'s
static clause), or `some γn`, the node's names in the dynamic mode. Then it is `ApplyBoth` (Go
calls raft only then, or on a failed validation), the server's node meets the dynamic contract
(`srvRaftNodeDyn`), and the caller hands over the view `nodeCfg γn ca cfg` with the committed log
`ds` handed out (`dlvLb`): the entry `e` at position `k` is the next conf entry, and both changes
Go may hand raft -- the entry's `m`, or on a failed validation `m` with `NodeId` `0` -- meet raft's
premise (`DynCCPreOp`: the decoder's effect, `cs'`); it gives back the view at `(k + 1, cs')`
(`dvCCPre`, `dvCCPost`). -/
abbrev EtcdServer.applyConfChange.spec : Prop :=
  ∀ (s cc ep : Loc) (m : CCV1M) (cs : Loc) (v3 : Bool) (ci : Loc) (ua : GoInterface)
    (E : apply.AEnv GF) (γs : ServerRaftNames) (Pre Q Post Adv : IProp GF) (i t : w64)
    (γB : backend.BNames) (cl : Loc) (rs : apply.RestM) (d : mvcc.KBReal) (al st lp : Loc)
    (dv : Option NodeNames) (ds : List EntryM) (ca k : Nat) (cfg cs' : CCState) (e : EntryM),
  ccApplyOk γs.raft.reCfg m → E.RO = srvRestOwnH γB cl (srvObjsOn al st lp cl d.be) →
  E.γ.kb = some d → d.γB = γB →
  (dv = none → γs.raft.reDyn = none) →
  (∀ γn, dv = some γn → v3 = true ∧ ∀ dec c0 h0 h1, γn.mode = .dyn dec c0 h0 h1 →
    DynCCPreOp dec ds ca cfg (ccV2Of (.v1 m)) k e cs' ∧
    DynCCPreOp dec ds ca cfg (ccV2Of (.v1 { m with nodeId := W64 0 })) k e cs') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCIAddr s ↦□ ciIface ci ∗ srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
      srvRaftNode s γs ∗ srvClusterAddr s ↦□ cl ∗ E.RO rs ∗
      dvCCPre s dv ca cfg ds ∗
      ownCCV1 cc (DFrac.own 1) m ∗ epConfState ep cs ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post) ∗
          (Pre -∗ WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!!
            go!"SetConsistentIndex")) (Val #i)) (Val #t)) {{ _v, Adv }}))
       else iprop(True)) ∗ Pre }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyConfChange"))
      (Val #cc)) (Val #ep)) (Val #v3))
  {{ (removed : Bool) (err : GoInterface), RET (PairV #removed #err);
      ⌜removed = false⌝ ∗ srvUberApplyAddr s ↦ ua ∗
      (∃ (m' : CCV1M) (csl : Loc), ownCCV1 cc DFrac.discard m' ∗ ⌜m'.id = m.id⌝ ∗
        epConfState ep csl) ∗
      E.RO (ccRest v3 m rs) ∗ (if v3 then iprop(Post ∨ Adv) else Pre) ∗
      dvCCPost dv k cs' }}

end spec

end EtcdGrove
end Perennial
