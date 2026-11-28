/-
`startMembers(ms, lg)` (`examples/etcd/restartN/restartN.go`; `notes/restartN-plan.md`): the members `ms`
of a new cluster started in order. **The start mirrors `etcdstart.StartMembers`' steps** (the initial
cluster's map, then per member: the server built at the token and snapshot settings, its peer address
listened on and served, the server started) **but serves each member's peer address through the member's
`raftSwap`** (restart3's `newMember`) instead of its raft handler directly, so that a stopped member's
restarted incarnation can be served at the same address without closing or re-listening it (decided by
etcd-grove-81, 2026-11-15). Lean-first (no Rocq counterpart).

**The triple:** `etcdstart.StartMembers.spec`'s (each member `m` paired with its ghost names `g`,
`xs : List (GMember × MemberG)`, at one cluster, the members' names distinct and valid UTF-8, each
member's URLs `urlsN` of the cluster's), at restartN's token and snapshot settings and the lease mode
`none`, per member `build`'s and `newMember`'s resources (`etcdstart.memberPre`): `startMembers`
returns the thread token and either an error or the slices of the started servers and of the members'
records, one pair `z` per member in order (`zs`), with the cluster's map (read-only, each name's slice
its member's one peer URL); per member, its `memberUp` given the thread token back, its record
(`memberRec`: its peer handler, at its peer address) and its data directory.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.newMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open etcd_restart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **A started member** (`startMembers`' post, per member): its server `z.1`'s `memberUp`, the thread
token lent out; its record `z.2` (its peer handler at its peer address); its data directory. -/
def memberStarted (lg : Loc) (γn : NetNames GF) (z : Loc × Loc) (x : GMember × MemberG GF) :
    IProp GF :=
  iprop((threadTok -∗ memberUp z.1 x.2.ρ x.2.E lg γn x.2.id) ∗
    (∃ γS : SwNames, memberRec z.2 γS γn x.1.Name' x.1.Peer' x.1.Client') ∗
    srvDataDir z.1 (memberDataDir x.1.Name'))

/-- See the file header. -/
abbrev startMembers.spec : Prop :=
  ∀ (N : Nat) (msl : GoSlice) (lg : Loc)
    (xs : List (GMember × MemberG GF)) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  N + 7 + bootWB ≤ backend.wbInit →
  bootLog.length ≤ 2 ^ 60 → γn.dir = dir → netDirOk dir → rafthttp.bootCfg dir ps →
  -- the members' names distinct and valid UTF-8 (`bootPremise`'s condition on the map's keys)
  (xs.map (·.1.Name')).Nodup → (∀ x ∈ xs, utf8Valid x.1.Name') →
  -- (wal-fsfix, 2026-11-20, the user's decision) the members' names at most 200 bytes, so that their
  -- data directories fit (`bootCfgFresh`'s `Fs.DirFits`, from `dirFits_memberDataDir`)
  (∀ x ∈ xs, x.1.Name'.length ≤ 200) →
  -- (fmt stage 1, 2026-11-24) the members' addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  (∀ x ∈ xs, etcdstart.addrFits x.1.Peer' ∧ etcdstart.addrFits x.1.Client') →
  -- each member's names the cluster's, its peer URL its directory entry
  (∀ x ∈ xs, x.2.γ.vs = ps ∧ x.2.γ.rule = srvRule (W64 0) bootLog ∧ x.2.γ.boot = bootLog ∧
    γn.N = srvNet x.2.γ ∧ go!"http://" ++ x.1.Peer' ∈ dir x.2.id) →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
      zapLoggerOk lg ∗ threadTok ∗ msl ↦*□ xs.map (·.1) ∗
      context.isClosedchanInit ∗
      [∗list] x ∈ xs, memberPre N token (xs.map (·.1)) ps bootLog ctxs dir Φs γn .none x }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restartN.startMembers))
      (Val #msl)) (Val #lg))
  {{ (ssl msl' : GoSlice) (cl : Loc) (err : GoInterface),
      RET (PairV (PairV (PairV #ssl #msl') #cl) #err); threadTok ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ (zs : List (Loc × Loc)) (M : GMap GoString GoSlice),
          ssl ↦* zs.map (·.1) ∗ msl' ↦* zs.map (·.2) ∗
          cl ↦$□ M ∗ ([∗map] n ↦ sl ∈ M, sl ↦*□ iuOf (xs.map (·.1)) n) ∗
          ⌜∀ n, (M.lookup n).isSome ↔ n ∈ xs.map (·.1.Name')⌝ ∗
          [∗list] z; x ∈ zs; xs, memberStarted lg γn z x)) }}

end spec

end etcd_restartN
end EtcdGrove
end Perennial
