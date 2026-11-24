/-
`StartMembers(ms, token, lg)` (`examples/lib/etcdstart/members.go`; the clusterN Scope,
`notes/clusterN-scope.md`, 2026-11-15): the members `ms` of a new cluster started, in order. Lean-first
(no Rocq counterpart).

**The triple:** `StartMember`'s for every member of a list, each member `m` paired with its ghost
names `g` (`xs : List (GMember × MemberG)`, the Go slice the members `xs.map (·.1)`), at one
cluster (the peers `ps`, the bootstrap log, the peer-URL directory `dir`, the claimers' facts `Φs`,
the network `γn`, the lease mode `lm`, the compaction mode `cmp`: `false` but for the compactor's
k-member cluster, `notes/k8s-compactor-n-plan.md`), the members' names distinct and valid UTF-8, and each
member's URLs `urlsN` of the cluster's (its peer URL `http://Peer`, its client URL
`http://Client`, the initial cluster's map of the members' names, `iuOf`): from the thread token and,
per member, `bootstrap`'s contract (`bootPremise`), `memberBoot`, its network's HTTP side and its
fresh bundle (without a client address), `StartMembers` returns the thread token and either an
error or a slice of the started servers, one per member in order, each with its `memberUp` given
the thread token back (`StartMember` takes the token, `Start`'s goroutines' `srvGoRes` holds it, and
the next member's start borrows it).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev StartMembers.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (token : GoString) (snapCount catchUp : w64)
    (msl : GoSlice) (lg : Loc)
    (xs : List (GMember × MemberG GF)) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode) (cmp : Bool),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  bootLog.length ≤ 2 ^ 60 → γn.dir = dir → netDirOk dir → rafthttp.bootCfg dir ps →
  -- the members' names distinct and valid UTF-8 (`bootPremise`'s condition on the map's keys)
  (xs.map (·.1.Name')).Nodup → (∀ x ∈ xs, utf8Valid x.1.Name') →
  -- (wal-fsfix, 2026-11-20, the user's decision) the members' names at most 200 bytes, so that their
  -- data directories fit (`bootCfgFresh`'s `Fs.DirFits`, from `dirFits_memberDataDir`)
  (∀ x ∈ xs, x.1.Name'.length ≤ 200) →
  -- (fmt stage 1, 2026-11-24) the members' addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  (∀ x ∈ xs, addrFits x.1.Peer' ∧ addrFits x.1.Client') →
  -- each member's names the cluster's, its peer URL its directory entry
  (∀ x ∈ xs, x.2.γ.vs = ps ∧ x.2.γ.rule = srvRule (W64 0) bootLog ∧ x.2.γ.boot = bootLog ∧
    γn.N = srvNet x.2.γ ∧ go!"http://" ++ x.1.Peer' ∈ dir x.2.id) →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗ threadTok ∗ msl ↦*□ xs.map (·.1) ∗ commonPremises ∗
      context.isClosedchanInit ∗
      [∗list] x ∈ xs, memberPre N token (xs.map (·.1)) ps bootLog ctxs dir Φs γn lm x cmp }}
    (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembers))
      (Val #msl)) (Val #token)) (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (ssl : GoSlice) (err : GoInterface), RET (PairV #ssl #err); threadTok ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ ss : List Loc, ssl ↦* ss ∗
          [∗list] s; x ∈ ss; xs, (threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id lm))) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
