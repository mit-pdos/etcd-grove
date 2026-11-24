/-
`StartMembersAuth(ms, token, snapCount, catchUp, lg)` (`examples/lib/etcdstart/auth.go`; authN,
2026-11-15, `notes/authN-plan.md`): the members `ms` of a new cluster started with auth on, in order.
Lean-first (no Rocq counterpart).

**The triple:** `StartMembers.spec` with auth on: per member `memberPreOn` (`bootstrap`'s contract at
`bootPremiseOn`, `memberBootOn`) in place of `memberPre`, and each started member's
`memberUpOn` (at the auth names of the store its `NewServer` built) in place of `memberUp`; no lease
mode (auth on grants no lease at `memberBootOn`). Kept generic for later k-member auth theorems.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMemberAuth

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
abbrev StartMembersAuth.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (token : GoString) (snapCount catchUp : w64)
    (msl : GoSlice) (lg : Loc)
    (xs : List (GMember × MemberG GF)) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    -- (auth-lease S4, 2026-11-16) the cluster's lease mode
    (m : lease.Mode),
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
  -- (auth-lease S4, 2026-11-16) in raft's no-snapshot mode, the catch-up at least `2^48`
  -- (`StartMemberAuth.spec`'s)
  (∀ x ∈ xs, clusterNoSnap x.2.γ.cl → 2 ^ 48 ≤ uint.Z catchUp) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗ threadTok ∗ msl ↦*□ xs.map (·.1) ∗ commonPremises ∗
      context.isClosedchanInit ∗
      [∗list] x ∈ xs, memberPreOn N token (xs.map (·.1)) ps bootLog ctxs dir Φs γn x m }}
    (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembersAuth))
      (Val #msl)) (Val #token)) (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (ssl : GoSlice) (err : GoInterface), RET (PairV #ssl #err); threadTok ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ ss : List Loc, ssl ↦* ss ∗
          [∗list] s; x ∈ ss; xs, (threadTok -∗ ∃ γa : auth.AuthNames, memberUpOn s x.2.ρ x.2.E lg γn x.2.id γa m))) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
