/-
`StartMemberAuth(name, peer, peerAddr, client, cluster, token, snapCount, catchUp, lg)`
(`examples/lib/etcdstart/auth.go`; authN, 2026-11-15, `notes/authN-plan.md`): member `name` of a new
cluster started with auth on -- auth3's `startMember` (`Spec/.../etcd/auth3/startMember.lean`) at any
token, URLs and snapshot settings. Lean-first (no Rocq counterpart).

**The triple:** auth3's `startMember.spec` with the token, the snapshot settings and the URLs'
condition `Uok` parameters, `bootstrap`'s contract at `bootPremiseOn` (auth3's `bootPremise`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersAuthDefs

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
abbrev StartMemberAuth.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF)
    -- (auth-lease S4, 2026-11-16) the cluster's lease mode
    (m : lease.Mode),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (fmt stage 1, 2026-11-24) the addresses within etcd's URL bounds (`NewServer`'s `etcdURLsFit`)
  addrFits peerAddr → addrFits client →
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  -- (wal-fsfix, 2026-11-20, the user's decision) the member's name at most 200 bytes, so that its data
  -- directory fits (`bootCfgFresh`'s `Fs.DirFits`, from `dirFits_memberDataDir`)
  name.length ≤ 200 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  -- (auth-lease S4, 2026-11-16) in raft's no-snapshot mode, the catch-up at least `2^48` (the
  -- receipts' bound above; `NewServer.spec`'s)
  (clusterNoSnap γ.cl → 2 ^ 48 ≤ uint.Z catchUp) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremiseOn N ps bootLog ctxs dir token name Uok id ∗
      context.isClosedchanInit ∗
      memberBootOn γ ctxs ρ E₀ Φs id false m ∗
      netHttpOk γn id ∗
      memberFreshRes name ⟨some peerAddr, none⟩ γn }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMemberAuth))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γa : auth.AuthNames, memberUpOn s ρ E₀ lg γn id γa m) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
