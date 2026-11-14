/-
`startMember(name, peer, peerAddr, client, cluster, lg)` (`examples/etcd/auth3/auth3.go`; the auth3
Scope's A1, `notes/auth3-scope.md`, Q5): member `name` of the three-member cluster started with auth
on -- its configuration (authkv's `startServer`'s at the member's name, URLs and the cluster's map:
the simple token provider, etcd's default token TTL, the examples' no-snapshot settings),
`etcdserver.NewServer`, its raft handler served on a listener at its peer address (as
`etcdstart.NewMember`), `s.Start()`. Lean-first (no Rocq counterpart).

**The triple:** `etcdstart.StartMember.spec`'s with auth on (authkv's `startServer.spec`'s at a
member of a three-member cluster): given the member's ghost state with auth on (`memberBootOn`), the
network's HTTP side, its fresh bundle (its WAL directory fresh, its peer address's listen right
and raft protocol), a thread token, the configuration's URL slices and map, `bootstrap`'s contract
for it (auth3's `bootPremise`, at its `cfgOk`) and the premises the members share: an error with
the thread token, or the member started with auth on (`memberUpOn`, at the auth names `γa` of the
store `NewServer` built).

**The pure premises:** `etcdstart.StartMember.spec`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- See the file header. -/
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  rafthttp.bootCfg dir ps →
  urlsOk peerAddr client ⟨[etcdstart.httpURL peerAddr], [etcdstart.httpURL client], M, iu⟩ →
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth3 ∗
      zapLoggerOk lg ∗
      threadTok ∗
      peer ↦*□ [etcdstart.httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir name peerAddr client id ∗ etcdstart.commonPremises ∗
      context.isClosedchanInit ∗
      etcdstart.memberBootOn γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id ∗
      etcdstart.memberFreshRes name ⟨some peerAddr, none⟩ γn }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth3.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s ρ E₀ lg γn id γa) }}

end spec

end etcd_auth3
end EtcdGrove
end Perennial
