/- Lean-first (no Rocq counterpart).

# PLACEHOLDER for phase 7 S5: `etcdstart.StartMember` on a member machine of a `k`-member cluster

**Not a trust-boundary contract and no axiom: a named hypothesis** of the `k`-member member boots
(`putgetk`'s `Member.wp_proof`, `notes/putget-dist-plan.md` §13, plan item 4), which S5 (net/http over the
net extension, rafthttp across machines; #24/#18) is to prove, stated as `StartMember.spec` with the
single-process network replaced by S5's names (`dist/S5Draft.lean`). Its exact form is to be agreed with
proving session 2 with S5Draft's other member-side fields; until then nothing outside the member boots'
internal lemmas takes it, and no top-level statement does (Upamanyu, 2026-11-24).

**What changes from `StartMember.spec`** (`Spec/.../examples/lib/etcdstart/StartMember.lean`):
* no network names `γn` in the premises (`γn.N = srvNet γ`, `γn.dir = dir` dropped): the network across
  machines is S5's; the post's `memberUp` is at some network names `γn` (what `Serve_dist` takes);
* `netHttpOk γn id` (the streams' registry, every other member's host registered with raft's protocol) is
  replaced by S5's address facts: the member's own peer address served with rafthttp's protocol and, for
  every other peer of the directory, its address's (`S5Draft.httpAddrAt`, set by the start,
  `etcdClusterStart`'s `peerAddrFacts`);
* `memberFreshRes name ⟨some peerAddr, none⟩ γn` (its fresh WAL area, `ETCD_VERIFY` off, the right to listen
  on the peer address with its protocol reserved) is replaced by its file part (`envVerifyOff`,
  `memberAreasFresh`): the listen right is in `httpAddrAt`.
Everything else (`bootPremise`, `commonPremises`, `memberBoot`, the bounds, the directory's pure facts) is
`StartMember.spec`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Draft
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- **`StartMember` on a member machine** (PLACEHOLDER for S5; see the file header), at S5's names `S5`. -/
abbrev StartMember_dist.spec [π : Net.NetProtoGS] (S5 : S5Draft (G := hG.goose_globalGS) GF) : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (lm : lease.Mode),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  netDirOk dir → go!"http://" ++ peerAddr ∈ dir id → rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  name.length ≤ 200 →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id (m := lm) ∗
      -- S5's address facts: its own peer address, and every other peer's in the directory
      S5.httpAddrAt peerAddr ∗
      (□ ∀ (pid : w64) (a : GoString), ⌜pid ∈ ps ∧ pid ≠ id ∧ go!"http://" ++ a ∈ dir pid⌝ -∗
        S5.httpAddrAt a) ∗
      -- the file part of `memberFreshRes`
      envVerifyOff (GF := GF) ∗ memberAreasFresh (GF := GF) (memberDataDir name) }}
    (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γn : NetNames GF, memberUp s ρ E₀ lg γn id lm) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial

end
