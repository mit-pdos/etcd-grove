/-
`startServer(lg)` (`examples/etcd/auth/etcd_auth.go`; the auth plan's E3zb, 2026-10-28): the one member
of a new cluster started with auth on -- its peer URL slice, its configuration (`etcdstart.newServer`'s,
on authkv's ports, with the simple token provider and etcd's default token TTL, `300`),
`etcdserver.NewServer`, `s.Start()`. Lean-first (no Rocq counterpart).

**The triple:** `etcdstart.StartServer.spec`'s, with auth on: given the member's ghost state with auth
on (`memberBootOn`: the start chain with the auth layer enabled, the KV invariant in the mode `on`),
the network's HTTP side, a thread token, `bootstrap`'s contract for it (at the one-member cluster `[id]`, for
the configurations and URLs `startServer` builds: `cfgOk`, `urlsOk`, the first of `Main`'s
`premises`; 2026-10-30, until then `etcdstart.bootPremise`, whose `etcdstart.cfgOk` leaves out the
simple token provider) and the premises the members share: an error with the thread token, or the member started with auth on (`memberUpOn`, at the auth
names `γa` of the store `NewServer` built).

**The pure premises:** `etcdstart.StartServer.spec`'s, at authkv's addresses.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- See the file header. -/
abbrev startServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (lg : Loc)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString) (id : w64)
    (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = [id] → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://127.0.0.1:23926" ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir [id] →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      threadTok ∗
      (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ' : SrvRaft),
        ⌜cfgOk cfg ∧ urlsOk U ∧ γ'.vs = [id] ∧ γ'.rule = srvRule (W64 0) bootLog ∧
          γ'.boot = bootLog⌝ -∗
        letI : MemStorReg GF := ⟨γ'.reg⟩; bootstrapContract cfg U γ' id ctxs N dir) ∗
      etcdstart.commonPremises ∗ context.isClosedchanInit ∗
      etcdstart.memberBootOn γ ctxs ρ E₀ Φs id ∗
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its fresh bundle) the
      -- member's WAL directory fresh: a first start
      etcdstart.memberFreshRes go!"authkv" {} γn }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.startServer)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s ρ E₀ lg γn id γa) }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
