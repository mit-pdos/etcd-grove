/-
**The examples' shared start, for a member stopped and started again** (the restart plan's R2a,
2026-11-02, `notes/restart-plan.md`; DRAFT). Lean-first (no Rocq counterpart).

* `bootPremiseR`: `bootPremise`'s restart case, `bootstrap`'s contract on the stopped member's data
  directory (`bootstrapRestartContract`, R2c), at the same cluster.
* `memberBuiltR`: a restarted member built (restart S7.2', 2026-11-14, `notes/restart-s7-probe.md`, P3):
  `memberBuilt`'s rows at `NewServer.specR`'s post: the restart's built part `srvBuiltR` at
  `ai₀ = c₀ = 0` and the apply state `restartKV` of the image's applied log (the restart point is the
  raft wrapper's `γn.a0`), and the lessor at the snapshot it recovered (`srvLeaseRd`'s mode-`none`
  case). (Until S7.2', a DRAFT: `memberBuilt` at any starting index, which no restart could give:
  `memberBuilt` holds a first start's `isServerBuilt`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`bootstrap`'s contract on member `name`'s stopped data directory** (DRAFT; `bootPremise`'s
restart case, see the file header). -/
def bootPremiseR (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
    (dir : w64 → List GoString) (token name : GoString) (Uok : BootURLs → Prop) (id : w64) :
    IProp GF :=
  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk token name cfg ∧ Uok U ∧ γ.vs = ps ∧ γ.rule = srvRule (W64 0) bootLog ∧ γ.boot = bootLog⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapRestartContract cfg U γ id N dir)

instance bootPremiseR_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (ctxs : List (List w8)) (dir : w64 → List GoString) (token name : GoString)
    (Uok : BootURLs → Prop) (id : w64) :
    Persistent (bootPremiseR (GF := GF) N ps bootLog ctxs dir token name Uok id) := by
  unfold bootPremiseR; infer_instance

/-- **A restarted member built** (see the file header): `memberBuilt`'s rows, with the restart's
built part (`srvBuiltR`, at `NewServer.specR`'s apply state `restartKV ρ.rd.kv A` for some applied
log `A`) in place of a first start's `isServerBuilt`, and the lessor in the mode `none` at the
snapshot it recovered. -/
def memberBuiltR (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (served : Bool) : IProp GF :=
  iprop(∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
      (γrn : RNNames) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF) (at₀ : w64) (A : List EntryModel),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    srvServeStock s E ∗
    srvWatchBuilt s E ∗
    srvBuiltR s γA ci TM E ρ ρ.rd
      (srvErM false ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk) (srvTrStopK γk))
      γrn b (W64 0) at₀ (W64 0) (restartKV ρ.rd.kv A) N ∗
    srvServeBuilt s E cfg ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvLgReader s ∗
    srvReadyCloser s ∗ srvNetMember γn s id τ ∗ srvTrTok γn τ ∗
    memberPeerServeRes γn τ served ∗
    srvLeaseRd s E .none ∗ srvStop.keep s cfg E γrn γk)

/-- **The cluster's persistent facts a restart reuses** (restart S7.4, P4-a of
`notes/restart-s7-probe.md`, approved by etcd-grove-81 2026-11-14): the persistent part of
`memberBoot` at the stopped incarnation's names `ρ` (auth off, no compaction, the lease mode
`none`): its pure facts but the stand-in environment's (a restart picks a new one), the server's raft
invariant, the cluster's ids invariant and its id `0` unclaimed, the proposals' mint and the read
contexts' invariant (each over raft's names and the issued map only, which `restartNames` keeps:
`srvPropMint` holds an exclusive authority, so a restart must reuse the stopped one's), and the KV
invariant (`kvInv_restartNames`). What `BuildServer.specRestart` takes beside the image; a driver
keeps it from the cluster's allocation (`memberBoot_restartFacts`). -/
def memberRestartFacts (γ : SrvRaft) (ρ : ReqNames) (id : w64) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ ρ.rd.kv.cmp = false ∧
      lease.runCfg (GF := GF) ρ.rd.kv.lm .none⌝ ∗
    srvRaftLogInv ρ.rd.raft ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs srvFloorFacts ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗ kvInv ρ.rd.raft ρ.rd.kv)

instance memberRestartFacts_persistent (γ : SrvRaft) (ρ : ReqNames) (id : w64) :
    Persistent (memberRestartFacts (GF := GF) γ ρ id) := by
  unfold memberRestartFacts; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode in
/-- **The restart's facts, out of a first start's boot bundle** (auth off, no compaction, the lease
mode `none`), the bundle kept. -/
theorem memberBoot_restartFacts (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames)
    (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) :
    memberBoot γ ctxs ρ E₀ Φs id false .none ⊢
      memberRestartFacts γ ρ id ∗ memberBoot γ ctxs ρ E₀ Φs id false .none := by
  iintro H
  iunfold memberBoot at H
  icases H with ⟨%Hρ, Hnb, #Hsrl, #Hidc, Hkf, #Hnz, #Hpm, #Hrc, Hsh, Hwt, Hfr, Hcok, Hrev, Hrdf,
    #Hkv, Hreg, Hsd⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hρ
  isplitr
  · iunfold memberRestartFacts
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4, h5, h8, h10⟩
    iframe #
  iunfold memberBoot
  isplitr
  · ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  iframe
  iframe #

end laws


end etcdstart
end EtcdGrove
end Perennial
