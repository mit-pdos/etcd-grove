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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc

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
      (γrn : RNNames GF) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF) (at₀ : w64) (A : List EntryModel),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0⌝ ∗
    srvServeStock s E ∗
    srvWatchBuilt s E ∗
    srvBuiltR s γA ci TM E ρ ρ.rd
      (srvEr ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk) (srvTrStopK γk))
      γrn b (W64 0) at₀ (W64 0) (restartKV ρ.rd.kv A) N ∗
    srvServeBuilt s E cfg ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvMonitorRes s ∗
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
invariant (`kvInv_restartNames`); (restart S7.4, 2026-11-14) and the stopped incarnation's key
registered (`idKeyFactAt`), from which the claims' invariant gives its prefix good (`idPfxOk`,
`idKeyFact_pfxOk`), what a new incarnation's key needs (`idIncarnation_alloc`). What
`BuildServer.specRestart` takes beside the image; a driver keeps it from the cluster's allocation
(`memberBoot_restartFacts`). -/
def memberRestartFacts (γ : SrvRaft) (ρ : ReqNames) (id : w64) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ ρ.rd.kv.cmp = false ∧
      lease.runCfg (GF := GF) ρ.rd.kv.lm .none⌝ ∗
    -- (auth-lease S4, 2026-11-16) the cluster outside raft's no-snapshot mode (`RestartNode`'s)
    ⌜¬ clusterNoSnap γ.cl⌝ ∗
    srvRaftLogInv ρ.rd.raft ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs ρ.ids.gen srvFloorFacts ∗
    idPfxInv ρ.ids.gen ρ.ids.pfx ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗ kvInv ρ.rd.raft ρ.rd.kv ∗
    ∃ x : GName, idKeyFactAt ρ.ids.fs ρ.ids.key x)

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
  icases H with ⟨%Hρ, %Hnsn, Hnb, #Hsrl, #Hidc, #Hpfxi, #Hkf, #Hnz, #Hpm, #Hrc, Hsh, Hwt, Hfr, Hcok, Hrev,
    Hrdf, #Hkv, Hreg, Hsd⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hρ
  isplitr
  · iunfold memberRestartFacts
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4, h5, h8, h10⟩
    isplitr
    · ipureintro; exact Hnsn
    iframe #
  iunfold memberBoot
  isplitr
  · ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  isplitr
  · ipureintro; exact Hnsn
  iframe
  iframe #

end laws


section restartAlloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **What a restarted incarnation's `NewServer` takes of the ghost state** (restart S7.4; auth off,
no compaction, the lease mode `none`): `NewServer.specR`'s rows at the incarnation's names `ρ` and
stand-in environment `E₀` but the image and the restart-only rows: `memberBoot`'s, without the
node's boot token, the storage registry and the snapshot directory (the image holds them). -/
def memberRestartBoot (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧
      Φs ρ.ids.pfx = srvFloorFact E₀ ∧ E₀.cmp = false ∧ ρ.rd.kv.cmp = false ∧
      E₀.Nx = srvApi.kvNx ρ.rd false ∧ lease.runCfg (GF := GF) ρ.rd.kv.lm .none⌝ ∗
    -- (auth-lease S4, 2026-11-16) the cluster outside raft's no-snapshot mode (`RestartNode`'s)
    ⌜¬ clusterNoSnap γ.cl⌝ ∗
    srvRaftLogInv ρ.rd.raft ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt ρ.ids.wn ρ.ids.fs ρ.ids.gen srvFloorFacts ∗
    idPfxInv ρ.ids.gen ρ.ids.pfx ∗
    idKeyFactAt ρ.ids.fs ρ.ids.key E₀.γs.slog ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
    idShare ρ.ids ∗ idWaitTok ρ.ids ∗
    srvApi.newServerStoreFreshA E₀.γs ∗
    ghostMapAuth ρ.rd.kv.cok 1 (∅ : GMap w64 mvcc.Log) ∗
    ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
    srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv)

open Iris.ProofMode in
/-- **A registered key's prefix is good** (the claims' invariant: every key of the keys' map has a
good prefix, and the facts' map has the keys' domain). -/
theorem idKeyFact_pfxOk {X : Type} [Pos.Countable X] (issued cnt wn fs gen : GName)
    (Φs : X → w64 → List w8 → GName → IProp GF) (k : IdKey) (x : X) (E : CoPset)
    (HE : ↑idClusterN ⊆ E) :
    ⊢ idClusterInv (GF := GF) issued cnt wn fs gen Φs -∗ idKeyFactAt fs k x ={E}=∗ ⌜idPfxOk k.1⌝ := by
  iintro #Hcl #Hk
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, %R, %Fm, >HI, >HC, >HR, >HF, >%Hok, #HFs, >#HG⟩
  iunfold idKeyFactAt at Hk
  ihave %Hlk := ghost_map_lookup $$ HF Hk
  imod Hclose $$ [HI HC HR HF] with -
  · inext
    iexists I, C, R, Fm
    iframe HI HC HR HF HFs HG
    ipureintro; exact Hok
  imodintro
  ipureintro
  obtain ⟨-, h2, -, -, -, h6⟩ := Hok
  have hs : (C !! k).isSome := (h6 k).2 (by simp [Hlk])
  cases hc : C !! k with
  | none => simp [hc] at hs
  | some e => exact (h2 k e hc).1

/-- **A restarted incarnation's names** (restart S7.4, `memberRestartFacts_alloc`): the stopped
incarnation's `ρ` with new read names' rows (`applied`, `committed`, `notifier`, `logs`, `pend`), a
new certificate map `cok` and applied height `hi`, and the ids at a new incarnation number `inc`
with new slot and pending maps (`slot`, `ipend`). -/
def restartReqNames (ρ : ReqNames) (cursor applied committed notifier logs pend cok hi slot ipend : GName)
    (inc : Nat) : ReqNames :=
  let ids : IdNames := ⟨ρ.ids.issued, ρ.ids.cnt, slot, ρ.ids.pfx, ρ.ids.wn, inc, ρ.ids.fs, ipend, ρ.ids.gen⟩
  let kv : KVNames := ⟨ρ.rd.kv.st, ρ.rd.kv.c0, ρ.rd.kv.ch0, ρ.rd.kv.log0, cok, hi, ids, ρ.rd.kv.hist,
    ρ.rd.kv.cmp, ρ.rd.kv.rlog, ρ.rd.kv.cret, ρ.rd.kv.lm, ρ.rd.kv.gps⟩
  ⟨ρ.wait, ⟨cursor, applied, committed, notifier, logs, pend, ρ.rd.raft, kv⟩⟩

theorem restartReqNames_restartNames (ρ : ReqNames)
    (cursor applied committed notifier logs pend cok hi slot ipend : GName) (inc : Nat) :
    restartNames ρ (restartReqNames ρ cursor applied committed notifier logs pend cok hi slot ipend inc) :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩, rfl, rfl⟩

open Iris.ProofMode in
/-- **A restarted incarnation's names, allocated** (restart S7.4): from the cluster's persistent
facts at the stopped incarnation's names `ρ`, new names `ρ'` that agree with `ρ` where the cluster
sees them (`restartNames`; `restartReqNames`): raft's names, the KV names but the certificate map
`cok` and the applied height `hi`, the claims' map, counters, wait names, facts' map and prefix, at a
new incarnation key (`idIncarnation_alloc`, its number above every key's) with new slot and pending
maps; new read names' rows (`srvReadNamesFreshNK`); and a new stand-in environment `E₀` over a fresh
store's names (`newServerNames_alloc`), the key's facts at its store index. The persistent facts
carry over (`srvPropMint_congr`, `kvInv_congr`). -/
theorem memberRestartFacts_alloc (hne : mvcc.api.names_nonempty.law) (γ : SrvRaft) (ρ : ReqNames)
    (id : w64) :
    ⊢ memberRestartFacts (GF := GF) γ ρ id ={⊤}=∗
      ∃ (ρ' : ReqNames) (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF),
        ⌜restartNames ρ ρ'⌝ ∗ memberRestartBoot γ ρ' E₀ Φs id := by
  iintro #Hf
  iunfold memberRestartFacts at Hf
  icases Hf with ⟨%Hρ, %Hnsn, #Hsrl, #Hidc, #Hpfxi, #Hnz, #Hpm, #Hrc, #Hkv, %x, #Hkf⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hρ
  imod (idKeyFact_pfxOk _ _ _ _ _ _ _ _ ⊤ (by simp)) $$ Hidc Hkf with %Hpok
  imod newServerNames_alloc (GF := GF) with ⟨%γs, %cok, %rev, Hidx, Hcok, Hrev⟩
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  imod (idIncarnation_alloc (GF := GF) _ _ _ _ _ srvFloorFacts ρ.ids.pfx γs.slog ⊤ (by simp) Hpok)
    $$ Hidc with ⟨%inc, Hk, Hwt, #Hkf'⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γsl, Hsl⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γpd, Hpend⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%cursor, Hcursor, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γa, Ha, -⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γc, Hc, -⟩
  imod ghostVar_alloc (GF := GF) ((null, ⟨γa, γa⟩) : Loc × NeedNames) with ⟨%γn, Hn⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := mvcc.Log) with ⟨%γl, Hl⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γp, Hpd⟩
  imod ghostVar_alloc (GF := GF) ρ.rd.kv.log0.length with ⟨%γhi, Hhi⟩
  have hR := restartReqNames_restartNames ρ cursor γa γc γn γl γp cok γhi γsl γpd inc
  imodintro
  iexists restartReqNames ρ cursor γa γc γn γl γp cok γhi γsl γpd inc,
    env₀ γm γs rev (srvApi.kvNx (restartReqNames ρ cursor γa γc γn γl γp cok γhi γsl γpd inc).rd false) false,
    (fun _ => srvFloorFacts γs.slog)
  isplitr
  · ipureintro; exact hR
  iunfold memberRestartBoot
  rw [kvInv_congr _ _ _ hR.2.1.symm, hR.1,
    srvPropMint_congr _ (restartReqNames ρ cursor γa γc γn γl γp cok γhi γsl γpd inc).ids ρ.ids rfl]
  simp only [restartReqNames, env₀, ReqNames.ids, ReqNames.kv, IdNames.key]
  isplitr
  · ipureintro
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_, h6, ?_, h7⟩ <;> first | trivial | rfl
  isplitr
  · ipureintro; exact Hnsn
  iframe Hsrl Hidc Hpfxi Hkf' Hpm Hrc Hkv Hidx Hcok Hrev
  isplitr
  · iunfold idNoZero; iunfold idNoZero at Hnz; iexact Hnz
  isplitl [Hk Hsl Hpend]
  · iunfold idShare
    iframe Hk Hsl Hpend
  isplitl [Hwt]
  · iexact Hwt
  iunfold srvReadNamesFreshNK
  iframe Hcursor Ha Hc Hl Hpd Hhi
  iexists _
  iexact Hn

end restartAlloc


end etcdstart
end EtcdGrove
end Perennial
