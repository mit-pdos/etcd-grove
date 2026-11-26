/- Lean-first (no Rocq counterpart).

# A member machine's generation: the boot, the stopped keep and the stop (etcd_safe §5.2, S0 statements)

`plans/etcd-safe-restart-design.md` §4. **Statements only** (S0, 2026-11-26): definitions, `abbrev <name>.law : Prop`
statements of the laws the parallel tasks prove, and one theorem whose proof is a labeled `sorry` (P6's). Nothing
here is reached by a result. The deployment-specific statements (`memberDistFacts`, `memberPcD`,
`memberFirst_of_share.law`, `member_crash_boot`, `EtcdBootCAt`) are in `MemberCrashBoot.lean`.

* `memberClOk C`: the pure relations between a member's cluster names that `memberBoot_of_slice` takes (the
  start's `ClusterOk` at lease mode `.none`, no compaction, auth off).
* `memberGen_boot.law` (P3): a generation's `memberGen` gives `NewServer`'s ghost rows, of a first start
  (`memberBoot`, with the WAL area fresh) or of a restart (`memberRestartBoot` at the restarted names, with the
  image the crash left), both with the KV names' agreement with the cluster's (`kvCongr`, what `Serve_dist`/
  `Serve_distR` take).
* `memberKeepRc` (P5/P6's shared vocabulary): what a **stopped** restartable run keeps for its crash:
  `memberKeepR`'s rows without the backend's open record (`dbCrashKeep`), the backend's closed state in the
  abstract piece `KeepBc` (T10's, P6's), as `KeepB` is the open state's.
* `memberKeepS`: `memberKeep` (T7) or the stopped keep. `memberKeepInv`: the generation's keep slot, an invariant
  holding `memberKeepS` at every step of the run (design §4.3, "a slot allocated at boot"), which the crash
  obligation opens with its later credit.
* `memberStop.law` (P5, proved: `memberStop_law_holds`, by framing `HardStop.wp_proof`): `HardStop` on a started
  server, with the stop's request, keeps the slot valid: the crash-aware stop (design §4.3, row P3′). Its post is `True`: under R-A the process exits after the stop and the
  image comes back through the crash (`memberGenS_crash_law_holds`).
* `memberGenS_crash_law_holds` (P6, `sorry`): T7's crash law at the keep with the stopped case, from T7's named
  hypotheses and T10's `memberBackend.law` at the closed backend keep `KeepBc`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.BackendImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__HardStop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The boot (P3) -/

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The pure relations a member's boot reads of its cluster's names** (`memberBoot_of_slice`'s hypotheses on
the names, at the start's `ClusterOk`, lease mode `.none`, compaction off, auth off): the KV names' request-id
names the cluster's, their start values, the peers, the modes, the prefixes' apartness, a cluster outside
raft's no-snapshot mode. -/
def memberClOk (C : MemberCl) : Prop :=
  C.γk.ids.issued = C.issued ∧ C.γk.ids.wn = C.wn ∧ C.γk.ids.fs = C.fs ∧ C.γk.ids.gen = C.gen ∧
    C.γk.c0 = W64 0 ∧ C.γk.ch0 = apply.alarmChain false false false ∧ C.γk.log0 = [[], []] ∧
    C.γ.vs = C.ps ∧ C.γk.cmp = false ∧ C.γk.lm = .none ∧ kvPfxOk C.γk ∧ ¬ clusterNoSnap C.γ.cl

/-- **P3: a generation's boot** (design §4.3, row "boot of any gen"; kvnet's `kvGen_boot` without the keep, which
the run fills: `memberKeepInv`). From the boot log's marshalling (`bootMarshal`, per heap: the program's package
initialization gives it) and the generation's `memberGen`, an update to `NewServer`'s ghost rows:
* a first start (`memberFirst`): `memberBoot` at the member's raft names with its registry name `r`, auth off,
  no compaction, lease mode `.none`, and the WAL area fresh (`wal.bootRes cfg`);
* a restart (`memberRestart`): `memberRestartBoot` at the restarted names `ρ` (`restartNames ρo ρ`) of the
  incarnation `ρo` that wrote the files, and the image the crash left (`srvCrashImage`);
in both, the KV names agree with the cluster's (`kvCongr`).
To be proved from `memberBoot_of_slice` (`etcdstart/AllocN.lean:360`) and `memberRestartFacts_alloc`
(`etcdstart/Restart.lean:226`). **Note for P3:** the restart case's `kvCongr ρ.rd.kv C.γk` needs `memberRestart`
to carry `⌜kvCongr ρo.rd.kv C.γk⌝` (a pure row; `restartNames` keeps it), which T7's crash law then gives from
`memberKeepR`'s names (`k.ρo`); today neither carries it. -/
abbrev memberGen_boot.law (C : MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64) :
    Prop :=
  memberClOk C →
  ⊢ bootMarshal C.ps C.ctxs C.bl -∗ memberGen C cfg id ={⊤}=∗
    (∃ (ρ : ReqNames) (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (r : GName),
        ⌜kvCongr ρ.rd.kv C.γk⌝ ∗
        etcdstart.memberBoot { C.γ with reg := r } C.ctxs ρ E₀ Φs id false .none ∗ wal.bootRes cfg) ∨
    (∃ (ρo ρ : ReqNames) (E₀ : apply.AEnv GF) (Φs : w64 → w64 → List w8 → GName → IProp GF)
        (γ' : SrvRaft),
        ⌜(∃ r : GName, γ' = { C.γ with reg := r }) ∧ restartNames ρo ρ ∧ kvCongr ρ.rd.kv C.γk⌝ ∗
        etcdstart.memberRestartBoot γ' ρ E₀ Φs id ∗ srvCrashImage γ' ρo id cfg.DataDir')

end boot

end etcd_dist

namespace memberCrash

open Iris Iris.BI Fs backend

/-! ## The stopped keep (P5, P6) -/

section keepDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **What a stopped restartable run of member `id` keeps for a crash** (design §4.3, row P3′): `memberKeepR`'s
rows verbatim but the backend's open record `dbCrashKeep`, with the abstract piece `KeepBc k` (T10's closed
backend keep, P6's) in place of `KeepB k`. **Its intended instance** (the lead's decision, 2026-11-26, no new
trust): the durable file `backend.fileHoldsMDur k.i0 k.Dn` (`FileDur.lean:114`), which the crash-mode `DB.Close`
gives (bbolt-crash's atomic `<<dbCrashKeep γ i0 Dl Dn>> db.Close() <<fileHoldsMDur i0 Dn>>`, commit point at
`bfile_out`), with T10's image payload of `k.Dn` (`bkPayload`'s `□ bkImgAny`) and the name's crash promise. Raft's durability
(`memberDurKeep`, with the stop's token: the crash-aware stop leaves the records inside `rnDurInvK`, so D-T7-3's
`rnTakenK_stop` still refutes the stop case), the WAL area (`memberWalKeep`, across `WAL.Close`) and the snapshot
directory are unchanged by the stop. (Once T10 moves the open record into `KeepB`, as BackendImage.lean's header
plans, `memberKeepRc C cfg id KeepBc` is `memberKeepR C cfg id KeepBc` and this definition goes.) -/
def memberKeepRc (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepBc : MemberKN GF → IProp GF) : IProp GF :=
  iprop(∃ k : MemberKN GF,
    ⌜(∃ r : GName, k.γ = { C.γ with reg := r }) ∧ k.h.dir = srvWalDirOf cfg.DataDir' ∧
      k.h.md = walMetaEnc id k.cid ∧ k.γ.snapLoc id = some k.γd ∧ (∃ c, theFs GF = some c) ∧
      (cfg.DataDir', k.jd) ∈ k.h.R ∧ (k.h.r, k.h.jr) ∈ k.h.R ∧ k.h.r ≠ cfg.DataDir' ∧
      IsUnder k.h.r k.h.dir ∧
      config.snapDirOf cfg.DataDir' = joinPath cfg.DataDir' [go!"member", go!"snap"] ∧
      ∀ i, PathFits (snap.snapDBPath (config.snapDirOf cfg.DataDir') i)⌝ ∗
    etcdstart.memberRestartFacts k.γ k.ρo id ∗ memberDurKeep k.γ id k.νk k.h ∗ memberWalKeep k.h ∗
    memberSnapKeep k cfg.DataDir' ∗ osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ KeepBc k)

end keepDefs

section stopFrame
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- `HardStop.spec` with any extra resource `P` in the precondition (framed and dropped). -/
theorem hardStop_frame (s : Loc) (E : apply.AEnv GF) (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString)
    (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvStopRight s E γ ρ id dd ∗ srvStopReq s E ρ dd ∗ P }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"HardStop")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨Hpkg, Hr, Hq, -⟩ HΦ
  iapply EtcdServer.HardStop.wp_proof s E γ ρ id dd $$ [Hpkg Hr Hq]
  · iframe Hpkg Hr Hq
  inext
  iintro -
  iapply HΦ
  itrivial

end stopFrame

section keep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **What the run of generation `L` keeps for its crash, the stopped case included**: T7's `memberKeep` (a first
generation's `KeepF L`, or a running restartable run's `memberKeepR` with the open backend keep `KeepB L`), or a
stopped run's (`memberKeepRc` with the closed backend keep `KeepBc L`), with the cluster's facts and the second
later credit as `memberKeep`'s. -/
def memberKeepS (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepF : GooseLocalGS GF → IProp GF) (KeepB KeepBc : GooseLocalGS GF → MemberKN GF → IProp GF)
    (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS HasLC.hasLC GF := ⟨G, etcd_dist.atCtx L⟩
  iprop(memberKeep C cfg id KeepF KeepB L ∨
    (memberClusterFacts C ∗ £ 1 ∗ memberKeepRc C cfg id (KeepBc L)))

/-- The namespace of a generation's keep slot. -/
def memberKeepN : Namespace := nroot.@"memberKeep"

/-- **The generation `L`'s keep slot** (persistent; design §4.3, "a slot allocated at boot"): an invariant that
holds `memberKeepS` at every step of the run. The run updates it in place (atomically, where a keep piece moves:
`NewServer`'s, the backend's commits and close); the crash obligation of `CrashBootWpGT` opens it with its credit
and passes `memberKeepS … L` to the crash law. -/
def memberKeepInv (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepF : GooseLocalGS GF → IProp GF) (KeepB KeepBc : GooseLocalGS GF → MemberKN GF → IProp GF)
    (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS HasLC.hasLC GF := ⟨G, etcd_dist.atCtx L⟩
  inv memberKeepN (memberKeepS C cfg id KeepF KeepB KeepBc L)

/-- **P5: the crash-aware stop** (design §4.3, row P3′; `HardStop.specK`): in a generation `L` whose keep slot
holds `memberKeepS`, `s.HardStop()` with the right to stop `s` (`srvStopRight`, `Start`'s) and the stop's request
(`srvStopReq`: the boot evidence, the scope `srvStop.scope`, the data directory and the serving readers, which
`GracefulStop_dist` gives back) returns, and the slot stays valid at every step: the shutdown keeps raft's records
inside `rnDurInvK` (`InvWalCrash.lean:256`) and the WAL area's `walInv` across `WAL.Close`, and the backend's close
moves the slot from the open keep (`KeepB`) to the stopped one (`KeepBc`) at `DB.Close`'s commit point (bbolt-crash's
crash-mode `DB.Close`, `<<dbCrashKeep γ i0 Dl Dn>> db.Close() <<fileHoldsMDur i0 Dn>>`: before it the open record
and `dbCrash`, after it the durable file). Proved (`memberStop_law_holds`) from
`HardStop.wp_proof` by framing: that shutdown runs in `run`'s deferred code, not in `HardStop`, so its crash-aware
obligation is the crash-aware `run`'s (P5's finding, 2026-11-26). The post is `True`: the member's process exits after
the stop (R-A), and the next generation gets the image through the crash (`memberGenS_crash_law_holds`). -/
abbrev memberStop.law (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepF : GooseLocalGS GF → IProp GF) (KeepB KeepBc : GooseLocalGS GF → MemberKN GF → IProp GF) : Prop :=
  ∀ (L : GooseLocalGS GF) (s : Loc) (E : apply.AEnv GF) (γ : SrvRaft) (ρ : ReqNames) (dd : GoString),
    L.goose_go_local_context = lctx →
    letI : HeapGS HasLC.hasLC GF := ⟨G, etcd_dist.atCtx L⟩;
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvStopRight s E γ ρ id dd ∗ srvStopReq s E ρ dd ∗
        memberKeepInv C cfg id KeepF KeepB KeepBc L }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"HardStop")) (Val #()))
    {{ RET #(); True }}

/-- **P5: `memberStop.law` holds**, from `EtcdServer.HardStop.wp_proof` with the slot framed. `HardStop` itself only
sends the stop request on `s.stop` and waits for `done` (`EtcdServer__HardStop.lean`); the shutdown (raft's stop,
`WAL.Close`, `Cleanup`'s backend close) runs in `run`'s deferred code, on resources `run` holds since `Start`. So
`HardStop` touches no keep piece, and the slot (an invariant) stays valid by framing. What the slot's contents
say at a crash during or after that shutdown is the crash-aware `run`'s obligation (through the spec that
starts the server with the slot), not `HardStop`'s. -/
theorem memberStop_law_holds (C : etcd_dist.MemberCl) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (id : w64) (KeepF : GooseLocalGS GF → IProp GF) (KeepB KeepBc : GooseLocalGS GF → MemberKN GF → IProp GF) :
    memberStop.law C cfg id KeepF KeepB KeepBc := by
  intro L s E γ ρ dd hL
  -- the triple's `WP` is at `L`, its resources at `atCtx L`: the same generation, by `hL` (structure eta)
  subst hL
  exact hardStop_frame (hG := ⟨G, L⟩) s E γ ρ id dd _

end keep

section main
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [Sf : ExtSemantics fsExt] [Of : FsSemOk] [Hf : HasExt fsExt] [Hi : HasExt idIssueExt]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **P6: T7's crash law with the stopped case** (S0 stub, `sorry`): `memberGen_crash.law` at `memberKeepS`, from
`memberGen_crash_law_holds`'s hypotheses (the crash premise's W1 `hQ` and bbolt's `hA1`, B4 `hB4`, B1 `hB1`,
`hB1n`) for `memberKeep`'s cases, and for the stopped case T10's `memberBackend.law` at the closed backend keep
`KeepBc` (`hBc`: the closed-backend case of design §4.4, `BackendImage.lean:130`, proved by P6 at `KeepBc`'s
instance through the proved `fileHoldsMDur_crash`, `FileDur.lean:244`: no axiom). The stopped case is T7's restart case
with `hBc` in place of `dbCrash` and `hB1`: the same `memberDurKeep`, `memberWalKeep`, snapshot directory and
spine steps (`memberDur_crash`, `memberWal_crash`, `snapDir_crash`), then `crashImage_of`. -/
theorem memberGenS_crash_law_holds (C : etcd_dist.MemberCl)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepF : GooseLocalGS GF → IProp GF) (KeepB KeepBc : GooseLocalGS GF → MemberKN GF → IProp GF)
    (Q : OsState → OsState → Prop)
    (hQ : ∀ st st', Q st st' → WalFs.W1 walCodec st st')
    (hA1 : ∀ i0 st st', Q st st' → backend.BoltCrashWhole (· = i0) st st')
    (hB4 : memberFirstCrash.law C cfg id KeepF Q) (hB1 : memberImage.law cfg id KeepB)
    (hB1n : memberDbNamed.law KeepB) (hBc : bkImage.memberBackend.law cfg id KeepBc) :
    etcd_dist.memberGen_crash.law C cfg id (memberKeepS C cfg id KeepF KeepB KeepBc) Q := by
  sorry -- S0 stub (P6): see the docstring

end main

end memberCrash
end EtcdGrove
end Perennial
