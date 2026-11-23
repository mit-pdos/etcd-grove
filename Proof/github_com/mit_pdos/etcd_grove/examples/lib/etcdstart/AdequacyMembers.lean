/- Lean-first (no Rocq counterpart).

# The single-process examples' closed theorems from the members' start bundles (hub step 7's L4,
2026-11-05; over the net extension since 2026-11-23)

`etcd_adequate_members_below` and `etcd_adequate_alloc_members_below`: an etcd example's closed theorem
over `goose_adequacy_start` (`Proof/runtime/Start.lean`), the body proved from the members' start bundles
(`etcdstart.memberStartRes`, `StartRes.lean`) and the other addresses' listen rights (`netAddrFree`), which
program start's lists give up to order (`etcdstart.memberStartRes_intro`, D2). A module of its own, not
`Adequacy.lean`: the start bundles' module imports the server's (the restart bundle's `srvDiskImage`),
which the raft examples importing `Adequacy.lean` must not (the witness part declares raft's names again).

(wal-link P2, 2026-11-19) With the members' WAL areas (`WalAreas.lean`): the theorems take the premise
`etcdWalAreasInit` on the file extension's initial state (each member's area a root holding no WAL), and
before the program's first step their proof allocates each member's WAL area (`progOk_walAreas`), which
the member's start bundle holds (`walAreaFresh`).

(2026-11-23, etcd-grove#28, `notes/single-process-restore.md`) Retired at the net swap with the closed
theorems that used them, restored for `etcd_safe_single_process`, `k8s_safe_single_process` and
`etcd_leaseexpiryN_safe_single_process` over the extensions `etcdNetExts` (`NetExts.lean`:
`[idIssueExt, fsExt, netExt]`; until the swap `etcdFsExts`, without the net extension). Each address's
`netAddrFree` is built from program start's `addrClaim` and the net extension's listening token, from its
start resources (`netAddrFrees_start`): the addresses are valid for the extension (`hAsOk`, `Net.addrOk`).
The network starts with no connection (`Hinitg`, the extension's `initgP`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreas
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExts
public import Robustness.Statement

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section adequacy
attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem
  etcdNetExts_hasIdIssue etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSemOk etcdFsNoErr
variable [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **`progOk` at a body resource that gives the one proved**. -/
theorem progOk_pre [hG : HeapGS .hasLC GF] (R B B' : IProp GF) (init : val) (body : Expr)
    (φ : val → Prop) (hB : B ⊢ B') (h : progOk R B' init body φ) : progOk R B init body φ := by
  obtain ⟨getInit, I, Hinit, Hbody⟩ := h
  refine ⟨getInit, I, Hinit, ?_⟩
  iintro HI Htok HB
  ihave HB' := hB $$ HB
  iapply Hbody $$ HI Htok HB'

/-- Reassociation: the start rights and the extensions' start resources. -/
theorem sep_reassoc5 (P1 P2 P3 P4 P5 : IProp GF) :
    iprop(P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5) ⊢ iprop((P1 ∗ P2 ∗ P3 ∗ P4) ∗ P5) := by
  iintro ⟨H1, H2, H3, H4, H5⟩
  iframe

/-- Reassociation: the start rights, the allocated ghost state, the WAL areas. -/
theorem sep_swap_right3 (P Q W : IProp GF) :
    iprop((P ∗ Q) ∗ W) ⊢ iprop((P ∗ W) ∗ Q) := by
  iintro ⟨⟨HP, HQ⟩, HW⟩
  iframe

/-- **The members' WAL areas, allocated before the body's first step** (wal-link P2; `wp_walAreas`):
`progOk` at a body resource with the file extension's start resources, from `progOk` at one with each
data directory's fresh WAL area, over an initial state with the areas `etcdWalAreasInit` says. -/
theorem progOk_walAreas [hG : HeapGS .hasLC GF] [go.BasicIntoValInj] (hPre : AbsDiskGpreS GF)
    (R B : IProp GF) (init : val) (body : Expr) (φ : val → Prop) (hbody : toVal body = none)
    (σ : state) (hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (Ds : List GoString) (hDs : Ds.Nodup)
    (hW : etcdWalAreasInit (extLocal Fs.fsExt σ.world) Ds) (hrb : receiptBound GF ≤ 2 ^ 62)
    (hF : ∀ d ∈ Ds, Fs.DirFits (srvWalDirOf d))
    (h : progOk R iprop(B ∗ [∗list] d ∈ Ds, memberAreasFresh d) init body φ) :
    progOk R iprop(B ∗ extsLocalStart (L := hG.goose_localGS) σ.world) init body φ := by
  obtain ⟨getInit, I, Hinit, Hbody⟩ := h
  refine ⟨getInit, I, Hinit, ?_⟩
  iintro HI Htok ⟨HB, Hl⟩
  imod etcdNetFs_start σ hfs $$ Hl with ⟨#Hinv, -, Ht⟩
  iapply wp_walAreas hPre etcdFsExts_sat etcdFsExts_satL _ hfs Ds hDs hW hF ⟨hrb⟩ body hbody _ $$ Hinv Ht
  iintro Hw
  iapply Hbody $$ HI Htok [HB Hw]
  iframe

/-- (wal-fsfix2) **The members' WAL directories fit** when their names are at most 200 bytes (what
`WalA.fits` takes at the areas' allocation). -/
theorem walDirsFit_of_names (ms : List (GoString × etcdstart.MemberAddrs)) (Ds : List GoString)
    (hD : (ms.map (fun m => memberDataDir m.1)).Perm Ds) (hmsL : ∀ m ∈ ms, m.1.length ≤ 200) :
    ∀ d ∈ Ds, Fs.DirFits (srvWalDirOf d) := by
  intro d hd
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (hD.mem_iff.2 hd)
  exact dirFits_srvWalDirOf_memberDataDir m.1 (hmsL m hm)

/-- **An etcd example's closed theorem over `goose_adequacy_start`, with ghost state allocated
first, at a thread bound of the execution** (the single-process examples' adequacy, over `etcdNetExts`;
2026-11-05, Q1 (c) of `notes/k8s-compactor-plan.md`; restored 2026-11-23 over the net extension): every
real execution of `init #() ;; body` from a fresh state with one thread and a network with no connection
(`Hinitg`), of `n` steps along which fewer than `TB` threads are live: if the main thread has finished,
its result is in `φ`; no thread is stuck; no thread has ended in a panic. The program's initializer takes
the rights to register the metric names `Ns` (distinct, `decide`d by default), its body the right to
listen at each address of `As` (distinct numeric loopback literals valid for the net extension:
`netAddrFree`, program start's `addrClaim` with the extension's token), each address's HTTP protocol
unregistered (`httpProtoFree`), the data directories `Ds` fresh, `ETCD_VERIFY` off, `T x` (ghost state
allocated first, at some `x`) and the extensions' local start resources. The WP proof at the thread
bound `max TB srvLevelK` (`srvLevels`: a serving member's gRPC runs that many levels). -/
theorem etcd_adequate_alloc_below [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hAsOk : ∀ a ∈ As, Net.addrOk a = true)
    (Ds : List GoString) (hDs : Ds.Nodup)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    {Ns : List GoString} (HNs : prometheus.namesUnclaimed (init #() ;; body) Ns)
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : dataDirsAbsent (init #() ;; body) Ds)
    (HEnv : verifyEnvOff (init #() ;; body))
    (TB n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow TB n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 →
      threadBound GF = max TB srvLevelK →
      ∃ (X : Type) (T : X → IProp GF),
        (⊢ (|==> ∃ x, T x : IProp GF)) ∧
        ∀ x, progOk (hG := heapWith hG lctx) (prometheus.namesFree (GF := GF) Ns)
          iprop((([∗list] a ∈ As, netAddrFree (hG := heapWith hG lctx) a) ∗
            ([∗list] a ∈ As, httpProtoFree a) ∗
            ([∗list] d ∈ Ds, dataDirFresh d) ∗ envVerifyOff) ∗ T x ∗
            extsLocalStart (L := (heapWith hG lctx).goose_localGS) σ.world) init body φ)
    (hNs : Ns.Nodup := by decide +kernel) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy_start (GF := GF) (n + 1) (max TB srvLevelK) _ σ g φ hφ Hinitg
    Hinitw
    Ns As Ds hNs hAs hDs hAsLit HNs HAs HDs HEnv ?_
    n κs t2 σ2 (Hsteps.mono (Nat.le_max_left _ _)) (Nat.lt_succ_self n) Hthreads
  intro hG HN HT HL
  obtain ⟨X, T, Halloc, Hp⟩ := Hprog hG HN HT
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC GF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  iintro Hg Hl Hgs Htok Hrights
  iunfold startRights at Hrights
  icases Hrights with ⟨Hns, Hcl, Hps, Hds, #Hvoff⟩
  ihave Has := netAddrFrees_start g.globalWorld As hAs hAsOk $$ [Hg Hcl]
  · iframe
  imod Halloc with ⟨%x, HTx⟩
  iapply (wp_of_progOk _ _ init body φ (Hp x)) $$ Hgs Htok [Hns] [Has Hps Hds HTx Hl]
  · iunfold prometheus.namesFree
    iexact Hns
  · iframe; iexact Hvoff

/-- **`etcd_adequate_alloc_below` without ghost state allocated first**. -/
theorem etcd_adequate_below [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hAsOk : ∀ a ∈ As, Net.addrOk a = true)
    (Ds : List GoString) (hDs : Ds.Nodup)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    {Ns : List GoString} (HNs : prometheus.namesUnclaimed (init #() ;; body) Ns)
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : dataDirsAbsent (init #() ;; body) Ds)
    (HEnv : verifyEnvOff (init #() ;; body))
    (TB n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow TB n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 →
      threadBound GF = max TB srvLevelK →
      progOk (hG := heapWith hG lctx) (prometheus.namesFree (GF := GF) Ns)
        iprop(([∗list] a ∈ As, netAddrFree (hG := heapWith hG lctx) a) ∗
          ([∗list] a ∈ As, httpProtoFree a) ∗
          ([∗list] d ∈ Ds, dataDirFresh d) ∗ envVerifyOff ∗
          extsLocalStart (L := (heapWith hG lctx).goose_localGS) σ.world) init body φ)
    (hNs : Ns.Nodup := by decide +kernel) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_adequate_alloc_below init body φ hφ As hAs hAsLit hAsOk Ds hDs σ g Hinitg Hinitw Hlctx Hinit
    Hthreads HNs HAs HDs HEnv TB n κs t2 σ2 Hsteps (hNs := hNs) fun hG HN HT =>
      ⟨Unit, fun _ => iprop(emp), by imodintro; iexists (); iempintro,
        fun _ => progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
          (by iintro ⟨⟨Ha, Hp, Hd, Hv⟩, -, Hl⟩; iframe) (Hprog hG HN HT)⟩

/-- **An etcd example's closed theorem, from its members' start bundles** (hub step 7's L4, D2):
`etcd_adequate_below`, the body proved from the start bundles of the members `ms`
(`etcdstart.memberStartRes`) and the listen rights of the other addresses `Bs`, when the members'
addresses and `Bs` are `As` up to order and the members' data directories are `Ds` up to order;
(wal-link P2) the members' WAL areas as `etcdWalAreasInit` says at start (`HWal`), each allocated before
the body's first step (`progOk_walAreas`), for a body that is not a value and an execution of fewer
than `2 ^ 62` steps (the WAL's receipts' bound); (wal-fsfix2) the members' names of at most 200 bytes
(`hmsL`, by `decide` for literal members: their WAL directories fit, `walDirsFit_of_names`). -/
theorem etcd_adequate_members_below [hPre : GooseGpreS GF] [lctx : GoLocalContext] [go.BasicIntoValInj]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (hbody : toVal body = none)
    (As : List GoString) (hAs : As.Nodup) (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hAsOk : ∀ a ∈ As, Net.addrOk a = true)
    (Ds : List GoString) (hDs : Ds.Nodup)
    (ms : List (GoString × etcdstart.MemberAddrs)) (Bs : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => memberDataDir m.1)).Perm Ds)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    {Ns : List GoString} (HNs : prometheus.namesUnclaimed (init #() ;; body) Ns)
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : dataDirsAbsent (init #() ;; body) Ds)
    (HEnv : verifyEnvOff (init #() ;; body))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) Ds)
    (TB n : Nat) (hn : n + 1 ≤ 2 ^ 62) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow TB n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 →
      threadBound GF = max TB srvLevelK →
      progOk (hG := heapWith hG lctx) (prometheus.namesFree (GF := GF) Ns)
        iprop(([∗list] m ∈ ms, etcdstart.memberStartRes (hG := heapWith hG lctx) m.1 m.2) ∗ [∗list] b ∈ Bs, netAddrFree (hG := heapWith hG lctx) b)
        init body φ)
    (hNs : Ns.Nodup := by decide +kernel)
    (hmsL : ∀ m ∈ ms, m.1.length ≤ 200 := by decide) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_adequate_below init body φ hφ As hAs hAsLit hAsOk Ds hDs σ g Hinitg Hinitw Hlctx Hinit Hthreads
    HNs HAs HDs HEnv TB n κs t2 σ2 Hsteps (hNs := hNs) fun hG HN HT =>
      progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ (sep_reassoc5 _ _ _ _ _)
        (progOk_walAreas (hG := heapWith hG lctx) ⟨hPre.goosePreGAllG⟩ _ _ init body φ hbody σ
          Hinitw.2.1 Ds hDs HWal (by rw [HN]; exact hn) (walDirsFit_of_names ms Ds hD hmsL)
          (progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
            (etcdstart.memberStartRes_intro (hG := heapWith hG lctx) ms Bs As Ds hA hD) (Hprog hG HN HT)))

/-- **`etcd_adequate_alloc_below`, from the members' start bundles** (hub step 7's L4): as
`etcd_adequate_members_below`, with ghost state allocated first. -/
theorem etcd_adequate_alloc_members_below [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    [go.BasicIntoValInj]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (hbody : toVal body = none)
    (As : List GoString) (hAs : As.Nodup) (hAsLit : ∀ a ∈ As, netAddrLit a = true)
    (hAsOk : ∀ a ∈ As, Net.addrOk a = true)
    (Ds : List GoString) (hDs : Ds.Nodup)
    (ms : List (GoString × etcdstart.MemberAddrs)) (Bs : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => memberDataDir m.1)).Perm Ds)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    {Ns : List GoString} (HNs : prometheus.namesUnclaimed (init #() ;; body) Ns)
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : dataDirsAbsent (init #() ;; body) Ds)
    (HEnv : verifyEnvOff (init #() ;; body))
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) Ds)
    (TB n : Nat) (hn : n + 1 ≤ 2 ^ 62) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow TB n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 →
      threadBound GF = max TB srvLevelK →
      ∃ (X : Type) (T : X → IProp GF),
        (⊢ (|==> ∃ x, T x : IProp GF)) ∧
        ∀ x, progOk (hG := heapWith hG lctx) (prometheus.namesFree (GF := GF) Ns)
          iprop((([∗list] m ∈ ms, etcdstart.memberStartRes (hG := heapWith hG lctx) m.1 m.2) ∗
            [∗list] b ∈ Bs, netAddrFree (hG := heapWith hG lctx) b) ∗ T x) init body φ)
    (hNs : Ns.Nodup := by decide +kernel)
    (hmsL : ∀ m ∈ ms, m.1.length ≤ 200 := by decide) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_adequate_alloc_below init body φ hφ As hAs hAsLit hAsOk Ds hDs σ g Hinitg Hinitw Hlctx Hinit
    Hthreads HNs HAs HDs HEnv TB n κs t2 σ2 Hsteps (hNs := hNs) fun hG HN HT => by
      obtain ⟨X, T, Halloc, Hp⟩ := Hprog hG HN HT
      exact ⟨X, T, Halloc, fun x => progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
        sep_assoc.2
        (progOk_walAreas (hG := heapWith hG lctx) ⟨hPre.goosePreGAllG⟩ _ _ init body φ hbody σ
          Hinitw.2.1 Ds hDs HWal (by rw [HN]; exact hn) (walDirsFit_of_names ms Ds hD hmsL)
          (progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
            (sep_swap_right3 _ _ _ |>.trans
              (sep_mono_left (etcdstart.memberStartRes_intro (hG := heapWith hG lctx) ms Bs As Ds hA hD)))
            (Hp x)))⟩

end adequacy

/-! ## The robustness statement of one process, with the network's initial state -/

section robust
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- **A single process that never crashes, with its thread bound and the extensions' initial
states** (`Robustness.Robust.of_single_below`, which drops `Robust`'s premises on the extensions'
initial states; the single-process theorems over the net extension need the network's: no connection
at start). -/
theorem robust_of_single_below_init [lctx : GoLocalContext] {e : Expr} {σ : state} {g : GlobalState}
    {threads bound : Nat}
    (h : Robustness.Fresh lctx σ → extsInitGlobal g → extsInitLocal σ g →
      ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState), n < bound →
      RealNstepsBelow threads n ([e], ((σ, g) : CfgState)) κs (t2, σ2) →
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    Robustness.Robust [] [(e, σ)] g threads bound := by
  intro hfresh hg hl
  exact Robustness.Robust.of_single_below
    (fun hf => h hf hg (hl (e, σ) (by simp))) hfresh hg hl

end robust

end EtcdGrove
end Perennial
