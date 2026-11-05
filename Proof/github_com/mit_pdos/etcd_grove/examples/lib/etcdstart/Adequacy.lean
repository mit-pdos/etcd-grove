/- Lean-first (no Rocq counterpart).

# The examples' closed theorems, generically (2026-10-22, D36)

Every example's closed theorem goes the same way from its `Main`'s spec to "no thread stuck, no
panic, the main thread's result in a set": Perennial's adequacy theorem (`goose_adequacy`, or
`goose_adequacy_start`, `Proof/runtime/Start.lean`, which also hands the WP proof program start's
rights) at the receipt bound `n + 1` and the thread bound `n + 2` of an execution of `n` steps
from one thread (`realThreadsBelow_of_one`); the package state empty (`IsInit`), from which the
right to initialize (`ownInitializing`); the package's initializer, then the program's body; and
`UnrecoveredPanic`'s exclusion of a final `PanicV` turned into `isPanic = false`.

* `adequate_of_unrecovered`: the last step, pure.
* `init_adequate`: a program `init #() ;; body` over `goose_adequacy`, from its initializer's
  triple and its body's WP (`progOk`, at every ghost-state instance at the state's local
  context). Generic in Perennial's terms: a proposal for Perennial (`notes/perennial-changes.md`).
* `etcd_adequate`: the same over `goose_adequacy_start`, for a program whose initializer takes
  the read package's two metric names (`read.readRegPerm`: every etcd example's) and whose body
  takes the addresses `As` (`startProgOk`).
* `etcd_adequate_members` (and `etcd_adequate_alloc_members`, over `etcd_adequate_alloc`;
  2026-11-05, hub step 7's L4): the same, the body taking the members' start bundles
  (`etcdstart.memberStartRes`) and the other addresses' listen rights, which program start's lists
  give up to order (`etcdstart.memberStartRes_intro`).

Each example's closed theorem is an instance: its proof gives its initializer's triple
(`wp_initialize'`) and proves its body from its `Main`'s spec, at its ghost-state bundle.
-/
module

public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Metrics
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **`UnrecoveredPanic` excludes a final panic** (pure): adequacy's third conclusion, as the
examples state it (no thread has ended in a panic value). -/
theorem adequate_of_unrecovered [GooseExts] {t2 : List Expr} {P Q : Prop}
    (H : P ∧ Q ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    P ∧ Q ∧ (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine ⟨H.1, H.2.1, fun v hv => ?_⟩
  cases h : v.isPanic
  · rfl
  · obtain ⟨p, rfl⟩ := val.isPanic_eq_true h
    exact absurd (UnrecoveredPanic.panic p) (H.2.2 _ hv)

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **A ghost-state instance at the local context `lctx`** (the examples state their hypotheses
over every instance whose Go local context is the semantics' own). -/
abbrev heapWith (hG : HeapGS .hasLC GF) (lctx : GoLocalContext) : HeapGS .hasLC GF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-- **The right to initialize, from the empty package state.** -/
theorem ownInitializing_of_empty [hG : HeapGS .hasLC GF] (getInit : GoString → IProp GF) :
    ownGoState (∅ : GMap GoString Bool) ⊢ ownInitializing getInit := by
  iintro Hgs
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  iexists ∅
  iframe Hgs
  imodintro
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- **A program `init #() ;; body`, proved** (at the instance `hG`): the initializer's triple
for some post-initialization map `getInit`, from the right to initialize and `R`, giving the
package's predicate `I`; and the body's WP from `I`, the main thread's token and `B`. -/
def progOk [hG : HeapGS .hasLC GF] (R B : IProp GF) (init : val) (body : Expr) (φ : val → Prop) :
    Prop :=
  ∃ (getInit : GoString → IProp GF) (I : IProp GF),
    ({{ ownInitializing getInit ∗ R }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getInit ∗ I }}) ∧
    (⊢ I -∗ threadTok -∗ B -∗ WP body @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})

/-- `progOk`'s WP of the whole program, from the empty package state. -/
theorem wp_of_progOk [hG : HeapGS .hasLC GF] (R B : IProp GF) (init : val) (body : Expr)
    (φ : val → Prop) (h : progOk R B init body φ) :
    ⊢ ownGoState (∅ : GMap GoString Bool) -∗ threadTok -∗ R -∗ B ={⊤}=∗
      WP (init #() ;; body) @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  obtain ⟨getInit, I, Hinit, Hbody⟩ := h
  iintro Hgs Htok HR HB
  ihave Hown := (ownInitializing_of_empty getInit) $$ Hgs
  imodintro
  wp_apply Hinit $$ [Hown HR] as ⟨-, HI⟩
  · iframe
  iapply Hbody $$ HI Htok HB

/-- **A program `init #() ;; body` whose initializer takes no resource, proved** (`progOk`'s
form for a program that registers no metric name and listens on no address). -/
def progOk0 [hG : HeapGS .hasLC GF] (init : val) (body : Expr) (φ : val → Prop) : Prop :=
  ∃ (getInit : GoString → IProp GF) (I : IProp GF),
    ({{ ownInitializing getInit }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getInit ∗ I }}) ∧
    (⊢ I -∗ threadTok -∗ WP body @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})

/-- **A program's closed theorem over `goose_adequacy`** (see the file header): every real
execution of `init #() ;; body` from a fresh state with one thread, of `n` steps: if the main
thread has finished, its result is in `φ`; no thread is stuck; no thread has ended in a panic. -/
theorem init_adequate [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      progOk0 (hG := heapWith hG lctx) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply adequate_of_unrecovered
  refine goose_adequacy (GF := GF) (n + 1) (n + 2) _ σ g φ hφ Hinitg Hinitw ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  have Hp := Hprog hG HN HT
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC GF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  obtain ⟨getInit, I, Hinitwp, Hbody⟩ := Hp
  iintro - - Hgs Htok
  ihave Hown := (ownInitializing_of_empty getInit) $$ Hgs
  imodintro
  wp_apply Hinitwp $$ Hown as ⟨-, HI⟩
  iapply Hbody $$ HI Htok

/-- **An etcd example's closed theorem over `goose_adequacy_start`, with ghost state allocated
first** (2026-11-05, Q1 (c) of `notes/k8s-compactor-plan.md`): as `etcd_adequate` below, for a
program whose proof needs ghost state allocated before its initializer's triple is chosen (a ghost
name an instance of the proof carries, as the compactor registry's, `k8s.CompactorRegistry`):
`T x` is allocated (at some `x`), then given to the body with `B`, and the program's proof may
depend on `x`. -/
theorem etcd_adequate_alloc [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (Ds : List GoString) (hDs : Ds.Nodup)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (HNs : prometheus.namesUnclaimed (init #() ;; body)
      [read.slowReadIndexName, read.readIndexFailedName])
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : walDirsAbsent (init #() ;; body) Ds)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      ∃ (X : Type) (T : X → IProp GF),
        (⊢ (|==> ∃ x, T x : IProp GF)) ∧
        ∀ x, progOk (hG := heapWith hG lctx) (read.readRegPerm (GF := GF))
          iprop((([∗list] a ∈ As, netAddrFree a) ∗ ([∗list] a ∈ As, httpProtoFree a) ∗
            ([∗list] d ∈ Ds, walDirFresh d)) ∗ T x) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply adequate_of_unrecovered
  refine goose_adequacy_start (GF := GF) (n + 1) (n + 2) _ σ g φ hφ Hinitg Hinitw
    [read.slowReadIndexName, read.readIndexFailedName] As Ds (by decide) hAs hDs HNs HAs HDs ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  obtain ⟨X, T, Halloc, Hp⟩ := Hprog hG HN HT
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC GF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  iintro - - Hgs Htok Hrights
  iunfold startRights at Hrights
  icases Hrights with ⟨Hns, Has, Hps, Hds⟩
  imod Halloc with ⟨%x, HTx⟩
  iapply (wp_of_progOk _ _ init body φ (Hp x)) $$ Hgs Htok [Hns] [Has Hps Hds HTx]
  · iunfold read.readRegPerm
    icases BigSepL.bigSepL_cons.1 $$ Hns with ⟨Hn1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hn2, -⟩
    iframe
  · iframe

/-- **An etcd example's closed theorem over `goose_adequacy_start`** (see the file header): as
`init_adequate`, for a program whose initializer takes the read package's two metric names and
whose body the addresses `As`, each with its HTTP protocol unregistered (`httpProtoFree`, 2026-10-24,
rafthttp stage 6a, D39a), and (2026-11-03, the WAL's API) the members' WAL directories `Ds` fresh
(`walDirFresh`). -/
theorem etcd_adequate [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (Ds : List GoString) (hDs : Ds.Nodup)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (HNs : prometheus.namesUnclaimed (init #() ;; body)
      [read.slowReadIndexName, read.readIndexFailedName])
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : walDirsAbsent (init #() ;; body) Ds)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      progOk (hG := heapWith hG lctx) (read.readRegPerm (GF := GF))
        iprop(([∗list] a ∈ As, netAddrFree a) ∗ ([∗list] a ∈ As, httpProtoFree a) ∗
          ([∗list] d ∈ Ds, walDirFresh d)) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply adequate_of_unrecovered
  refine goose_adequacy_start (GF := GF) (n + 1) (n + 2) _ σ g φ hφ Hinitg Hinitw
    [read.slowReadIndexName, read.readIndexFailedName] As Ds (by decide) hAs hDs HNs HAs HDs ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  have Hp := Hprog hG HN HT
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC GF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  iintro - - Hgs Htok Hrights
  iunfold startRights at Hrights
  icases Hrights with ⟨Hns, Has, Hps, Hds⟩
  iapply (wp_of_progOk _ _ init body φ Hp) $$ Hgs Htok [Hns] [$Has $Hps $Hds]
  iunfold read.readRegPerm
  icases BigSepL.bigSepL_cons.1 $$ Hns with ⟨Hn1, Hr⟩
  icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hn2, -⟩
  iframe

/-- **`progOk` at a body resource that gives the one proved**. -/
theorem progOk_pre [hG : HeapGS .hasLC GF] (R B B' : IProp GF) (init : val) (body : Expr)
    (φ : val → Prop) (hB : B ⊢ B') (h : progOk R B' init body φ) : progOk R B init body φ := by
  obtain ⟨getInit, I, Hinit, Hbody⟩ := h
  refine ⟨getInit, I, Hinit, ?_⟩
  iintro HI Htok HB
  ihave HB' := hB $$ HB
  iapply Hbody $$ HI Htok HB'

/-- **An etcd example's closed theorem, from its members' start bundles** (hub step 7's L4, D2):
`etcd_adequate`, the body proved from the start bundles of the members `ms`
(`etcdstart.memberStartRes`) and the listen rights of the other addresses `Bs`, when the members'
addresses and `Bs` are `As` up to order and the members' WAL directories are `Ds` up to order. -/
theorem etcd_adequate_members [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (Ds : List GoString) (hDs : Ds.Nodup)
    (ms : List (GoString × etcdstart.MemberAddrs)) (Bs : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => etcdstart.memberWalDir m.1)).Perm Ds)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (HNs : prometheus.namesUnclaimed (init #() ;; body)
      [read.slowReadIndexName, read.readIndexFailedName])
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : walDirsAbsent (init #() ;; body) Ds)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      progOk (hG := heapWith hG lctx) (read.readRegPerm (GF := GF))
        iprop(([∗list] m ∈ ms, etcdstart.memberStartRes m.1 m.2) ∗ [∗list] b ∈ Bs, netAddrFree b)
        init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_adequate init body φ hφ As hAs Ds hDs σ g Hinitg Hinitw Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps fun hG HN HT =>
      progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
        (etcdstart.memberStartRes_intro ms Bs As Ds hA hD) (Hprog hG HN HT)

/-- **`etcd_adequate_alloc`, from the members' start bundles** (hub step 7's L4): as
`etcd_adequate_members`, with ghost state allocated first. -/
theorem etcd_adequate_alloc_members [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (Ds : List GoString) (hDs : Ds.Nodup)
    (ms : List (GoString × etcdstart.MemberAddrs)) (Bs : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => etcdstart.memberWalDir m.1)).Perm Ds)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (HNs : prometheus.namesUnclaimed (init #() ;; body)
      [read.slowReadIndexName, read.readIndexFailedName])
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : walDirsAbsent (init #() ;; body) Ds)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = n + 2 →
      ∃ (X : Type) (T : X → IProp GF),
        (⊢ (|==> ∃ x, T x : IProp GF)) ∧
        ∀ x, progOk (hG := heapWith hG lctx) (read.readRegPerm (GF := GF))
          iprop((([∗list] m ∈ ms, etcdstart.memberStartRes m.1 m.2) ∗
            [∗list] b ∈ Bs, netAddrFree b) ∗ T x) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_adequate_alloc init body φ hφ As hAs Ds hDs σ g Hinitg Hinitw Hlctx Hinit Hthreads HNs HAs
    HDs n κs t2 σ2 Hsteps fun hG HN HT => by
      obtain ⟨X, T, Halloc, Hp⟩ := Hprog hG HN HT
      exact ⟨X, T, Halloc, fun x => progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
        (sep_mono_left (etcdstart.memberStartRes_intro ms Bs As Ds hA hD)) (Hp x)⟩

end adequacy

end EtcdGrove
end Perennial
