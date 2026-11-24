/- Lean-first (no Rocq counterpart).

# The examples' closed theorems, generically (2026-10-22, D36)

Every example's closed theorem goes the same way from its `Main`'s spec to "no thread stuck, no
panic, the main thread's result in a set": Perennial's adequacy theorem (`goose_adequacy`, or
`goose_adequacy_start`, `Proof/runtime/Start.lean`, which also hands the WP proof program start's
rights) at the receipt bound `n + 1` and a thread bound at least `n + 2` of an execution of `n`
steps from one thread (`realThreadsBelow_of_one`): `n + 2` for `init_adequate`, `max (n + 2)
srvLevelK` for the etcd lemmas (revoke-open, 2026-11-06: the server's revocation uses
`srvRevokeK` levels of a thread token, `srvRevokeLevels`; per-type stage B2, 2026-11-11, r5 §3.3:
written with `srvLevelK`, the levels a serving member uses, `srvRevokeK + 1` since k8s 7f-4); the package
state empty (`IsInit`), from which the right to initialize (`ownInitializing`); the package's initializer, then the program's body; and
`UnrecoveredPanic`'s exclusion of a final `PanicV` turned into `isPanic = false`.

* `adequate_of_unrecovered`: the last step, pure.
* `init_adequate_below`: a program `init #() ;; body` over `goose_adequacy_below` (Perennial's
  `AdequacyAlong.lean`: the thread bound `T` a property of the execution, `RealNstepsBelow T n`, not
  of every execution of `n` steps), from its initializer's triple and its body's WP (`progOk`, at
  every ghost-state instance at the state's local context). `init_adequate`: the same over all
  executions of `n` steps, at `T = n + 2`. Generic in Perennial's terms: a proposal for Perennial
  (`notes/perennial-changes.md`).
* (net-swap, etcd-dist D2, 2026-11-22) `etcd_adequate` and its variants (over `goose_adequacy_start`, with
  the metric names' and the addresses' rights) went with the closed theorems that used them (`etcd_safe`,
  `k8s_safe`, leaseexpiryN's; `notes/etcd-dist-plan.md` §9, "D2's `net` half").

Each example's closed theorem is an instance: its proof gives its initializer's triple
(`wp_initialize'`) and proves its body from its `Main`'s spec, at its ghost-state bundle.
-/
module

public import Proof.runtime.Start
public import Proof.runtime.InitEmpty
public import Perennial.GooseLang.AdequacyAlong
public import Proof.runtime.Threads
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Metrics
public import Proof.runtime.PkgInitRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeLevels
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TopLevelDefs

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

/-- **A program's closed theorem over `goose_adequacy_below`** (see the file header): every real
execution of `init #() ;; body` from a fresh state with one thread, of `n` steps, along which fewer
than `T` threads are ever live at once (`RealNstepsBelow`): if the main thread has finished, its
result is in `φ`; no thread is stuck; no thread has ended in a panic. The body's WP is proved at the
thread bound `T`, whatever the step count. -/
theorem init_adequate_below [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (T n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = T →
      progOk0 (hG := heapWith hG lctx) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy_below (GF := GF) (n + 1) T _ σ g φ hφ Hinitg Hinitw ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads
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

/-- **A program's closed theorem over `goose_adequacy`** (see the file header): every real
execution of `init #() ;; body` from a fresh state with one thread, of `n` steps: if the main
thread has finished, its result is in `φ`; no thread is stuck; no thread has ended in a panic.
`init_adequate_below` at `T = n + 2`, which bounds every such execution (`RealNstepsBelow.of_one`). -/
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
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  init_adequate_below init body φ hφ σ g Hinitg Hinitw Hlctx Hinit Hthreads (n + 2) n κs t2 σ2
    (RealNstepsBelow.of_one Hsteps Hthreads) Hprog

end adequacy

end EtcdGrove
end Perennial
