/- Lean-first (no Rocq counterpart).

# Adequacy of the store's linearizability test (2026-10-19)

A closed theorem about the operational semantics of `Main()` (`examples/kvwitness/check.go`), with no
Iris in its statement: the program `initialize'(); Main()` -- the store package's
initialization (which initializes its dependencies, raft, lintest, porcupine and `context`
among them, then the package) followed by `Main` -- started from a fresh state (no package
initialized, one thread), for every real execution of fewer than `2^63` steps, never gets
stuck, no thread of it ends in a panic, and the main thread's result, if it has one, is `#()`.

`Main` starts the 3-node raft cluster (`StartCluster`), runs the randomized linearizability test
`Check(kvs, lintest.CounterClock(), 4, 25)` -- random `Put`/`Get`/`Append` traffic from 4
clients, traced with a counter clock, the trace checked by porcupine's translated checker
against the store's model -- and panics unless the answer is `Ok`. So no panic means porcupine
never rejects the store's trace.

It follows from Perennial's `goose_adequacy`, as the register's and the counter's
(`lintest/counter/Adequacy.lean`): the disk FFI (the proofs are generic over the FFI), a
concrete ghost-state bundle `kvGF`, the bounds `N = n + 1` (time receipts) and `T = n + 2`
(threads, `Proof/runtime/Threads.lean`), the package initialization (`Init.lean`; `context`'s
`isClosedchanInit`, which `Main.spec` takes, from `context`'s `isPkgInit`,
`context.isClosedchanInit_of_init`) and `Main`'s spec. This file proves it from `Main.spec`
as a hypothesis (`kv_adequate_of`); `AdequacyLinked.lean` applies it to the linked result
`kvwitness.wp_Main` (`Link.lean`): `kv_adequate`.

The same for `MainWitness()` (2026-10-21, W4: the cluster of two voters and a witness,
`StartClusterWitness([]uint64{1, 2}, 3)`, then the same test): `kv_witness_adequate_of`, from
`MainWitness.spec`, and `kv_witness_adequate` (`AdequacyLinked.lean`).

- **The length bound.** `Main.spec` takes `receiptBound GF ≤ 2^63` (the counter clock does not
  wrap; raft's terms stay below `2^64`), and `goose_adequacy`'s receipt bound `N` must exceed
  the execution's length `n`: `N = n + 1 ≤ 2^63`, so the theorem is about executions of
  `n < 2^63` steps.
- **Non-atomic invariants.** Porcupine's results take `[NaInvG GF]` (iris-lean's camera of
  non-atomic invariants, not in Perennial's `allG`); `kvGF` has a slot for it (11), so the
  instance is concrete and the theorem assumes none.
- **The Go semantics** is a parameter, as in every Perennial result: `GoGlobalContext`,
  `GoLocalContext`, `go.Semantics`, the package assumptions `kvwitness.Assumptions` (every name's
  translated body or Perennial's trusted model, the struct layouts, recursively for the
  imports), and raft's initialization premises: `context`'s two method-set facts
  (`ErrorStringIsError`, `DeadlineExceededIsError`) and the model of `log.New` (`log.NewModel`).
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Init
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Main
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.MainWitness
public import Proof.runtime.Threads
public import Perennial.GooseLang.Ffi.DiskFfi.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The ghost-state bundle -/

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state, and the disk FFI's heap (the register's), and
iris-lean's non-atomic invariants at slot 11 (the counter's). Every other slot is the unit
functor. -/
def kvGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 8 => ⟨constOF (HeapView Int (Agree (DiscreteO Block)) (GMap Int)), inferInstance⟩
  | 9 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) (GMap Int)), inferInstance⟩
  | 10 => ⟨constOF MetaUR, inferInstance⟩
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0 (not an instance: under a `HeapGS` the `AllG` is the one
it carries, `GooseGlobalGS.gooseAllG`). -/
@[instance_reducible] def kvGF_allG : AllG kvGF := ⟨⟨0, rfl⟩⟩

instance kvGF_gooseGpreS : GooseGpreS disk_model kvGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGFfi := (⟨⟨⟨⟨8, rfl⟩⟩, ⟨⟨9, rfl⟩⟩, ⟨10, rfl⟩⟩⟩ : DiskPreG kvGF)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := kvGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance the porcupine
results take. -/
instance kvGF_naInvG : NaInvG kvGF := ⟨⟨11, rfl⟩⟩

/-! ## Package initialization's starting point -/

section pkgs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- The post-initialization predicate of every package the store (transitively) imports, and
of the store itself: what `ownInitializing` hands out for an initialized package. -/
def pkgInitTable : List (GoString × IProp GF) :=
  [(pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness,
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness),
   (pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest,
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest),
   (pkg_id.github_com.anishathalye.porcupine,
      isPkgInit pkg_id.github_com.anishathalye.porcupine),
   (pkg_id.context, isPkgInit pkg_id.context),
   (pkg_id.github_com.goose_lang.primitive, isPkgInit pkg_id.github_com.goose_lang.primitive),
   (pkg_id.sort, isPkgInit pkg_id.sort),
   (pkg_id.sync, isPkgInit pkg_id.sync),
   (pkg_id.internal.synctest, isPkgInit pkg_id.internal.synctest),
   (pkg_id.internal.race, isPkgInit pkg_id.internal.race),
   (pkg_id.sync.atomic, isPkgInit pkg_id.sync.atomic),
   (pkg_id.encoding.binary, isPkgInit pkg_id.encoding.binary),
   (pkg_id.slices, isPkgInit pkg_id.slices),
   (pkg_id.math.bits, isPkgInit pkg_id.math.bits),
   (pkg_id.«unsafe», isPkgInit pkg_id.«unsafe»),
   (pkg_id.cmp, isPkgInit pkg_id.cmp),
   (pkg_id.math, isPkgInit pkg_id.math),
   (pkg_id.io, isPkgInit pkg_id.io),
   (pkg_id.errors, isPkgInit pkg_id.errors),
   (pkg_id.go_etcd_io.raft.v3.raftpb, isPkgInit pkg_id.go_etcd_io.raft.v3.raftpb),
   (pkg_id.google_golang_org.protobuf.proto, isPkgInit pkg_id.google_golang_org.protobuf.proto),
   (pkg_id.google_golang_org.protobuf.reflect.protoreflect,
      isPkgInit pkg_id.google_golang_org.protobuf.reflect.protoreflect),
   (pkg_id.google_golang_org.protobuf.runtime.protoimpl,
      isPkgInit pkg_id.google_golang_org.protobuf.runtime.protoimpl),
   (pkg_id.google_golang_org.protobuf.internal.impl,
      isPkgInit pkg_id.google_golang_org.protobuf.internal.impl),
   (pkg_id.google_golang_org.protobuf.internal.pragma,
      isPkgInit pkg_id.google_golang_org.protobuf.internal.pragma),
   (pkg_id.fmt, isPkgInit pkg_id.fmt),
   (pkg_id.go_etcd_io.raft.v3, isPkgInit pkg_id.go_etcd_io.raft.v3),
   (pkg_id.go_etcd_io.raft.v3.tracker, isPkgInit pkg_id.go_etcd_io.raft.v3.tracker),
   (pkg_id.go_etcd_io.raft.v3.quorum, isPkgInit pkg_id.go_etcd_io.raft.v3.quorum),
   (pkg_id.strconv, isPkgInit pkg_id.strconv),
   (pkg_id.strings, isPkgInit pkg_id.strings),
   (pkg_id.go_etcd_io.raft.v3.confchange, isPkgInit pkg_id.go_etcd_io.raft.v3.confchange),
   (pkg_id.math.big, isPkgInit pkg_id.math.big),
   (pkg_id.crypto.rand, isPkgInit pkg_id.crypto.rand),
   (pkg_id.bytes, isPkgInit pkg_id.bytes),
   (pkg_id.time, isPkgInit pkg_id.time),
   (pkg_id.os, isPkgInit pkg_id.os),
   (pkg_id.log, isPkgInit pkg_id.log)]

/-- `get_is_pkg_init` for the store's program: a package's entry in `pkgInitTable`. -/
def getIsPkgInit (s : GoString) : IProp GF :=
  ((pkgInitTable (GF := GF)).lookup s).getD iprop(True)

theorem getIsPkgInit_kv :
    GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness (getIsPkgInit (GF := GF)) := by
  repeat' (first | exact True.intro | apply And.intro | rfl)

end pkgs

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s spec at `kvGF`, for every `HeapGS` (hence every local context), every semantics
and every package assumptions: what `Main.wp_proof` gives, the hypothesis of
`kv_adequate_of`. -/
abbrev kvMainSpec : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC kvGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions],
    kvwitness.Main.spec (GF := kvGF) (hG := hG)

/-- The store's program: the package's initialization, then `Main()`. -/
def kvProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.kvwitness.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.Main) #()

/-- **Porcupine never rejects the store's trace**, from `Main`'s spec (`wp_Main`, at every
`HeapGS` of `kvGF` and every semantics): every real execution of `kvProgram` (the store package's initialization,
then `Main()`) from a fresh state -- no package initialized (`IsInit`), one live thread -- of
`n < 2^63` steps: if the main thread has finished, its result is `#()`; no thread is stuck
(each is a value or can step); no thread has ended in a panic. `Main` panics unless porcupine
answers `Ok` on the trace of the randomized test against the 3-node cluster (see the file
header), so porcupine answered `Ok` in every interleaving and every choice of the scheduler.

Parametric in the Go semantics: any `go.Semantics` at the state's local context, any package
assumptions (the translated bodies behind the store's and its imports' names), `context`'s
method-set facts and the model of `log.New`. No instance is assumed for the ghost state: the
bundle `kvGF` provides iris-lean's non-atomic invariants (`NaInvG`). -/
theorem kv_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError]
    [hLog : log.NewModel]
    (wp_Main : kvMainSpec)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  suffices H : (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) by
    refine ⟨H.1, H.2.1, fun v hv => ?_⟩
    cases h : v.isPanic
    · rfl
    · obtain ⟨p, rfl⟩ := val.isPanic_eq_true h
      exact absurd (UnrecoveredPanic.panic p) (H.2.2 _ hv)
  refine goose_adequacy (GF := kvGF) (n + 1) (n + 2) kvProgram σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN _ HL
  obtain ⟨G, ⟨fl, lc, nh, gs⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC kvGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs⟩⟩
  have Hbound : receiptBound kvGF ≤ 2 ^ 63 := by rw [HN]; omega
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok
  ihave Hown : ownInitializing (getIsPkgInit (GF := kvGF)) $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  unfold kvProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.kvwitness.wp_initialize' _
    getIsPkgInit_kv) $$ Hown as ⟨_, #Hpkg⟩
  ihave #Hcc : context.isClosedchanInit (GF := kvGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (wp_Main Hbound) $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

/-- `MainWitness`'s spec at `kvGF`, the hypothesis of `kv_witness_adequate_of`. -/
abbrev kvMainWitnessSpec : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC kvGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions],
    kvwitness.MainWitness.spec (GF := kvGF) (hG := hG)

/-- The store's program with a witness: the package's initialization, then `MainWitness()`. -/
def kvProgramWitness [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.kvwitness.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.MainWitness) #()

/-- **Porcupine never rejects the trace of the store with a witness**, from `MainWitness`'s
spec: `kv_adequate_of` for `kvProgramWitness` (the store package's initialization, then
`MainWitness()`: the cluster of the voters `1`, `2` and the witness `3` in raft's static mode,
the same randomized test, and a panic unless porcupine answers `Ok`). -/
theorem kv_witness_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError]
    [hLog : log.NewModel]
    (wp_MainWitness : kvMainWitnessSpec)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvProgramWitness], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  suffices H : (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) by
    refine ⟨H.1, H.2.1, fun v hv => ?_⟩
    cases h : v.isPanic
    · rfl
    · obtain ⟨p, rfl⟩ := val.isPanic_eq_true h
      exact absurd (UnrecoveredPanic.panic p) (H.2.2 _ hv)
  refine goose_adequacy (GF := kvGF) (n + 1) (n + 2) kvProgramWitness σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN _ HL
  obtain ⟨G, ⟨fl, lc, nh, gs⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC kvGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs⟩⟩
  have Hbound : receiptBound kvGF ≤ 2 ^ 63 := by rw [HN]; omega
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok
  ihave Hown : ownInitializing (getIsPkgInit (GF := kvGF)) $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  unfold kvProgramWitness
  wp_apply (github_com.mit_pdos.etcd_grove.examples.kvwitness.wp_initialize' _
    getIsPkgInit_kv) $$ Hown as ⟨_, #Hpkg⟩
  ihave #Hcc : context.isClosedchanInit (GF := kvGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (wp_MainWitness Hbound) $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.kv_adequate_of
#print axioms Perennial.EtcdGrove.kv_witness_adequate_of
