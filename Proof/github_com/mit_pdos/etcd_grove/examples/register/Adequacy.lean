/- Lean-first (no Rocq counterpart).

# Adequacy of the register's cluster driver (2026-10-12)

A closed theorem about the operational semantics of `Main()` (`examples/register/cluster.go`):
the program `initialize'(); Main()` -- the register package's initialization (which
initializes its dependencies, raft's among them, then the package itself) followed by
`Main` -- started from a fresh state (no package initialized, one thread), never gets
stuck, no thread of it ends in a panic, and the main thread's result, if it has one, is
`#()`. For every real execution, of any length: the thread bound comes from
`threads_le_steps` (one step forks at most one thread).

It follows from Perennial's `goose_adequacy_nopanic`, instantiated with the disk FFI (the
register's proofs are generic over the FFI; the disk's adequacy instance has trivial
initial-state conditions) and a concrete ghost-state bundle `registerGF`, from
`register_Main` (`Spec/.../register/Main.lean`) and the register package's
`wp_initialize'` (`Init.lean`).

The statement is parametric in the Go semantics, as every Perennial result is: the
`GoGlobalContext`, the language semantics `go.Semantics` at the initial state's local
context and the package assumptions `register.Assumptions` (the translated function bodies
behind each name, the struct layouts, recursively for the imported packages) are instance
arguments.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Init
public import Perennial.GooseLang.Ffi.DiskFfi.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The thread count grows by at most one per step -/

section threads
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

/-- A real thread-pool step adds at most one live thread. -/
theorem realStep_threads_le {ρ₁ ρ₂ : List Expr × CfgState} {κ : List Observation}
    (h : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) :
    ρ₂.2.2.threads ≤ ρ₁.2.2.threads + 1 := by
  obtain ⟨H, t₁, t₂⟩ := h
  rename_i e σ e' σ' eₜ
  obtain ⟨hb⟩ := H
  rename_i e₁ e₂ K
  simp only
  rcases hk : redexKind e₁ with _ | _ | _ | _
  · have := baseStep_threads hb (by simp [hk]) (by simp [hk]); omega
  · obtain ⟨e₀, rfl⟩ := redexKind_eq_fork hk
    rcases hb with ⟨hu⟩ | ⟨_, hb⟩
    · exact absurd hu (not_unwinds_Fork _ _)
    cases hb
    simp
  · have := redexKind_eq_exit hk
    subst this
    rcases hb with ⟨hu⟩ | ⟨_, hb⟩
    · exact absurd hu (not_unwinds_ThreadExit _)
    cases hb
    simp; omega
  · have := baseStep_threads hb (by simp [hk]) (by simp [hk]); omega

/-- After `k` real steps, at most `k` more threads are live. -/
theorem threads_le_steps {k : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps k ρ₁ κs ρ₂) : ρ₂.2.2.threads ≤ ρ₁.2.2.threads + k := by
  unfold RealNsteps at h
  induction h with
  | refl ρ => omega
  | cons hstep _ ih => have := realStep_threads_le hstep; omega

/-- Any execution of `n` steps from one live thread stays below `n + 2` threads. -/
theorem realThreadsBelow_of_one {n : Nat} {ρ : List Expr × CfgState} (h1 : ρ.2.2.threads = 1) :
    RealThreadsBelow (n + 2) n ρ := by
  intro k κs ρ' hk hsteps
  have := threads_le_steps hsteps
  omega

end threads

/-! ## The ghost-state bundle -/

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state, and the disk FFI's heap. Every other slot
is the unit functor. -/
def registerGF : BundledGFunctors := fun i =>
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
  | _ => ⟨constOF Unit, inferInstance⟩

instance registerGF_allG : AllG registerGF := ⟨⟨0, rfl⟩⟩

instance registerGF_gooseGpreS : GooseGpreS disk_model registerGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGFfi := (⟨⟨⟨⟨8, rfl⟩⟩, ⟨⟨9, rfl⟩⟩, ⟨10, rfl⟩⟩⟩ : DiskPreG registerGF)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goose_preG_receipt := ⟨registerGF_allG⟩
  goose_preG_thread := ⟨registerGF_allG⟩

/-! ## Package initialization's starting point -/

section pkgs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

/-- The post-initialization predicate of every package the register (transitively)
imports, and of the register itself: what `ownInitializing` hands out for an initialized
package. -/
def pkgInitTable : List (GoString × IProp GF) :=
  [(pkg_id.github_com.mit_pdos.etcd_grove.examples.register,
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.register),
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
   (pkg_id.reflect, isPkgInit pkg_id.reflect),
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
   (pkg_id.context, isPkgInit pkg_id.context),
   (pkg_id.time, isPkgInit pkg_id.time),
   (pkg_id.os, isPkgInit pkg_id.os),
   (pkg_id.log, isPkgInit pkg_id.log)]

/-- `get_is_pkg_init` for the register's program: a package's entry in `pkgInitTable`. -/
def getIsPkgInit (s : GoString) : IProp GF :=
  ((pkgInitTable (GF := GF)).lookup s).getD iprop(True)

theorem getIsPkgInit_wf :
    GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.register
      (getIsPkgInit (GF := GF)) := by
  repeat' (first | exact True.intro | apply And.intro | rfl)

end pkgs

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The register's program: the package's initialization, then `Main()`. -/
def registerProgram [GoSemanticsFunctions] : Expr :=
  App (Rec BAnon BAnon
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.Main)) (Val #())))
    (App (Val github_com.mit_pdos.etcd_grove.examples.register.initialize') (Val #()))

/-- **The register's cluster driver is safe.** Every real execution of `registerProgram`
(the register package's initialization, then `Main()`) from a fresh state -- no package
initialized (`IsInit`), one live thread -- of any length `n`: if the main thread has
finished, its result is `#()`; no thread is stuck (each is a value or can step); no thread
has ended in a panic (client B's check of its `Get` among them). Parametric in the Go
semantics: any `go.Semantics` at the state's local context and any package assumptions
(the translated bodies behind the register's and its imports' names). -/
theorem register_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
    [hErr : context.ErrorStringIsError] [hLog : log.NewModel]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([registerProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine goose_adequacy_nopanic (GF := registerGF) (n + 1) (n + 2) registerProgram σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG _ _ HL
  obtain ⟨G, ⟨fl, lc, nh, gs⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC registerGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs⟩⟩
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok
  ihave Hown : ownInitializing (getIsPkgInit (GF := registerGF)) $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  unfold registerProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.register.wp_initialize' _
    getIsPkgInit_wf) $$ Hown as ⟨_, #Hinit⟩
  wp_apply register.wp_Main $$ Hinit
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
