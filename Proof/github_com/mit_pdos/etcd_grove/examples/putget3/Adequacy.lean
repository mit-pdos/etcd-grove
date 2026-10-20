/- Lean-first (no Rocq counterpart).

# putget3's closed theorem (D21 stage M5, 2026-10-19)

putget's closed theorem (`putget/Adequacy.lean`) for `examples/putget3`: the package's
initialization followed by `Main()` -- three etcd members started in process, each serving its raft
handler on its own peer listener, a client connected to the first, a `Put` of `k` with `v`, a `Get`
of `k`, and a panic unless the `Get` returned `v` -- started from a fresh state (no package
initialized, one thread): for every real execution of `n` steps, the main thread's result, if it
has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

It follows from `EtcdGrove.goose_adequacy_start` with the read package's two metric names and the
four addresses (the three peer addresses and the first member's client address), over the
ghost-state bundle `putget3GF` (putget's), from `putget3`'s `wp_initialize'` (over the program's
package table `PkgTable.lean`) and `putget3_Main` (`Results.lean`).

**Its hypotheses** (D19a; putget's, `notes/decisions.md`, D19r and "D21 M5"):
* pure facts of the program and its environment: `BootFacts id₁ id₂ id₃ bootLog` (the member ids
  and the bootstrap log Go computes, the ids' 16 low bits distinct and not `0`), `ckptEffectsOk`,
  `authRecordsFit`, `apply.backendUnderQuota`,
  `namesUnclaimed`/`addrsUnclaimed` (D19d), and the execution's length (`n + 2 ≤ 2 ^ 31`;
  `n + 7 ≤ backend.wbInit`);
* the semantics, as putget's;
* triples of functions the program calls, with fresh resources (`putget3.premises`: `bootstrap`'s
  contract for each member, the raft wrapper's names-only contracts, `Stop` of a started node,
  `runsNoRequireLeader`), at every ghost-state instance;
* **the two marked hypotheses**, false under the current Perennial pin: `EofFromIoInit` and
  `ClosedchanFromContextInit`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Perennial.GooseLang.Ffi.DiskFfi.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-! ## The ghost-state bundle -/

/-- The functors (as the register's `registerGF`): the universal camera (`AllG`) at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state, and the disk FFI's
heap. Every other slot is the unit functor. -/
def putget3GF : BundledGFunctors := fun i =>
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

/-- The universal camera at slot 0. -/
def putget3GF_allG : AllG putget3GF := ⟨⟨0, rfl⟩⟩

instance putget3GF_gooseGpreS : GooseGpreS disk_model putget3GF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGFfi := (⟨⟨⟨⟨8, rfl⟩⟩, ⟨⟨9, rfl⟩⟩, ⟨10, rfl⟩⟩⟩ : DiskPreG putget3GF)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := putget3GF_allG

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAt3 (hG : HeapGS .hasLC putget3GF) (lctx : GoLocalContext) : HeapGS .hasLC putget3GF :=
  ⟨hG.goose_globalGS, ⟨hG.goose_localGS.gooseFfiLocalGS, lctx,
    hG.goose_localGS.goose_na_heapGS, hG.goose_localGS.goose_go_stateGS⟩⟩

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `putget3`'s initialization, then `Main()`. -/
def putget3Program [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.putget3.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.putget3.Main) #()

/-- The program's addresses: the three members' peer addresses and the first's client address. -/
def putget3Addrs : List GoString :=
  [putget3.peerAddr₁, putget3.peerAddr₂, putget3.peerAddr₃, putget3.clientAddr₁]

/-- The read package's two metric names, which `putget3`'s initialization registers (`readRegPerm`,
D16). -/
def putget3Names : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- **putget3 is safe** (see the file header): every real execution of
`putget3Program` from a fresh state with one thread, of `n` steps: if the main thread has finished,
its result is `#()` (`Main` returned: the `Get` that returned `nil` returned the `Put`'s value); no
thread is stuck; no thread has ended in a panic. -/
theorem putget3_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putget3GF, ContextReadErrs (GF := putget3GF) (hG := heapAt3 hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : putget3.BootFacts id₁ id₂ id₃ bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota)
    (HNs : prometheus.namesUnclaimed putget3Program putget3Names)
    (HAs : addrsUnclaimed putget3Program putget3Addrs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putget3GF,
      ⊢ putget3.premises (GF := putget3GF) (hG := heapAt3 hG lctx) n id₁ id₂ id₃ bootLog)
    (HEof : ∀ hG : HeapGS .hasLC putget3GF, putget3.EofFromIoInit (GF := putget3GF) (hG := heapAt3 hG lctx))
    (HCc : ∀ hG : HeapGS .hasLC putget3GF,
      putget3.ClosedchanFromContextInit (GF := putget3GF) (hG := heapAt3 hG lctx))
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putget3Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
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
  refine goose_adequacy_start (GF := putget3GF) (n + 1) (n + 2) putget3Program σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial
    putget3Names putget3Addrs (by decide) (by decide) HNs HAs ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  have Hprem0 := Hprem hG
  have HEof0 := HEof hG
  have HCc0 := HCc hG
  have Hctx0 := Hctx hG
  obtain ⟨G, ⟨fl, lc, nh, gs⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC putget3GF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs⟩⟩
  haveI := Hctx0
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok Hrights
  ihave Hown : ownInitializing
      (github_com.mit_pdos.etcd_grove.examples.putget3.getIsPkgInit (GF := putget3GF)) $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  iunfold startRights at Hrights
  simp only [putget3Names, putget3Addrs, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  icases Hrights with ⟨⟨Hn1, Hn2, -⟩, ⟨Ha₁, Ha₂, Ha₃, Hac, -⟩⟩
  ihave #Hprem' := Hprem0
  imodintro
  unfold putget3Program
  wp_apply (github_com.mit_pdos.etcd_grove.examples.putget3.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.putget3.getIsPkgInit_wf) $$ [Hown Hn1 Hn2]
    as ⟨_, #Hinit⟩
  · iframe Hown
    iunfold read.readRegPerm
    iframe
  have hM := putget3.wp_Main (GF := putget3GF) n id₁ id₂ id₃ bootLog Hbf HEof0 HCc0 (by rw [HT]; omega)
    (by rw [HN]; omega) (by rw [HN]; omega) Hck Haf Hbuq Hms hAs
  wp_apply hM $$ [Ha₁ Ha₂ Ha₃ Hac Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
