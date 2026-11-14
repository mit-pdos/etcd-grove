/-
The closed form of the counterexample of `notes/axiom-review/tcp-semantics.md`
(`examples/axiomcx/tcp-emptywrite`): the crash safety, under the TCP extension's semantics
(`GooseLang/Ext/Tcp`), of the one-node system that runs `Main` (initialize the package, then call
`Main`) at the start and after every crash, the plan having `Addr` at the node's host `h` and the
network no connection. The deployment is the one the semantics allows: one process on this machine,
which listens at `127.0.0.1:7199` and dials it.

`emptywrite_crash_safety` says that no thread ever has an unrecovered panic, so `Main`'s check
(the empty `Write` succeeded) never fails. On Linux 7.0 with Go 1.27.3, `Main` panics on every run
(`examples/axiomcx/tcp-emptywrite`, `TestMainPanics`): the semantics is refuted. The step that
excludes Go's outcome is `WriteOutcome` (`Main.lean`, `emptyWrite_ok`).

The precondition of the boot program in a generation (`nodePre`): `Addr`'s invariant (no
deposit), the plan's entry, a fresh package state and the node's host; the invariant is allocated
in the global setup from `Addr`'s pending set (empty), the host comes from the start resources and
is kept by a crash (`tcp_crashStart`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite.PkgTable
public import NetTcp.Proof.net.Conn__Write
public import NetTcp.Proof.net.Conn__SetDeadline
public import NetTcp.Proof.net.Conn__Close
public import NetTcp.Proof.net.Dial
public import NetTcp.Proof.net.Listen
public import NetTcp.Proof.net.Listener__Close
public import Perennial.Proof.time.Link
public import GooseLang.Ext.Tcp.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

/- The global setup of `goose_dist_crash_adequacy` is under the global ghost state alone, whose
invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The boot program of a node: initialize the package, then call the package's function `f` (as
goose calls a function: resolve it, then apply it). -/
def boot [GoGlobalContext] (f : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve f []))) (Val #())) (Val #()))

/-- The system: the one node, from the local state `σ`. -/
def system [GoGlobalContext] (σ : state) : List (Expr × state) :=
  [(boot Main, σ)]

/-- A node's initial local state: its Go context is `lctx`, no package is initialized and it has
its main thread only. -/
structure NodeStart [GoGlobalContext] (lctx : GoLocalContext) (σ : state) : Prop where
  goLctx : σ.goState.goLctx = lctx
  packageState : σ.goState.packageState = ∅
  threads : σ.threads = 1

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A boot program, from a spec of its function `f` with precondition `P` (and the package
initialized). -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics] [package_sem : Assumptions]
    (f : GoString) (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
            pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite ∗ P }}
        (App (Val (@! f)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot f) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot
  wp_apply (wp_initialize' _ getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
  · -- no package is initialized
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

/-- The precondition of the node's boot program in the generation with local ghost state `L`:
`Addr`'s invariant, the plan's entry for `Addr` (at `h`), a fresh package state, and that the
node's host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (h : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop(inv addrN (addrInv (Gg := G) addr (fun _ => iprop(True))) ∗
    tcpPlan (extGlobalGS tcpExt) addr h ∗
    ownGoState (hG := L.goose_go_stateGS) ∅ ∗ ⌜(extLocalGS tcpExt (L := L)).host = h⌝)

/-- `emptywrite_crash_safety` for executions of fewer than `N` steps along which the node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. -/
theorem emptywrite_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    [hPre : GooseGpreS GF] (N T : Nat) (σ0 : state) (g : GlobalState) (h : GoString)
    (H0 : NodeStart lctx σ0)
    (Hhost : (extLocal tcpExt σ0.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup addr = some h)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σ0).map Prod.fst) n (distInit (system σ0) g) κs c)
    (Hbound : n < N)
    (Hlive : DistCrashThreadsBelow ((system σ0).map Prod.fst) T n (distInit (system σ0) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_crash_adequacy (GF := GF) N T (system σ0) g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ L => nodePre h L) ?_ ?_
    n κs c Hsteps Hbound ?_ Hlive
  · -- the global setup and the node's first generation
    intro G _
    iintro Hg
    icases tcp_globalStart g.globalWorld $$ Hg with Hnet
    unfold tcpStart
    icases Hnet with ⟨Hplans, Hpends⟩
    have Hpl : PartialMap.get? (extGlobal tcpExt g.globalWorld).plan addr = some h := by
      rw [gmap_get?_eq]; exact Hplan
    ihave #Hp := (BigSepM.bigSepM_lookup (Φ := fun a h => tcpPlan (extGlobalGS tcpExt) a h) Hpl)
      $$ Hplans
    have Hpe : PartialMap.get? (pendInit (extGlobal tcpExt g.globalWorld)) addr = some ∅ := by
      rw [gmap_get?_eq]; simp [pendInit, GMap.lookup_fmap, Hplan]
    ihave Hpend := (BigSepM.bigSepM_lookup (Φ := fun a S => tcpPend (extGlobalGS tcpExt) a S) Hpe)
      $$ Hpends
    -- the address's invariant
    imod github_com.mit_pdos.etcd_grove.examples.net.wire.addrInv_alloc addrN addr (fun _ => iprop(True)) $$ Hpend with #HaddrInv
    imodintro
    simp only [system]
    unfold nodeStart
    isplitl []
    · -- the node: its host is `h`
      iintro %L %_ %_ Hstart Hgs
      ihave Hl := tcp_localStart (L := L) σ0.world $$ Hstart
      iunfold lisStart at Hl
      icases Hl with ⟨%Hh, -⟩
      rw [H0.packageState]
      imodintro
      simp only []
      unfold nodePre
      iframe Hgs Hp HaddrInv
      ipureintro; exact Hh.trans Hhost
    iempintro
  · -- every generation of the node: its boot program, and its next precondition
    intro hG _ _ i e σ Hes Hlctx
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    have Hnode : i = 0 ∧ e = boot Main ∧ σ = σ0 := by
      match i, Hes with
      | 0, Hes => cases Hes; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := Hnode
    rw [H0.goLctx] at Hlctx
    subst Hlctx
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold nodePre
    iintro ⟨#Hinv, #Hplan, Hgs, %Hh⟩ _
    imodintro
    isplitl [Hgs]
    · iapply wp_boot Main _ (wp_Main net.Listen.wp_proof net.Listener.Close.wp_proof
        net.Dial.wp_proof net.Conn.SetDeadline.wp_proof net.Conn.Write.wp_proof
        net.Conn.Close.wp_proof time.Now.wp_proof) $$ [] Hgs
      rw [Hh]
      iframe Hinv Hplan
    · -- after a crash: the host is kept, the rest is persistent
      iintro %L' _ Hcs Hgs'
      icases tcp_crashStart _ L' $$ Hcs with %Hhost'
      imodintro
      iframe Hgs' Hplan Hinv
      ipureintro
      rw [Hhost']
      exact Hh
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    subst hn
    exact H0.threads

/-- Crash safety of the one-node system running `Main`, under the TCP extension's semantics: in
every execution with crashes (`DistCrashNsteps`), from a local state whose Go context satisfies the
Go semantics and the package's assumptions, with no package initialized and its main thread only,
where the node's host is `h`, the plan has `Addr` at `h` and the network has no connection yet,
the boot program returns `#()` if it returns, no thread is stuck and none has an unrecovered panic.
False of Go on Linux: `Main` panics on every run. (`emptywrite_crash_safety_bounded` with the ghost
state `tcpGF`, the step bound `n + 1` and the thread bound `n + 2`.) -/
theorem emptywrite_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σ0 : state) (g : GlobalState) (h : GoString)
    (H0 : NodeStart lctx σ0)
    (Hhost : (extLocal tcpExt σ0.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup addr = some h)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σ0).map Prod.fst) n (distInit (system σ0) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  emptywrite_crash_safety_bounded (GF := tcpGF) (n + 1) (n + 2) σ0 g h H0 Hhost Hplan
    Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact H0.threads))

end adequacy

#print axioms emptywrite_crash_safety

end github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite

end Perennial
