/-
The end-to-end result of `examples/net/shutdown`: the crash safety of the one-node system over
TCP (`GooseLang/Ext/Tcp`).

The node is the example's command `cmd/node` (`examples/net/shutdown/cmd/node/main.go`, whose
`main` calls `Run`), a process of its own, as the package's process test runs it over real TCP. It
runs the command's program `boot_node` (initialize the command's package, which initializes its
imports, then call its `main`), at the start and after every crash (a process that exits or is
killed and restarted: the semantics covers what the network then sees, `Impl.lean` D10/D11). The
theorem assumes the deployment of `Impl.lean` D13 (a closed world: the network holds only the
system's processes; addresses that do not alias; non-ephemeral ports; the target configuration).
The plan has the node's address `Addr` at a host `h`, which is the node's (it both listens at
`Addr` and dials it). The network starts with no connection.

The precondition of the boot program, over the local ghost state `L` of a generation of the node
(`nodePre`), is the protocol's invariants (`shutInvs`: the address's, every dialer's deposit the
acceptor's fresh end, and `downInv`, the acceptors' directions), the plan's entry for `Addr`, a
fresh package state (of the command's program, whose package table is
`cmd.node.getIsPkgInit`) and the node's host. The global setup allocates `downInv` (no connection
registered) and the address's invariant from the network's start resources (`Addr`'s pending set,
empty); the listener's and the dialer's end's invariants are allocated inside `Run`, after its
`Listen` and `Dial`. The first generation gets its host from its start resources; a crash keeps
the host (`tcp_crashStart`), and the rest is persistent, so every generation's proof guarantees
the next one's precondition.

The conclusion, `shutdown_crash_safety`, mentions no ghost state and no bounds: in every
execution of the system with crashes, no thread of the node is stuck and none has an unrecovered
panic, so the checks after the closes never fail: once a connection or a listener has been closed,
a `Write`, a `Read`, a second `Close` of the connection and an `Accept` on the listener fail,
whatever the reader goroutine and the accept loop blocked on them do, however the connection
fails and however often the node crashes.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node.PkgTable
public import NetTcp.Proof.net.Conn__Read
public import NetTcp.Proof.net.Conn__Write
public import NetTcp.Proof.net.Conn__Close
public import NetTcp.Proof.net.Dial
public import NetTcp.Proof.net.Listen
public import NetTcp.Proof.net.Listener__Accept
public import NetTcp.Proof.net.Listener__Close
public import GooseLang.Ext.Tcp.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

/- The global setup of `goose_dist_crash_adequacy` is under the global ghost state alone, whose
invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The program of the node's command `cmd/node`: initialize the command's package (and so its
imports), then call its `main` (as goose calls a function: resolve it, then apply it). -/
def boot_node [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.node.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.node.main []))) (Val #())) (Val #()))

/-- The system: the one node, running its command's program, from the local state `σ`. -/
def system [GoGlobalContext] (σ : state) : List (Expr × state) :=
  [(boot_node, σ)]

/-- A node's initial local state: its Go context is `lctx`, no package is initialized and it has
its main thread only. -/
structure NodeStart [GoGlobalContext] (lctx : GoLocalContext) (σ : state) : Prop where
  goLctx : σ.goState.goLctx = lctx
  packageState : σ.goState.packageState = ∅
  threads : σ.threads = 1

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The command's program, from a spec of its `main` with precondition `P` (and the command's
package initialized), over the command's package table. -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics] [package_sem : cmd.node.Assumptions]
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
            pkg_id.github_com.mit_pdos.etcd_grove.examples.net.shutdown.cmd.node ∗ P }}
        (App (Val (@! cmd.node.main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP boot_node @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot_node
  wp_apply (cmd.node.wp_initialize' _ cmd.node.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
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
the address's invariant, the plan's entry for `Addr` (at `h`), a fresh package state, and that the
node's host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (h : GoString) (L : GooseLocalGS GF) : IProp GF :=
  iprop((∃ γm, shutInvs (Gg := G) γm) ∗ tcpPlan (extGlobalGS tcpExt) addr h ∗
    ownGoState (hG := L.goose_go_stateGS) ∅ ∗ ⌜(extLocalGS tcpExt (L := L)).host = h⌝)

/-- `shutdown_crash_safety` for executions of fewer than `N` steps along which the node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. -/
theorem shutdown_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : cmd.node.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
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
    -- the acceptors' directions (none yet), then the address's invariant
    letI := (extGlobalGS tcpExt (G := G)).allG
    imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γm, Hm⟩
    imod inv_alloc downN ⊤ (downInv (extGlobalGS tcpExt) γm) $$ [Hm] with #HdownInv
    · inext
      unfold downInv
      iexists ∅
      iframe Hm
      iapply BigSepM.bigSepM_empty.2
      iempintro
    imod wire.addrInv_alloc addrN addr (connProto (Gg := G) γm) $$ Hpend with #HaddrInv
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
      unfold nodePre shutInvs
      iframe Hgs Hp
      isplitl []
      · iexists γm
        iframe HaddrInv HdownInv
      ipureintro; exact Hh.trans Hhost
    iempintro
  · -- every generation of the node: its boot program, and its next precondition
    intro hG _ _ i e σ Hes Hlctx
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    have Hnode : i = 0 ∧ e = boot_node ∧ σ = σ0 := by
      match i, Hes with
      | 0, Hes => cases Hes; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := Hnode
    rw [H0.goLctx] at Hlctx
    subst Hlctx
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold nodePre
    iintro ⟨⟨%γm, #Hinvs⟩, #Hplan, Hgs, %Hh⟩ _
    imodintro
    isplitl [Hgs]
    · iapply wp_boot _ (cmd.node.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
        net.Listener.Close.wp_proof net.Dial.wp_proof net.Conn.Read.wp_proof
        net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
      rw [Hh]
      iframe Hinvs Hplan
    · -- after a crash: the host is kept, the rest is persistent
      iintro %L' _ Hcs Hgs'
      icases tcp_crashStart _ L' $$ Hcs with %Hhost'
      imodintro
      iframe Hgs' Hplan
      isplitl []
      · iexists γm
        iexact Hinvs
      ipureintro
      rw [Hhost']
      exact Hh
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    subst hn
    exact H0.threads

/-- Crash safety of the shutdown system, whose one node is the example's command `cmd/node`, a
process of its own running the command's program (`boot_node`), deployed as `Impl.lean` D13
assumes: in every execution with crashes of the node (`DistCrashNsteps`, the real semantics: a
crash restarts the node with its program, from a crashed local state, the network's connections
and the bytes in flight on them kept), from a local state whose Go context satisfies the Go
semantics and the command's assumptions, with no package
initialized and its main thread only, where the node's host is `h`, the plan has `Addr` at `h` and
the network has no connection yet, the program returns `#()` if it returns, no thread of the
node is stuck and none has an unrecovered panic: the operations after each `Close` fail, so none of
the checks panics, however the connection fails and however often the node crashes.
(`shutdown_crash_safety_bounded` with the ghost state `tcpGF`, the step bound `n + 1` and the
thread bound `n + 2`, which an execution of `n` steps from a single thread respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem shutdown_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : cmd.node.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
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
  shutdown_crash_safety_bounded (GF := tcpGF) (n + 1) (n + 2) σ0 g h H0 Hhost Hplan
    Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact H0.threads))

end adequacy

#print axioms shutdown_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.shutdown

end Perennial
