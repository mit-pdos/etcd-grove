/-
The end-to-end result of `examples/net/echo`: the distributed crash safety of the three-node
system over TCP (`GooseLang/Ext/Net`).

The nodes are the example's commands, each its own process (`examples/net/echo/cmd/{server,client,
junk}`, which the package's process tests run over real TCP): node `i` runs its command's program,
`boot_server`, `boot_client` or `boot_junk` (initialize the command's package, then call its
`main`), at the start and after every crash of the node, each with its own package table (its
`getIsPkgInit_wf`). A process that exits is a node whose threads have all returned: its peers see
what the semantics says of a dead process's connections (`Impl.lean` D10, D11). The server's
address `SrvAddr` is valid (`addrOk`, D20, checked by `decide`); the nodes may be on any machines
(v3.4: the network has no plan and no hosts). The network starts with no connection.

The precondition of a node's boot program, over the local ghost state `L` of a generation of the
node (`nodePre`), is echo's protocol (`echoInvs`, `Defs.lean`: the address's invariant and every
connection's echo state), the plan's entry for `SrvAddr` (as a resource, which `Dial` takes, and in
the network's plan, which `Listen` resolves against), a fresh package state and, for the server,
its host. The global setup allocates the protocol from the network's start resources (`SrvAddr`'s
pending set, empty, and the ghost state's plan, the network's); each node's first generation gets its precondition from its start
resources (its host); a crash keeps the host (`net_crashStart`), and the rest is persistent, so
every generation's proof guarantees the next one's precondition. Each command's `main` is proved
from echo's bodies (`cmd/<node>/Main.lean`: `wp_main`).

The conclusion, `echo_crash_safety`, mentions no ghost state and no bounds: in every execution of
the system with crashes, no thread of any node is stuck and none has an unrecovered panic, so the
client's check (the reply it read in full is `"hello"`, the bytes it sent) never fails, whatever
the junk sender sends, however the connections fail (with any error kind, D14; a write cut short
by a close, D15) or the nodes crash (a crash does not clear the bytes in flight on a connection: the
network is global state), and whatever connections a failed dial leaves behind (D16: the server may
accept one and reads EOF from it). Like every theorem over the TCP semantics, it assumes the
deployment of `Impl.lean` D13: a closed world (prose), plan addresses that do not alias and ports
outside the ephemeral range (`PlanWellFormed`, D20, a premise), the target configuration.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.client.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.junk.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.cmd.junk.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

/- The global setup of `goose_dist_crash_adequacy` is under the global ghost state alone, whose
invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A node's initial local state: its Go context is `lctx`, no package is initialized and it has
its main thread only. -/
structure NodeStart [GoGlobalContext] (lctx : GoLocalContext) (σ : state) : Prop where
  goLctx : σ.goState.goLctx = lctx
  packageState : σ.goState.packageState = ∅
  threads : σ.threads = 1

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec (with the program's package table
`getIs`, initializing the command's package `pkg`) and a spec of its `main` with precondition
`P`. -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (main pkg : GoString) [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (Hinit : {{ ownInitializing getIs }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg }})
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P }}
        (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot
  wp_apply Hinit $$ [Hgs] as ⟨-, #Hpkg⟩
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

/-- The precondition of node `i`'s boot program in the generation with local ghost state `L`:
echo's protocol, `SrvAddr`'s validity, and a fresh package state. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (i : Nat) (L : GooseLocalGS GF) : IProp GF :=
  iprop((∃ γm, echoInvs (Gg := G) γm) ∗ ⌜addrOk srvAddr = true⌝ ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

set_option linter.unusedVariables false in
/-- `echo_crash_safety` for executions of fewer than `N` steps along which every node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. -/
theorem echo_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [junk_sem : cmd.junk.Assumptions] [go.BasicIntoValInj]
    [hPre : GooseGpreS GF] (N T : Nat) (σs σc σj : state) (g : GlobalState)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc) (Hj : NodeStart lctx σj)
    (Hconns : (extGlobal netExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σs σc σj).map Prod.fst) n
      (distInit (system σs σc σj) g) κs c)
    (Hbound : n < N)
    (Hlive : DistCrashThreadsBelow ((system σs σc σj).map Prod.fst) T n
      (distInit (system σs σc σj) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_crash_adequacy (GF := GF) N T (system σs σc σj) g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩
    (fun _ _ => ⟨trivial, trivial⟩) (fun i L => nodePre i L) ?_ ?_
    n κs c Hsteps Hbound ?_ Hlive
  · -- the global setup and the first generation of every node
    intro G _
    iintro Hg
    icases net_globalStart g.globalWorld $$ Hg with Hnet
    unfold netStart
    have Hpe : PartialMap.get? pendInit srvAddr = some ∅ := by
      rw [gmap_get?_eq]; exact addrSpace_lookup_ok _ (by decide)
    icases Hnet with ⟨Hnet, Htoks⟩
    ihave Hpend := (BigSepM.bigSepM_lookup (Φ := fun a S => netPend (extGlobalGS netExt) a S) Hpe)
      $$ Hnet
    have Hte : PartialMap.get? (addrSpace ()) srvAddr = some () := by
      rw [gmap_get?_eq]; exact addrSpace_lookup_ok _ (by decide)
    ihave Htk := (BigSepM.bigSepM_lookup (Φ := fun a (_ : Unit) => netLisTok (extGlobalGS netExt) a)
      Hte) $$ Htoks
    have HGp : addrOk srvAddr = true := by decide
    -- echo's protocol: the connections' states (none yet), then the address's invariant
    imod echoInvs_alloc (Gg := G) $$ Hpend Htk with ⟨%γm, #Hinvs⟩
    imodintro
    simp only [system]
    unfold nodeStart
    isplitl []
    · -- the server
      iintro %L %_ %_ - Hgs
      rw [Hs.packageState]
      imodintro
      simp only []
      unfold nodePre
      iframe Hgs
      isplitl []
      · iexists γm
        iexact Hinvs
      ipureintro; exact HGp
    isplitl []
    · -- the client
      iintro %L %_ %_ - Hgs
      rw [Hc.packageState]
      imodintro
      simp only []
      unfold nodePre
      iframe Hgs
      isplitl []
      · iexists γm
        iexact Hinvs
      ipureintro; exact HGp
    isplitl []
    · -- the junk sender
      iintro %L %_ %_ - Hgs
      rw [Hj.packageState]
      imodintro
      simp only []
      unfold nodePre
      iframe Hgs
      isplitl []
      · iexists γm
        iexact Hinvs
      ipureintro; exact HGp
    iempintro
  · -- every generation of every node: its boot program, and its next precondition
    intro hG _ _ i e σ Hes Hlctx
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    have Hnode : (i = 0 ∧ e = boot_server ∧ σ = σs) ∨
        (i = 1 ∧ e = boot_client ∧ σ = σc) ∨ (i = 2 ∧ e = boot_junk ∧ σ = σj) := by
      match i, Hes with
      | 0, Hes => cases Hes; exact .inl ⟨rfl, rfl, rfl⟩
      | 1, Hes => cases Hes; exact .inr (.inl ⟨rfl, rfl, rfl⟩)
      | 2, Hes => cases Hes; exact .inr (.inr ⟨rfl, rfl, rfl⟩)
    have Hl : σ.goState.goLctx = lctx := by
      rcases Hnode with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact Hs.goLctx
      · exact Hc.goLctx
      · exact Hj.goLctx
    rw [Hl] at Hlctx
    subst Hlctx
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold nodePre
    iintro ⟨⟨%γm, #Hinvs⟩, #Hplan, Hgs⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · iapply wp_boot cmd.server.initialize' cmd.server.main _ cmd.server.getIsPkgInit
          (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) _
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_boot cmd.client.initialize' cmd.client.main _ cmd.client.getIsPkgInit
          (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf) _
          (cmd.client.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_boot cmd.junk.initialize' cmd.junk.main _ cmd.junk.getIsPkgInit
          (cmd.junk.wp_initialize' _ cmd.junk.getIsPkgInit_wf) _
          (cmd.junk.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
    · -- after a crash: everything is persistent
      iintro %L' _ - Hgs' _
      imodintro
      iframe Hgs' Hplan
      iexists γm
      iexact Hinvs
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact Hs.threads
    · exact Hc.threads
    · exact Hj.threads

set_option linter.unusedVariables false in
/-- Crash safety of the echo system: in every execution with crashes of the three nodes, the
example's commands `cmd/server`, `cmd/client` and `cmd/junk`, each its own process
(`DistCrashNsteps`, the real semantics: a crash of a node restarts it with its boot program, from
a crashed local state, the network's connections and the bytes in flight on them kept), from
local states whose Go contexts satisfy the Go semantics and the commands' assumptions, with no
package initialized and their main threads only, where the network has no connection yet, every boot program returns `#()` if it
returns, no thread of any node is stuck and none has an unrecovered panic: the client's check
holds, however connections fail, whatever the junk sender sends, and however often any node
crashes. (`echo_crash_safety_bounded` with the ghost state `netGF`, the step bound `n + 1` and the
thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) It assumes the deployment of `Impl.lean` D13. -/
theorem echo_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [srv_sem : cmd.server.Assumptions] [cli_sem : cmd.client.Assumptions]
    [junk_sem : cmd.junk.Assumptions] [go.BasicIntoValInj]
    (σs σc σj : state) (g : GlobalState)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc) (Hj : NodeStart lctx σj)
    (Hconns : (extGlobal netExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σs σc σj).map Prod.fst) n
      (distInit (system σs σc σj) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  echo_crash_safety_bounded (GF := netGF) (n + 1) (n + 2) σs σc σj g Hs Hc Hj Hconns n κs c
    Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads
      | 2, hi => cases hi; exact Hj.threads))

end adequacy

/-- The example's address is valid (D20). -/
example : addrOk srvAddr = true := by decide

#print axioms echo_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.echo

end Perennial
