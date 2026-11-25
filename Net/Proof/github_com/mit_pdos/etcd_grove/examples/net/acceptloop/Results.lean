/-
The end-to-end result of `examples/net/acceptloop`: the distributed crash safety of the two-node
system over TCP (`GooseLang/Ext/Net`), with goroutines on both nodes.

The nodes are the example's commands (`examples/net/acceptloop/cmd/{server,client}`), each its own
process, as the package's process tests run them over real TCP: node `i` runs its command's
program, `boot_server` or `boot_client` (initialize the command's package, then call its `main`),
at the start and after every crash of the node, each with its own package table
(`cmd.<node>.getIsPkgInit_wf`). A process that exits is, for its peers, a node whose connections
break (`Impl.lean`, D10/D11). The plan has the server's address `SrvAddr` at a host `h`, which is
the server node's; the client may be on any host (the server's too). The network starts with no
connection. The deployment is the one every theorem over the TCP semantics assumes (`Impl.lean`,
D13: a closed world, addresses that do not alias, a port outside the ephemeral range, the target
configuration); the plan is given as a list `pl` that is well formed (D20, `PlanWellFormed`,
checked by `decide`: the `example` after the theorems for the plan of `SrvAddr` alone).

The precondition of a node's boot program, over the local ghost state `L` of a generation of the
node (`nodePre`), is the protocol (`echoInvs`, `Defs.lean`: the address's invariant and every
connection's echo state), the plan's entry for `SrvAddr`, a fresh package state and, for the
server, its host. The global setup allocates the protocol from the network's start resources
(`SrvAddr`'s pending set, empty); each node's first generation gets its precondition from its start
resources (its host); a crash keeps the host (`net_crashStart`), and the rest is persistent, so
every generation's proof guarantees the next one's precondition.

The conclusion, `acceptloop_crash_safety`, mentions no ghost state and no bounds: in every
execution of the system with crashes, no thread of any node is stuck and none has an unrecovered
panic. The threads include the server's per-connection handlers and the client's 1 to 8 calls, so
each call's check (the 1-byte reply it read is its own id) never fails, however the goroutines of
both nodes interleave, however the connections fail or the nodes crash (a crash does not clear
the bytes in flight on a connection: the network is global state).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.RandomLinked
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Perennial.Proof.sync.Link
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

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

/-- No package is initialized: the start of `ownInitializing`. -/
theorem ownInitializing_start [hG : HeapGS .hasLC GF]
    (get_is_pkg_init : GoString → IProp GF) :
    ⊢ ownGoState ∅ -∗ ownInitializing get_is_pkg_init := by
  iintro Hgs
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  iexists ∅
  iframe Hgs
  iintro !>
  iapply BigSepM.bigSepM_empty.2
  iempintro

/-- The server node's program, from a spec of its command's `main` with precondition `P` (and the
command's package initialized). -/
theorem wp_boot_server [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    [package_sem : cmd.server.Assumptions] (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
            pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.server ∗ P }}
        (App (Val (@! cmd.server.main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP boot_server @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot_server
  wp_apply (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
  · iapply ownInitializing_start $$ Hgs
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

/-- The client node's program, from a spec of its command's `main`. -/
theorem wp_boot_client [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    [package_sem : cmd.client.Assumptions] (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
            pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.cmd.client ∗ P }}
        (App (Val (@! cmd.client.main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP boot_client @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot_client
  wp_apply (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
  · iapply ownInitializing_start $$ Hgs
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

/-- The precondition of node `i`'s boot program in the generation with local ghost state `L`:
the protocol, the plan's entry for `SrvAddr` (at `h`), a fresh package state, and for the server
(`i = 0`), that a `Listen` of `SrvAddr` on its host listens at it (`ListenAt`: its host is the
plan's `h`). -/
def nodePre [G : GooseGlobalGS .hasLC GF] (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop((∃ γm, echoInvs (Gg := G) γm) ∗ ⌜addrOk srvAddr = true⌝ ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

set_option linter.unusedVariables false in
/-- `acceptloop_crash_safety` for executions of fewer than `N` steps along which every node has
fewer than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. -/
theorem acceptloop_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] [client_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    [hPre : GooseGpreS GF] (N T : Nat) (σs σc : state) (g : GlobalState)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc)
    (Hconns : (extGlobal netExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σs σc).map Prod.fst) n
      (distInit (system σs σc) g) κs c)
    (Hbound : n < N)
    (Hlive : DistCrashThreadsBelow ((system σs σc).map Prod.fst) T n
      (distInit (system σs σc) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_crash_adequacy (GF := GF) N T (system σs σc) g (fun _ v => v = #())
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
    -- the protocol: the connections' echo state (none yet), then the address's invariant
    letI := (extGlobalGS netExt (G := G)).allG
    imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnG) with ⟨%γm, Hm⟩
    imod inv_alloc echoN ⊤ (echoState (Gg := G) γm) $$ [Hm] with #HechoInv
    · inext
      unfold echoState
      iexists ∅
      iframe Hm
      iapply BigSepM.bigSepM_empty.2
      iempintro
    imod wire.addrInv_alloc addrN srvAddr (connProto (Gg := G) γm) $$ Hpend Htk with #HaddrInv
    imodintro
    simp only [system]
    unfold nodeStart
    isplitl []
    · -- the server: its host is `h`
      iintro %L %_ %_ - Hgs
      rw [Hs.packageState]
      imodintro
      simp only []
      unfold nodePre echoInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HechoInv
      ipureintro; decide
    isplitl []
    · -- the client
      iintro %L %_ %_ - Hgs
      rw [Hc.packageState]
      imodintro
      simp only []
      unfold nodePre echoInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HechoInv
      ipureintro; decide
    iempintro
  · -- every generation of every node: its boot program, and its next precondition
    intro hG _ _ i e σ Hes Hlctx
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    have Hnode : (i = 0 ∧ e = boot_server ∧ σ = σs) ∨ (i = 1 ∧ e = boot_client ∧ σ = σc) := by
      match i, Hes with
      | 0, Hes => cases Hes; exact .inl ⟨rfl, rfl, rfl⟩
      | 1, Hes => cases Hes; exact .inr ⟨rfl, rfl, rfl⟩
    have Hl : σ.goState.goLctx = lctx := by
      rcases Hnode with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact Hs.goLctx
      · exact Hc.goLctx
    rw [Hl] at Hlctx
    subst Hlctx
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold nodePre
    iintro ⟨⟨%γm, #Hinvs⟩, #Hplan, Hgs⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · iapply wp_boot_server _ (cmd.server.wp_main net.Listen.wp_proof
          net.Listener.Accept.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
          net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_boot_client _ (cmd.client.wp_main wire.wp_RandomInt net.Dial.wp_proof
          (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
          net.Conn.Close.wp_proof sync.WaitGroup.wp_Add sync.WaitGroup.wp_Done
          sync.WaitGroup.wp_Wait γm) $$ [] Hgs
        iframe Hinvs Hplan
    · -- after a crash: the host is kept, the rest is persistent
      iintro %L' _ - Hgs' _
      imodintro
      iframe Hgs' Hplan
      iexists γm
      iexact Hinvs
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    rcases hn with rfl | rfl
    · exact Hs.threads
    · exact Hc.threads

set_option linter.unusedVariables false in
/-- Crash safety of the acceptloop system, its two nodes the example's commands, each its own
process (`boot_server`, `boot_client`), in the deployment `Impl.lean`'s D13 assumes: in every
execution with crashes of the two nodes (`DistCrashNsteps`, the real semantics: a crash of a node
restarts it with its boot program, from a crashed local state, the network's connections and the
bytes in flight on them kept), from local states whose Go contexts satisfy the Go semantics and
the assumptions of the commands' packages (and of the packages they import), with no
package initialized and their main threads only, where the server's host is `h`, the plan has
`SrvAddr` at `h` and is the map of a well-formed list `pl` (D20, `PlanWellFormed`, checked by
`decide`) and the network has no connection yet, every boot program returns `#()` if it returns, no
thread of any node is stuck and none has an unrecovered panic: each of the client's
two concurrent calls gets its own id back (or gives up), however the server's handler goroutines
and the client's calls interleave, however connections fail, and however often either node
crashes. (`acceptloop_crash_safety_bounded` with the ghost state `netGF`, the step bound `n + 1`
and the thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem acceptloop_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] [client_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc)
    (Hconns : (extGlobal netExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σs σc).map Prod.fst) n
      (distInit (system σs σc) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  acceptloop_crash_safety_bounded (GF := netGF) (n + 1) (n + 2) σs σc g Hs Hc Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads))

end adequacy

/-- The plan of `acceptloop_crash_safety`'s deployment, the server's address at its host, is well
formed (D20). -/
example : addrOk srvAddr = true := by decide

#print axioms acceptloop_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop

end Perennial
