/-
The end-to-end result of `examples/net/halfclose`: the distributed crash safety of the two-node
system over TCP (`GooseLang/Ext/Net`).

The nodes are the example's commands, `cmd/server` (`main` calls `Serve`) and `cmd/client` (`main`
calls `Call`), each its own process: node `i` runs its command's program, `boot_server` or
`boot_client` (initialize the command's package, then call its `main`), at the start and after
every crash of the node, with its own package table (`cmd.server.getIsPkgInit_wf`,
`cmd.client.getIsPkgInit_wf`). A process may exit (the client's does, once `Call` returns): what
its peers then see is the semantics' (`Impl.lean`, D10/D11). The plan has the server's address
`SrvAddr` at a host `h`, which is the server node's; the client may be on any host (the server's
too). The network starts with no connection. The theorems are about the deployment `Impl.lean`'s
D13 assumes: these two processes are the only users of the network (a closed world), on the
target configuration, with a well-formed plan (D20, `PlanWellFormed`, a premise checked by `decide`:
its addresses do not alias and their ports are not ephemeral).

The precondition of a node's boot program, over the local ghost state `L` of a generation of the
node (`nodePre`), is halfclose's protocol (`hcInvs`, `Defs.lean`: the address's invariant and every
connection's state), the plan's entry for `SrvAddr` (also as the network's plan, which the
server's `Listen` needs, from the start resources' `hG.plan = g.plan`), a fresh package state and,
for the server, its host. The global setup allocates the protocol from the network's start resources (`SrvAddr`'s
pending set, empty); each node's first generation gets its precondition from its start resources
(its host); a crash keeps the host (`net_crashStart`), and the rest is persistent, so every
generation's proof guarantees the next one's precondition.

The conclusion, `halfclose_crash_safety`, mentions no ghost state and no bounds: in every execution
of the system with crashes, no thread of any node is stuck and none has an unrecovered panic, so
the client's check (a response read until EOF is a prefix of `"hello"`, the request it sent
before shutting its write side) never fails, however reads are split, however the connections
fail or break (EOF included: a killed server's kernel sends a FIN), whatever error each failure
carries (D14), whichever dials are abandoned (D16) and however the nodes crash.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client.PkgTable
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.TCPConn__CloseWrite
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose

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

/-- The server's program, from a spec of its `main` with precondition `P` (and the command's
package initialized), under the command's package table. -/
theorem wp_boot_server [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.server ∗ P }}
        (App (Val (@! cmd.server.main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP boot_server @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot_server
  wp_apply (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
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

/-- The client's program, from a spec of its `main`, under the command's package table. -/
theorem wp_boot_client [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    [client_sem : cmd.client.Assumptions] (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.net.halfclose.cmd.client ∗ P }}
        (App (Val (@! cmd.client.main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP boot_client @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot_client
  wp_apply (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
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
halfclose's protocol, the plan's entry for `SrvAddr` (at `h`: as the client's `Dial` needs it, and in
the network's plan, as the server's `Listen` does), a fresh package state, and for the server
(`i = 0`), that its host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop((∃ γm, hcInvs (Gg := G) γm) ∗ ⌜addrOk srvAddr = true⌝ ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

set_option linter.unusedVariables false in
/-- `halfclose_crash_safety` for executions of fewer than `N` steps along which every node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. The plan is the list `pl`, well formed (D20,
`PlanWellFormed`, which `decide` checks on a concrete plan: the example below); the proof does not
use it (it restricts the theorem to the deployment D13 describes). -/
theorem halfclose_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] [client_sem : cmd.client.Assumptions]
    [go.BasicIntoValInj]
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
    -- halfclose's protocol: the connections' states (none yet), then the address's invariant
    letI := (extGlobalGS netExt (G := G)).allG
    imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := HcNames) with ⟨%γm, Hm⟩
    imod inv_alloc hcN ⊤ (hcState (Gg := G) γm) $$ [Hm] with #HhcInv
    · inext
      unfold hcState
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
      unfold nodePre hcInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HhcInv
      ipureintro; exact HGp
    isplitl []
    · -- the client
      iintro %L %_ %_ - Hgs
      rw [Hc.packageState]
      imodintro
      simp only []
      unfold nodePre hcInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HhcInv
      ipureintro; exact HGp
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
          net.Listener.Accept.wp_proof net.Conn.Read.wp_proof net.Conn.Write.wp_proof
          net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_boot_client _ (cmd.client.wp_main net.Dial.wp_proof net.Conn.Read.wp_proof
          net.Conn.Write.wp_proof net.TCPConn.CloseWrite.wp_proof net.Conn.Close.wp_proof
          γm) $$ [] Hgs
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
/-- Crash safety of the halfclose system: in every execution with crashes of the two nodes, the
server's and the client's commands, each its own process (`DistCrashNsteps`, the real semantics: a
crash of a node restarts it with its command's program, from a crashed local state, the network's
connections and the bytes in flight on them kept), from local states whose Go contexts satisfy the
Go semantics and the commands' assumptions, with no package initialized and their main threads
only, where the server's host is `h`, the plan is a well-formed list `pl` (D20, `PlanWellFormed`,
checked by `decide`: the example below) with `SrvAddr` at `h` and the network has no connection
yet, every program returns `#()` if it returns, no thread of any node is stuck and none
has an unrecovered panic: the client's check holds, however connections fail and however often any
node crashes or exits. (The deployment is the one `Impl.lean`'s D13 assumes: a closed world of
these two processes, non-aliasing addresses, a non-ephemeral port, the target configuration.)
(`halfclose_crash_safety_bounded` with the ghost state `netGF`, the step bound `n + 1` and the
thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem halfclose_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] [client_sem : cmd.client.Assumptions]
    [go.BasicIntoValInj]
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
  halfclose_crash_safety_bounded (GF := netGF) (n + 1) (n + 2) σs σc g Hs Hc Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads))

end adequacy

/-- The plan of halfclose's deployment is well formed (D20). -/
example : addrOk srvAddr = true := by decide

#print axioms halfclose_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.halfclose

end Perennial
