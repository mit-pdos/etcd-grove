/-
The end-to-end result of `examples/net/duplex`: the distributed crash safety of the two-node
system over TCP (`GooseLang/Ext/Net`), with a reader and a writer goroutine on one end.

The nodes are the example's commands, each its own process: `cmd/server` (its `main` calls
`Serve`) and `cmd/client` (`Call`), as the package's process tests run them over real TCP. A
node runs its command's program, `boot_server` or `boot_client` (the command's package
initialization, then its `main`, as Go runs a program), at the start and after every crash or exit
of its process (`Impl.lean` D10, D11), each with its own program's package table
(`cmd/<node>/PkgTable.lean`). The plan has the server's address `SrvAddr` at a host `h`, which is
the server node's; the client may be on any host (the server's too). The plan is well formed
(`Impl.lean` D20, `Deploy.lean`'s `PlanWellFormed`, checked by `decide` on the example's plan
below). The network starts with no connection.

The precondition of a node's program, over the local ghost state `L` of a generation of the
node (`nodePre`), is the protocol (`dupInvs`, `Defs.lean`: the address's invariant and every
connection's state, `dupInvs_alloc`), the plan's entry for `SrvAddr` (its resource, which `Dial`
takes, and the network's plan's, which `Listen` reads), a fresh package state and, for the server,
its host; the command's `wp_main` (`cmd/<node>/Main.lean`) proves its program from
it. The global setup allocates the protocol from the network's start resources (`SrvAddr`'s
pending set, empty); each node's first generation gets its precondition from its start
resources (its host); a crash keeps the host (`net_crashStart`), and the rest is persistent, so
every generation's proof guarantees the next one's precondition. (The client's end's invariant,
`cliInv`, is allocated by `Call` after its dial.)

The conclusion, `duplex_crash_safety`, mentions no ghost state and no bounds: in every execution of
the system with crashes, no thread of any node is stuck and none has an unrecovered panic, so the
client's check (the bytes 1, 2, 3, 4 its reader reads come back in order) never fails, however its
writer and reader interleave, however much each read returns, however the connections fail or
the nodes crash, and however a failed dial leaves its connection (abandoned, D16: the server may
accept it and read EOF). The theorems assume the deployment of `Impl.lean` D13 (a closed world, the
target configuration) and take its well-formed plan (D20: addresses that do not alias, ports
outside the ephemeral range) as a premise.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.PkgTable
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
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

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

/-- A program, its package initialization `init` then its function `f`, from the initialization's
spec (over the program's package table `get`, giving `I`) and a spec of `f` with precondition
`I ∗ P`. -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (f : GoString) (get : GoString → IProp GF) (I P : IProp GF)
    (Hinit : {{ ownInitializing get }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing get ∗ I }})
    (Hf : {{ I ∗ P }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗
      WP (Seq (App (Val init) (Val #()))
        (App (App (Val (GoInstruction (FuncResolve f []))) (Val #())) (Val #())))
        @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  wp_apply Hinit $$ [Hgs] as ⟨-, Hpkg⟩
  · -- no package is initialized
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP Hpkg]
  · iframe
  ipureintro; rfl

/-- The precondition of node `i`'s program in the generation with local ghost state `L`:
the protocol, the plan's entry for `SrvAddr` (at `h`: its resource, and the network's plan's), a
fresh package state, and for the server (`i = 0`), that its host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop((∃ γm, dupInvs (Gg := G) γm) ∗ ⌜addrOk srvAddr = true⌝ ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

set_option linter.unusedVariables false in
/-- `duplex_crash_safety` for executions of fewer than `N` steps along which every node has
fewer than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. The plan `pl` is well formed (D20, checked by `decide`:
the `example` after the theorems). -/
theorem duplex_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
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
    -- the protocol: every connection's state (none yet), then the address's invariant
    imod dupInvs_alloc (Gg := G) $$ Hpend Htk with ⟨%γm, #Hinvs⟩
    imodintro
    simp only [system]
    unfold nodeStart
    isplitl []
    · -- the server: its host is `h`
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
    iempintro
  · -- every generation of every node: its program, and its next precondition
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
      · unfold boot_server
        iapply wp_boot _ _ _ _ _
          (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf)
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            net.Conn.Read.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · unfold boot_client
        iapply wp_boot _ _ _ _ _
          (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf)
          (cmd.client.wp_main net.Dial.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof γm) $$ [] Hgs
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
/-- Crash safety of the duplex system, its nodes the commands `cmd/server` and `cmd/client`, each
its own process running its command's program (`boot_server`, `boot_client`), in the deployment
`Impl.lean` D13 assumes: in every execution with crashes of the two nodes
(`DistCrashNsteps`, the real semantics: a crash or exit of a node restarts it with its program, from
a crashed local state, the network's connections and the bytes in flight on them kept), from
local states whose Go contexts satisfy the Go semantics and the commands' assumptions, with no
package initialized and their main threads only, where the server's host is `h`, the plan has
`SrvAddr` at `h`, the plan is well formed (D20, checked by `decide`: the `example` below) and
the network has no connection yet, every program returns `#()` if it
returns, no thread of any node is stuck and none has an unrecovered panic: the bytes the
client's reader reads are 1, 2, 3, 4 in order (or it gives up), however its writer and reader
interleave, however the connections fail (bytes lost, a FIN or a reset at any read or write), and
however often either node crashes, whatever the failures' error kinds (closed, timeout, sys:
none ends a node's loop badly) and however a failed dial leaves its connection (abandoned, D16).
(`duplex_crash_safety_bounded` with the ghost state `netGF`, the step bound `n + 1`
and the thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem duplex_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
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
  duplex_crash_safety_bounded (GF := netGF) (n + 1) (n + 2) σs σc g Hs Hc Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads))

end adequacy

/-- The example's plan, `SrvAddr` at a host, is well formed (D20). -/
example : addrOk srvAddr = true := by decide

#print axioms duplex_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.duplex

end Perennial
