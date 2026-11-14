/-
The end-to-end result of `examples/net/duplex`: the distributed crash safety of the two-node
system over TCP (`GooseLang/Ext/Tcp`), with a reader and a writer goroutine on one end.

The nodes are the example's commands, each its own process: `cmd/server` (its `main` calls
`Serve`) and `cmd/client` (`Call`), as the package's process tests run them over real TCP. A
node runs its command's program, `boot_server` or `boot_client` (the command's package
initialization, then its `main`, as Go runs a program), at the start and after every crash or exit
of its process (`Impl.lean` D10, D11), each with its own program's package table
(`cmd/<node>/PkgTable.lean`). The plan has the server's address `SrvAddr` at a host `h`, which is
the server node's; the client may be on any host (the server's too). The network starts with no
connection.

The precondition of a node's program, over the local ghost state `L` of a generation of the
node (`nodePre`), is the protocol (`dupInvs`, `Defs.lean`: the address's invariant and every
connection's state, `dupInvs_alloc`), the plan's entry for `SrvAddr`, a fresh package state and,
for the server, its host; the command's `wp_main` (`cmd/<node>/Main.lean`) proves its program from
it. The global setup allocates the protocol from the network's start resources (`SrvAddr`'s
pending set, empty); each node's first generation gets its precondition from its start
resources (its host); a crash keeps the host (`tcp_crashStart`), and the rest is persistent, so
every generation's proof guarantees the next one's precondition. (The client's end's invariant,
`cliInv`, is allocated by `Call` after its dial.)

The conclusion, `duplex_crash_safety`, mentions no ghost state and no bounds: in every execution of
the system with crashes, no thread of any node is stuck and none has an unrecovered panic, so the
client's check (the bytes 1, 2, 3, 4 its reader reads come back in order) never fails, however its
writer and reader interleave, however much each read returns, however the connections fail or
the nodes crash. The theorems assume the deployment of `Impl.lean` D13 (a closed world, addresses
that do not alias, ports outside the ephemeral range, the target configuration).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.server.PkgTable
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.cmd.client.PkgTable
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Proof.net.Conn__Read
public import NetTcp.Proof.net.Conn__Write
public import NetTcp.Proof.net.Conn__Close
public import NetTcp.Proof.net.Dial
public import NetTcp.Proof.net.Listen
public import NetTcp.Proof.net.Listener__Accept
public import GooseLang.Ext.Tcp.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

/- The global setup of `goose_dist_crash_adequacy` is under the global ghost state alone, whose
invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The server node's program, the command `cmd/server`: its package initialization, then its
`main` (as goose calls a function: resolve it, then apply it). -/
def boot_server [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.server.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.server.main []))) (Val #())) (Val #()))

/-- The client node's program, the command `cmd/client`. -/
def boot_client [GoGlobalContext] : Expr :=
  Seq (App (Val cmd.client.initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve cmd.client.main []))) (Val #())) (Val #()))

/-- The system: the server and the client, each its own process, from the local states `σs` and
`σc`. -/
def system [GoGlobalContext] (σs σc : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc)]

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
the protocol, the plan's entry for `SrvAddr` (at `h`), a fresh package state, and for the server
(`i = 0`), that its host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (h : GoString) (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop((∃ γm, dupInvs (Gg := G) γm) ∗ tcpPlan (extGlobalGS tcpExt) srvAddr h ∗
    ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ⌜i = 0 → (extLocalGS tcpExt (L := L)).host = h⌝)

/-- `duplex_crash_safety` for executions of fewer than `N` steps along which every node has
fewer than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. -/
theorem duplex_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] [client_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    [hPre : GooseGpreS GF] (N T : Nat) (σs σc : state) (g : GlobalState) (h : GoString)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc)
    (Hhost : (extLocal tcpExt σs.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup srvAddr = some h)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
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
    (fun _ _ => ⟨trivial, trivial⟩) (fun i L => nodePre h i L) ?_ ?_
    n κs c Hsteps Hbound ?_ Hlive
  · -- the global setup and the first generation of every node
    intro G _
    iintro Hg
    icases tcp_globalStart g.globalWorld $$ Hg with Hnet
    unfold tcpStart
    icases Hnet with ⟨Hplans, Hpends⟩
    have Hpl : PartialMap.get? (extGlobal tcpExt g.globalWorld).plan srvAddr = some h := by
      rw [gmap_get?_eq]; exact Hplan
    ihave #Hp := (BigSepM.bigSepM_lookup (Φ := fun a h => tcpPlan (extGlobalGS tcpExt) a h) Hpl)
      $$ Hplans
    have Hpe : PartialMap.get? (pendInit (extGlobal tcpExt g.globalWorld)) srvAddr = some ∅ := by
      rw [gmap_get?_eq]; simp [pendInit, GMap.lookup_fmap, Hplan]
    ihave Hpend := (BigSepM.bigSepM_lookup (Φ := fun a S => tcpPend (extGlobalGS tcpExt) a S) Hpe)
      $$ Hpends
    -- the protocol: every connection's state (none yet), then the address's invariant
    imod dupInvs_alloc (Gg := G) $$ Hpend with ⟨%γm, #Hinvs⟩
    imodintro
    simp only [system]
    unfold nodeStart
    isplitl []
    · -- the server: its host is `h`
      iintro %L %_ %_ Hstart Hgs
      ihave Hl := tcp_localStart (L := L) σs.world $$ Hstart
      iunfold lisStart at Hl
      icases Hl with ⟨%Hh, -⟩
      rw [Hs.packageState]
      imodintro
      simp only []
      unfold nodePre
      iframe Hgs Hp
      isplitl []
      · iexists γm
        iexact Hinvs
      ipureintro; intro _; exact Hh.trans Hhost
    isplitl []
    · -- the client
      iintro %L %_ %_ - Hgs
      rw [Hc.packageState]
      imodintro
      simp only []
      unfold nodePre
      iframe Hgs Hp
      isplitl []
      · iexists γm
        iexact Hinvs
      ipureintro; intro h0; cases h0
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
    iintro ⟨⟨%γm, #Hinvs⟩, #Hplan, Hgs, %Hh⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · unfold boot_server
        iapply wp_boot _ _ _ _ _
          (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf)
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            net.Conn.Read.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        rw [Hh rfl]
        iframe Hinvs Hplan
      · unfold boot_client
        iapply wp_boot _ _ _ _ _
          (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf)
          (cmd.client.wp_main net.Dial.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof γm h) $$ [] Hgs
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
      intro hi
      rw [Hhost']
      exact Hh hi
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    rcases hn with rfl | rfl
    · exact Hs.threads
    · exact Hc.threads

/-- Crash safety of the duplex system, its nodes the commands `cmd/server` and `cmd/client`, each
its own process running its command's program (`boot_server`, `boot_client`), in the deployment
`Impl.lean` D13 assumes: in every execution with crashes of the two nodes
(`DistCrashNsteps`, the real semantics: a crash or exit of a node restarts it with its program, from
a crashed local state, the network's connections and the bytes in flight on them kept), from
local states whose Go contexts satisfy the Go semantics and the commands' assumptions, with no
package initialized and their main threads only, where the server's host is `h`, the plan has
`SrvAddr` at `h` and the network has no connection yet, every program returns `#()` if it
returns, no thread of any node is stuck and none has an unrecovered panic: the bytes the
client's reader reads are 1, 2, 3, 4 in order (or it gives up), however its writer and reader
interleave, however the connections fail (bytes lost, a FIN or a reset at any read or write), and
however often either node crashes. (`duplex_crash_safety_bounded` with the ghost state `tcpGF`, the step bound `n + 1`
and the thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem duplex_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [server_sem : cmd.server.Assumptions] [client_sem : cmd.client.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState) (h : GoString)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc)
    (Hhost : (extLocal tcpExt σs.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup srvAddr = some h)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σs σc).map Prod.fst) n
      (distInit (system σs σc) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  duplex_crash_safety_bounded (GF := tcpGF) (n + 1) (n + 2) σs σc g h Hs Hc Hhost Hplan
    Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads))

end adequacy

#print axioms duplex_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.duplex

end Perennial
