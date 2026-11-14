/-
The end-to-end result of `examples/net/preface`: the distributed crash safety of the three-node
system over TCP (`GooseLang/Ext/Tcp`).

The nodes are the example's commands `cmd/server`, `cmd/client` and `cmd/junk`
(`examples/net/preface/cmd/<node>/main.go`, whose `main`s call `Serve`, `Call` and `SendJunk`), each
a process of its own, as the package's process tests run them over real TCP. Node `i` runs its
command's program (`boot_server`, `boot_client`, `boot_junk`: initialize the command's package,
which initializes its imports, then call its `main`), at the start and after every crash of the
node (a process that exits or is killed and restarted: the semantics covers what its peers then
see, `Impl.lean` D10/D11). The theorem assumes the deployment of `Impl.lean` D13 (a closed world:
the network holds only the system's processes; addresses that do not alias; non-ephemeral ports;
the target configuration). The plan has the server's address `SrvAddr` at a host `h`, which is the
server node's; the client and the junk sender may be on any host (the server's too). The network
starts with no connection.

The precondition of a node's program, over the local ghost state `L` of a generation of the node
(`nodePre`), is preface's protocol (`pfInvs`, `Defs.lean`: the address's invariant and every
connection's state: its directions' stream protocols and its reply state), the plan's entry for
`SrvAddr`, a fresh package state (of the command's program, whose package table is the command's
`getIsPkgInit`) and, for the server, its host. The global setup allocates the protocol from the
network's start resources (`SrvAddr`'s pending set, empty); each node's first generation gets its
precondition from its start resources (its host); a crash keeps the host (`tcp_crashStart`), and
the rest is persistent, so every generation's proof guarantees the next one's precondition.

The conclusion, `preface_crash_safety`, mentions no ghost state and no bounds: in every execution of
the system with crashes, no thread of any node is stuck and none has an unrecovered panic, so the
client's check (the 1-byte reply it read in full is its request, the byte it sent after the
preface) never fails, whatever the junk sender sends (half a preface, which the server's deadline
lets it give up on), however the connections fail or the nodes crash or exit (a crash does not
clear the bytes in flight on a connection: the network is global state). It rests on Perennial's
trust-boundary axiom `time.Now.wp_proof` (`time.Now` returns some time: the server's deadline),
which `#print axioms` below lists with the translation's axiomatized types.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server.PkgTable
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.client.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.client.PkgTable
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.junk.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.junk.PkgTable
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Proof.net.Conn__Read
public import NetTcp.Proof.net.Conn__Write
public import NetTcp.Proof.net.Conn__Close
public import NetTcp.Proof.net.Dial
public import NetTcp.Proof.net.Listen
public import NetTcp.Proof.net.Listener__Accept
public import NetTcp.Proof.net.Conn__SetDeadline
public import Perennial.Proof.time.Link
public import GooseLang.Ext.Tcp.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

/- The global setup of `goose_dist_crash_adequacy` is under the global ghost state alone, whose
invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The program of a command whose package's initializer is `init` and whose `main` is `main`:
initialize the command's package (and so its imports), then call its `main` (as goose calls a
function: resolve it, then apply it). -/
def bootOf [GoGlobalContext] (init : val) (main : GoString) : Expr :=
  Seq (App (Val init) (Val #()))
    (App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #()))

/-- The program of the server's command `cmd/server`. -/
abbrev boot_server [GoGlobalContext] : Expr := bootOf cmd.server.initialize' cmd.server.main
/-- The program of the client's command `cmd/client`. -/
abbrev boot_client [GoGlobalContext] : Expr := bootOf cmd.client.initialize' cmd.client.main
/-- The program of the junk sender's command `cmd/junk`. -/
abbrev boot_junk [GoGlobalContext] : Expr := bootOf cmd.junk.initialize' cmd.junk.main

/-- The system: the server, the client and the junk sender, each running its command's program,
from the local states `σs`, `σc` and `σj`. -/
def system [GoGlobalContext] (σs σc σj : state) : List (Expr × state) :=
  [(boot_server, σs), (boot_client, σc), (boot_junk, σj)]

/-- A node's initial local state: its Go context is `lctx`, no package is initialized and it has
its main thread only. -/
structure NodeStart [GoGlobalContext] (lctx : GoLocalContext) (σ : state) : Prop where
  goLctx : σ.goState.goLctx = lctx
  packageState : σ.goState.packageState = ∅
  threads : σ.threads = 1

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's program, from its initializer's spec (over the program's package table
`getIsPkgInit`, which gives the package `pkg`'s `isPkgInit`) and a spec of its `main` with
precondition `P` (and the package initialized). -/
theorem wp_bootOf [hG : HeapGS .hasLC GF] [sem : go.Semantics] (init : val) (main pkg : GoString)
    [IsPkgInit (IProp GF) pkg] (getIsPkgInit : GoString → IProp GF) (P : IProp GF)
    (Hinit : {{ ownInitializing getIsPkgInit }} (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIsPkgInit ∗ isPkgInit (PROP := IProp GF) pkg }})
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P }} (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (bootOf init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold bootOf
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

/-- The precondition of node `i`'s program in the generation with local ghost state `L`:
preface's protocol, the plan's entry for `SrvAddr` (at `h`), a fresh package state, and for the
server (`i = 0`), that its host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (h : GoString) (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop((∃ γm, pfInvs (Gg := G) γm) ∗ tcpPlan (extGlobalGS tcpExt) srvAddr h ∗
    ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ⌜i = 0 → (extLocalGS tcpExt (L := L)).host = h⌝)

/-- `preface_crash_safety` for executions of fewer than `N` steps along which every node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. -/
theorem preface_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_s : cmd.server.Assumptions] [package_c : cmd.client.Assumptions]
    [package_j : cmd.junk.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    [hPre : GooseGpreS GF] (N T : Nat) (σs σc σj : state) (g : GlobalState) (h : GoString)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc) (Hj : NodeStart lctx σj)
    (Hhost : (extLocal tcpExt σs.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup srvAddr = some h)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
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
    -- preface's protocol: the connections' state (none yet), then the address's invariant
    letI := (extGlobalGS tcpExt (G := G)).allG
    imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := PfNames) with ⟨%γm, Hm⟩
    imod inv_alloc pfN ⊤ (pfState (Gg := G) γm) $$ [Hm] with #HpfInv
    · inext
      unfold pfState
      iexists ∅
      iframe Hm
      iapply BigSepM.bigSepM_empty.2
      iempintro
    imod wire.addrInv_alloc addrN srvAddr (connProto (Gg := G) γm) $$ Hpend with #HaddrInv
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
      unfold nodePre pfInvs
      iframe Hgs Hp
      isplitl []
      · iexists γm
        iframe HaddrInv HpfInv
      ipureintro; intro _; exact Hh.trans Hhost
    isplitl []
    · -- the client
      iintro %L %_ %_ - Hgs
      rw [Hc.packageState]
      imodintro
      simp only []
      unfold nodePre pfInvs
      iframe Hgs Hp
      isplitl []
      · iexists γm
        iframe HaddrInv HpfInv
      ipureintro; intro h0; cases h0
    isplitl []
    · -- the junk sender
      iintro %L %_ %_ - Hgs
      rw [Hj.packageState]
      imodintro
      simp only []
      unfold nodePre pfInvs
      iframe Hgs Hp
      isplitl []
      · iexists γm
        iframe HaddrInv HpfInv
      ipureintro; intro h0; cases h0
    iempintro
  · -- every generation of every node: its program, and its next precondition
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
    iintro ⟨⟨%γm, #Hinvs⟩, #Hplan, Hgs, %Hh⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · iapply wp_bootOf _ _ _ _ _ (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf)
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof net.Conn.SetDeadline.wp_proof time.wp_Now time.Time.wp_Add
            γm) $$ [] Hgs
        rw [Hh rfl]
        iframe Hinvs Hplan
      · iapply wp_bootOf _ _ _ _ _ (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf)
          (cmd.client.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm h) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_bootOf _ _ _ _ _ (cmd.junk.wp_initialize' _ cmd.junk.getIsPkgInit_wf)
          (cmd.junk.wp_main net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm h) $$ [] Hgs
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
    rcases hn with rfl | rfl | rfl
    · exact Hs.threads
    · exact Hc.threads
    · exact Hj.threads

/-- Crash safety of the preface system, whose nodes are the example's commands `cmd/server`,
`cmd/client` and `cmd/junk`, each a process of its own running its command's program
(`boot_server`, `boot_client`, `boot_junk`), deployed as `Impl.lean` D13 assumes: in every
execution with crashes of the three nodes (`DistCrashNsteps`, the real semantics: a crash of a
node restarts it with its program, from a crashed local state, the network's connections and the
bytes in flight on them kept), from local states whose Go contexts satisfy the Go semantics and
the commands' assumptions, with no package initialized and their main threads only, where the server's host is `h`, the plan has
`SrvAddr` at `h` and the network has no connection yet, every program returns `#()` if it
returns, no thread of any node is stuck and none has an unrecovered panic: the client's check
holds, however connections fail, whatever the junk sender sends, and however often any node
crashes. (`preface_crash_safety_bounded` with the ghost state `tcpGF`, the step bound `n + 1` and the
thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) -/
theorem preface_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_s : cmd.server.Assumptions] [package_c : cmd.client.Assumptions]
    [package_j : cmd.junk.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc σj : state) (g : GlobalState) (h : GoString)
    (Hs : NodeStart lctx σs) (Hc : NodeStart lctx σc) (Hj : NodeStart lctx σj)
    (Hhost : (extLocal tcpExt σs.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup srvAddr = some h)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((system σs σc σj).map Prod.fst) n
      (distInit (system σs σc σj) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  preface_crash_safety_bounded (GF := tcpGF) (n + 1) (n + 2) σs σc σj g h Hs Hc Hj Hhost Hplan
    Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads
      | 2, hi => cases hi; exact Hj.threads))

end adequacy

#print axioms preface_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.preface

end Perennial
