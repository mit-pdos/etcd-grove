/-
The end-to-end result of `examples/net/preface`: the distributed crash safety of the three-node
system over TCP (`GooseLang/Ext/Net`).

The nodes are the example's commands `cmd/server`, `cmd/client` and `cmd/junk`
(`examples/net/preface/cmd/<node>/main.go`, whose `main`s call `Serve`, `Call` and `SendJunk`), each
a process of its own, as the package's process tests run them over real TCP. Node `i` runs its
command's program (`boot_server`, `boot_client`, `boot_junk`: initialize the command's package,
which initializes its imports, then call its `main`), at the start and after every crash of the
node (a process that exits or is killed and restarted: the semantics covers what its peers then
see, `Impl.lean` D10/D11). The theorem assumes the deployment of `Impl.lean` D13 (a closed world:
the network holds only the system's processes; addresses that do not alias; non-ephemeral ports;
the target configuration), with a well-formed plan (D20, `PlanWellFormed`, checked by `decide`
below). The plan has the server's address `SrvAddr` at a host `h`, which is the server node's; the
client and the junk sender may be on any host (the server's too). The network starts with no
connection.

The precondition of a node's program, over the local ghost state `L` of a generation of the node
(`nodePre`), is preface's protocol (`pfInvs`, `Defs.lean`: the address's invariant and every
connection's state: its directions' stream protocols and its reply state), the plan's entry for
`SrvAddr` (and that the network's plan, which the extension's ghost state carries, has it at `h`:
`Listen` resolves its address through the plan), a fresh package state (of the command's program,
whose package table is the command's `getIsPkgInit`) and, for the server, its host. The global setup allocates the protocol from the
network's start resources (`SrvAddr`'s pending set, empty); each node's first generation gets its
precondition from its start resources (its host); a crash keeps the host (`net_crashStart`), and
the rest is persistent, so every generation's proof guarantees the next one's precondition.

The conclusion, `preface_crash_safety`, mentions no ghost state and no bounds: in every execution of
the system with crashes, no thread of any node is stuck and none has an unrecovered panic, so the
client's check (the 1-byte reply it read in full is its request, the byte it sent after the
preface) never fails, whatever the junk sender sends (half a preface, which the server's deadline
lets it give up on), however the connections fail, with whatever kind of error (closed, timeout,
system), whether a failed dial leaves its connection abandoned for the server to accept (D16), or
the nodes crash or exit (a crash does not clear the bytes in flight on a connection: the network is
global state). The server's deadline comes from `time.Now`, which Perennial proves (since its
`932c9c388`) over its trusted model of the runtime's clock (`runtimeNow`: any reading); `#print
axioms` below lists what the result rests on, with the translation's axiomatized types.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.client.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.client.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.junk.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.cmd.junk.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.RandomLinked
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__SetDeadline
public import Perennial.Proof.time.Link
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import Robustness.Statement
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

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
preface's protocol, the plan's entry for `SrvAddr` (at `h`, also in the ghost state's plan), a fresh
package state, and for the server (`i = 0`), that its host is `h`. -/
def nodePre [G : GooseGlobalGS .hasLC GF] (i : Nat) (L : GooseLocalGS GF) :
    IProp GF :=
  iprop((∃ γm, pfInvs (Gg := G) γm) ∗ ⌜addrOk srvAddr = true⌝ ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

set_option linter.unusedVariables false in
/-- `preface_crash_safety` for executions of fewer than `N` steps along which every node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`:
`goose_dist_crash_adequacy` for the system. The plan is well formed (D20, checked by `decide`); the
proof does not need it. -/
theorem preface_crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_s : cmd.server.Assumptions] [package_c : cmd.client.Assumptions]
    [package_j : cmd.junk.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
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
    -- preface's protocol: the connections' state (none yet), then the address's invariant
    letI := (extGlobalGS netExt (G := G)).allG
    imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := PfNames) with ⟨%γm, Hm⟩
    imod inv_alloc pfN ⊤ (pfState (Gg := G) γm) $$ [Hm] with #HpfInv
    · inext
      unfold pfState
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
      unfold nodePre pfInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HpfInv
      ipureintro; exact HGp
    isplitl []
    · -- the client
      iintro %L %_ %_ - Hgs
      rw [Hc.packageState]
      imodintro
      simp only []
      unfold nodePre pfInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HpfInv
      ipureintro; exact HGp
    isplitl []
    · -- the junk sender
      iintro %L %_ %_ - Hgs
      rw [Hj.packageState]
      imodintro
      simp only []
      unfold nodePre pfInvs
      iframe Hgs
      isplitl []
      · iexists γm
        iframe HaddrInv HpfInv
      ipureintro; exact HGp
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
    iintro ⟨⟨%γm, #Hinvs⟩, #Hplan, Hgs⟩ _
    imodintro
    isplitl [Hgs]
    · rcases Hnode with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · iapply wp_bootOf _ _ _ _ _ (cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf)
          (cmd.server.wp_main net.Listen.wp_proof net.Listener.Accept.wp_proof
            (wire.ReadFull.wp_proof net.Conn.Read.wp_proof) net.Conn.Write.wp_proof
            net.Conn.Close.wp_proof net.Conn.SetDeadline.wp_proof time.wp_Now time.Time.wp_Add
            γm) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_bootOf _ _ _ _ _ (cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf)
          (cmd.client.wp_main wire.wp_RandomBytes net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
      · iapply wp_bootOf _ _ _ _ _ (cmd.junk.wp_initialize' _ cmd.junk.getIsPkgInit_wf)
          (cmd.junk.wp_main wire.wp_RandomInt wire.wp_RandomBytes net.Dial.wp_proof (wire.ReadFull.wp_proof net.Conn.Read.wp_proof)
            net.Conn.Write.wp_proof net.Conn.Close.wp_proof γm) $$ [] Hgs
        iframe Hinvs Hplan
    · -- after a crash: the host is kept, the rest is persistent
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
crashes. (`preface_crash_safety_bounded` with the ghost state `netGF`, the step bound `n + 1` and the
thread bound `n + 2`, which an execution of `n` steps from single threads respects,
`DistCrashThreadsBelow.of_single`.) The plan is well formed (D20: `PlanWellFormed pl`, decidable,
checked by `decide` on a concrete plan, as below). -/
theorem preface_crash_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_s : cmd.server.Assumptions] [package_c : cmd.client.Assumptions]
    [package_j : cmd.junk.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
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
  preface_crash_safety_bounded (GF := netGF) (n + 1) (n + 2) σs σc σj g Hs Hc Hj Hconns n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hs.threads
      | 1, hi => cases hi; exact Hc.threads
      | 2, hi => cases hi; exact Hj.threads))

end adequacy

/-- The example's plan, `SrvAddr` at a host, is well formed (D20). -/
example : addrOk srvAddr = true := by decide

#print axioms preface_crash_safety

end github_com.mit_pdos.etcd_grove.examples.net.preface

end Perennial
