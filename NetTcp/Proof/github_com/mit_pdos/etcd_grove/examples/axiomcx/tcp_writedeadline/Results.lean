/-
The closed form of the counterexample of `notes/axiom-review/tcp-semantics.md`, v3
(`examples/axiomcx/tcp-writedeadline`): the safety, under the TCP extension's semantics
(`GooseLang/Ext/Tcp`), of the one-node system that runs `Main` (initialize the package, then call
`Main`), the plan having `Addr` at the node's host `h` and being well formed (`PlanWellFormed`,
D20), the network having no connection. The deployment is the one the semantics allows: one
process on this machine, which listens at `127.0.0.1:7197`, dials it and accepts.

`writedeadline_safety` says that no thread ever has an unrecovered panic, so `Main`'s check (the
`Write`'s error is not a timeout) never fails. On Linux 7.0 with Go 1.27.3, `Main` panics in about
99 runs of 100 (`examples/axiomcx/tcp-writedeadline`, `TestMainPanics`, `repeat.sh`): the semantics
is refuted. The step that excludes Go's outcome is `WriteOutcome` (`Main.lean`,
`write_noTimeout`).

The theorem is over executions without crashes (`goose_dist_adequacy`): Go's run has none. (With
crashes the program is not safe in the model either: a connection dialed before a crash stays
pending, D7, and a restarted node may accept it and read a byte that its own `Write` did not write.
Linux resets such connections, so this is an extra behaviour of the model, not Go's.)

The precondition of `Main`: the plan's entry for `Addr` and `Addr`'s pending set, empty, both from
the network's start resources (`tcpStart`), and the node's host from its local start resources.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline.Main
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline.PkgTable
public import NetTcp.Proof.net.Conn__Read
public import NetTcp.Proof.net.Conn__Write
public import NetTcp.Proof.net.Conn__SetDeadline
public import NetTcp.Proof.net.Dial
public import NetTcp.Proof.net.Listen
public import NetTcp.Proof.net.Listener__Accept
public import NetTcp.Proof.net.OpError__Timeout
public import Perennial.Proof.time.Link
public import GooseLang.Ext.Tcp.Adequacy
public import GooseLang.Ext.Tcp.Deploy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp

/- The global setup of `goose_dist_adequacy` is under the global ghost state alone, whose
invariants are those of the fancy updates. -/
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The boot program of the node: initialize the package, then call `Main` (as goose calls a
function: resolve it, then apply it). -/
def boot [GoGlobalContext] : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Main []))) (Val #())) (Val #()))

/-- The system: the one node, from the local state `σ`. -/
def system [GoGlobalContext] (σ : state) : List (Expr × state) :=
  [(boot, σ)]

/-- A node's initial local state: its Go context is `lctx`, no package is initialized and it has
its main thread only. -/
structure NodeStart [GoGlobalContext] (lctx : GoLocalContext) (σ : state) : Prop where
  goLctx : σ.goState.goLctx = lctx
  packageState : σ.goState.packageState = ∅
  threads : σ.threads = 1

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The boot program, from a spec of `Main` with precondition `P` (and the package
initialized). -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics] [package_sem : Assumptions]
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF)
            pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline ∗ P }}
        (App (Val (@! Main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP boot @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
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

set_option linter.unusedVariables false in
/-- `writedeadline_safety` for executions of fewer than `N` steps along which the node has fewer
than `T` live threads, under any ghost state `GF` with `GooseGpreS GF`: `goose_dist_adequacy` for
the system. The plan is well formed (`Hwf`, D20; not used by the proof, it restricts the theorem
to the deployment D13 describes). -/
theorem writedeadline_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    [hPre : GooseGpreS GF] (N T : Nat) (σ0 : state) (g : GlobalState) (h : GoString)
    (H0 : NodeStart lctx σ0)
    (Hhost : (extLocal tcpExt σ0.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup addr = some h)
    (pl : List (GoString × GoString)) (Hwf : PlanWellFormed pl)
    (Hpl : (extGlobal tcpExt g.globalWorld).plan = GMap.ofList pl)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistNsteps n (distInit (system σ0) g) κs c)
    (Hbound : n < N)
    (Hlive : DistThreadsBelow T n (distInit (system σ0) g)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  refine goose_dist_adequacy (GF := GF) N T (system σ0) g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩
    (fun _ _ => ⟨trivial, trivial⟩) ?_ n κs c Hsteps Hbound ?_ Hlive
  · -- the global setup and the node
    intro G _
    iintro Hg
    icases tcp_globalStart g.globalWorld $$ Hg with Hnet
    unfold tcpStart
    icases Hnet with ⟨Hplans, Hpends, %HGplan⟩
    have HpS : PartialMap.get? (extGlobal tcpExt g.globalWorld).plan addr = some h := by
      rw [gmap_get?_eq]; exact Hplan
    ihave #Hp := (BigSepM.bigSepM_lookup (Φ := fun a h => tcpPlan (extGlobalGS tcpExt) a h) HpS)
      $$ Hplans
    have Hpe : PartialMap.get? (pendInit (extGlobal tcpExt g.globalWorld)) addr = some ∅ := by
      rw [gmap_get?_eq]; simp [pendInit, GMap.lookup_fmap, Hplan]
    ihave Hpend := (BigSepM.bigSepM_lookup (Φ := fun a S => tcpPend (extGlobalGS tcpExt) a S) Hpe)
      $$ Hpends
    have HGp : (extGlobalGS tcpExt (G := G)).plan !! addr = some h := by
      rw [HGplan]; exact Hplan
    imodintro
    simp only [system]
    isplitl
    · unfold nodeWp
      iintro %L
      obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
      unfold nodeWpBody
      iintro %_ %Hlctx Hstart Hgs -
      ihave Hl := tcp_localStart (L := ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩) σ0.world $$ Hstart
      iunfold lisStart at Hl
      icases Hl with ⟨%Hh, -⟩
      rw [H0.packageState]
      rw [H0.goLctx] at Hlctx
      subst Hlctx
      imodintro
      simp only []
      letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
      iapply (wp_boot _ (wp_Main net.Listen.wp_proof net.Dial.wp_proof
        net.Listener.Accept.wp_proof net.Conn.Read.wp_proof net.Conn.Write.wp_proof
        net.Conn.SetDeadline.wp_proof net.OpError.Timeout.wp_proof time.Now.wp_proof)) $$ [Hpend] Hgs
      rw [show (extLocalGS tcpExt (L := hG.goose_localGS)).host = h from Hh.trans Hhost]
      iframe Hp Hpend
      ipureintro
      exact HGp
    iempintro
  · intro n hn
    simp only [system, List.mem_cons, List.not_mem_nil, _root_.or_false] at hn
    subst hn
    exact H0.threads

/-- Safety of the one-node system running `Main`, under the TCP extension's semantics: in every
execution without crashes (`DistNsteps`), from a local state whose Go context satisfies the Go
semantics and the package's assumptions, with no package initialized and its main thread only,
where the node's host is `h`, the plan has `Addr` at `h` and is well formed (`PlanWellFormed`, D20)
and the network has no connection yet, the boot program returns `#()` if it returns, no thread is
stuck and none has an unrecovered panic. False of Go on Linux: `Main` panics in about 99 runs of
100. (`writedeadline_safety_bounded` with the ghost state `tcpGF`, the step bound `n + 1` and the
thread bound `n + 2`.) -/
theorem writedeadline_safety [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σ0 : state) (g : GlobalState) (h : GoString)
    (H0 : NodeStart lctx σ0)
    (Hhost : (extLocal tcpExt σ0.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup addr = some h)
    (pl : List (GoString × GoString)) (Hwf : PlanWellFormed pl)
    (Hpl : (extGlobal tcpExt g.globalWorld).plan = GMap.ofList pl)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistNsteps n (distInit (system σ0) g) κs c) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → v = #()) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  writedeadline_safety_bounded (GF := tcpGF) (n + 1) (n + 2) σ0 g h H0 Hhost Hplan pl Hwf Hpl
    Hconns n κs c Hsteps (by omega)
    (DistThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, system, List.map_cons, List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact H0.threads))

/-- The deployment of `TestMainPanics`: `Addr` at the node's host, a well-formed plan. -/
example : PlanWellFormed [(addr, go!"h")] := by decide

end adequacy

#print axioms writedeadline_safety

end github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline

end Perennial
