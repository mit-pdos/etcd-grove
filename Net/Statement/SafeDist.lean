/-
**The statement of a distributed program's safety over the net extension, without restarts**
(`SafeDist`): dsverify-lab's statement of its network kits (`old/dsverify/harness/lean/Harness/
SafeDist.lean`), restated over this repository's net extension (`netExts`, `GooseLang/Ext/Net/`),
with the plan's premise `PlanWellFormed` (`GooseLang/Ext/Net/Deploy.lean`, D20) in place of the
lab's `NetConfig.WellFormed`, and over `goose_dist_adequacy` (no crash and restart:
`notes/dsverify-net-port-plan.md`, Q4; a process's death is a cut for its peers, D10, D11).

A node (`Node`) is a Go package's boot program (initialize the package, then call its function
`main` with the node's constant arguments) and the class of facts goose's translation assumes of
the Go context (`Assumptions`: for a program, the conjunction of its packages' generated
`Assumptions` and `net.FieldAssumptions`). The system is the list of nodes, run by Perennial's
distributed semantics (`DistNsteps`): each node has its own threads, heap and Go context, and they
share the extension's global state, the network.

The deployment is data: the plan `pl` (address, host) pairs, the network's plan as a map
(`GMap.ofList pl`), and the nodes' hosts `hosts` (node `i` on `hosts[i]`, the extension's local
state there, what a `Listen` needs: `ListenAt`, D6, D21).

`SafeDist nodes pl hosts` says: the plan is well formed (`PlanWellFormed`, D20, decidable), there
is a host per node, and from a start where every node has its Go context (meeting its
assumptions), no package initialized and one thread, node `i` is on `hosts[i]`, and the network has
the plan `pl` and no connection (`NetStart`), in every execution, at every node, a finished main
thread returned `#()`, no thread is stuck and no thread has an unrecovered panic (`Ok`).

The bridge (`safeDist_of_bootAt`; `safeDist_of_proto` also makes the protocol library's ghost
state): WPs of the nodes' boot programs from the extension's start resources for the plan's
addresses (each address unset, `addrUnset`, the kits' protocol library
`GooseLang/Ext/Net/Proto.lean`; and the plan, the ghost state's), node `i`'s
using that its host is `hosts[i]` (`NodeBootWpAt`), give `SafeDist`. A program that keeps the
network's resources in its own protocol rather than the library's gets them back from `addrUnset`
(`netPend`, `netPlan`). `goose_dist_adequacy` is instantiated with the ghost state `netGF`
(`Adequacy.lean`).
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.Golang.Defn
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Deploy
public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-! ## The statement -/

section statement
variable [GoGlobalContext]

/-- A node: its package's assumptions on the Go context, its `initialize'`, the name of the
function its boot program calls, and the constant arguments it calls it with. -/
structure Node where
  Assumptions : [GoLocalContext] → [GoSemanticsFunctions] → Prop
  init : val
  main : GoString
  args : List val := []

/-- The call of `main` with `args`, as goose calls a function: resolve it, then apply it to each
argument in turn, or to `#()` if it has no parameters. -/
def callArgs (main : GoString) : List val → Expr
  | [] => App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #())
  | a :: rest => (a :: rest).foldl (fun e x => App e (Val x))
      (App (Val (GoInstruction (FuncResolve main []))) (Val #()))

/-- A node's boot program: initialize the package, then call `main` with `args`. -/
def Node.boot (nd : Node) : Expr :=
  Seq (App (Val nd.init) (Val #())) (callArgs nd.main nd.args)

/-- A node's start state: a Go context with the Go semantics in which its package's assumptions
hold, no package initialized, the main thread only. -/
structure NodeStart (nd : Node) (σ : state) : Prop where
  sem : ∃ s : @go.Semantics _ σ.goState.goLctx _,
    @Node.Assumptions nd σ.goState.goLctx s.sem_fn
  pkgs : σ.goState.packageState = ∅
  threads : σ.threads = 1

/-- The network's start: the plan `pl`, no connection. -/
def NetStart (pl : List (GoString × GoString)) (g : GlobalState) : Prop :=
  (extGlobal netExt g.globalWorld).plan = GMap.ofList pl ∧
    (extGlobal netExt g.globalWorld).conns = ∅

/-- The configuration in which node `i` runs its boot program from `σs[i]`. -/
def distStart (nodes : List Node) (σs : List state) (g : GlobalState) : DistCfg :=
  distInit (nodes.zipWith (fun nd σ => (nd.boot, σ)) σs) g

/-- A node is safe: a finished main thread returned `#()`, no thread is stuck, none has an
unrecovered panic. -/
def Ok (tp : List Expr) (σ : state) (g : GlobalState) : Prop :=
  (∀ v tp', tp = Val v :: tp' → v = #()) ∧ (∀ e, e ∈ tp → RealNotStuck e (σ, g)) ∧
    (∀ e, e ∈ tp → ¬ UnrecoveredPanic e)

/-- The distributed statement: the plan is well formed, there is a host per node, and every
execution of the nodes from a start (node `i` on `hosts[i]`) is safe at every node. -/
def SafeDist (nodes : List Node) (pl : List (GoString × GoString)) (hosts : List GoString) :
    Prop :=
  PlanWellFormed pl ∧ hosts.length = nodes.length ∧
  ∀ (σs : List state) (g : GlobalState), σs.length = nodes.length →
    (∀ (i : Nat) (nd : Node) (σ : state), nodes[i]? = some nd → σs[i]? = some σ →
      NodeStart nd σ) →
    (∀ (i : Nat) (h : GoString) (σ : state), hosts[i]? = some h → σs[i]? = some σ →
      (extLocal netExt σ.world).host = h) →
    NetStart pl g →
  ∀ (n : Nat) (κs : List Observation) (c : DistCfg),
    DistNsteps n (distStart nodes σs g) κs c →
  ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) → Ok tp σ c.global

end statement

/-! ## The bridge -/

attribute [local instance] GooseGlobalGS.gooseInvGS

section bridge
variable [GoGlobalContext]

/-- Node `nd`'s boot program, on the host `h`, is safe from `P`: for any local ghost state over
the global one, under the Go semantics and the package's assumptions its start gives, from no
package initialized, given that its host is `h`. -/
def NodeBootWpAt [G : GooseGlobalGS .hasLC netGF] (nd : Node) (h : GoString) (P : IProp netGF) :
    Prop :=
  ∀ (hG : HeapGS .hasLC netGF) (s : go.Semantics), hG.goose_globalGS = G →
    @Node.Assumptions nd hG.goose_localGS.goose_go_local_context s.sem_fn →
    P ⊢ ⌜(extLocalGS netExt (L := hG.goose_localGS)).host = h⌝ -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP nd.boot @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- A node's obligation in `goose_dist_adequacy` (`nodeWp`) from `NodeBootWpAt`. -/
theorem nodeWp_of_bootAt [G : GooseGlobalGS .hasLC netGF] (T : Nat) (nd : Node) (h : GoString)
    (σ : state) (P : IProp netGF) (hst : NodeStart nd σ)
    (hh : (extLocal netExt σ.world).host = h) (H : NodeBootWpAt nd h P) :
    P ⊢ nodeWp T nd.boot σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  obtain ⟨s, hA⟩ := hst.sem
  have hpk := hst.pkgs
  obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
  unfold nodeWpBody
  iintro %_ %hL Hls Hgs -
  subst hL
  rw [hpk]
  ihave Hl := net_localStart (L := ⟨Lexts, σ.goState.goLctx, Lheap, Lgs, Lthr, Lcr⟩) σ.world
    $$ Hls
  iunfold lisStart at Hl
  icases Hl with ⟨%Hhost, -⟩
  imodintro
  iapply H ⟨G, ⟨Lexts, σ.goState.goLctx, Lheap, Lgs, Lthr, Lcr⟩⟩ s rfl hA $$ HP [] Hgs
  ipureintro
  exact Hhost.trans hh

theorem bigSepL_nodeWp [G : GooseGlobalGS .hasLC netGF] (T : Nat) :
    ∀ (nodes : List Node) (σs : List state) (Ps : Nat → IProp netGF),
    σs.length = nodes.length →
    (∀ (i : Nat) (nd : Node) (σ : state), nodes[i]? = some nd → σs[i]? = some σ →
      Ps i ⊢ nodeWp T nd.boot σ (fun v => v = #())) →
    ([∗list] i ↦ _nd ∈ nodes, Ps i) ⊢
      [∗list] _i ↦ n ∈ nodes.zipWith (fun nd σ => (nd.boot, σ)) σs,
        nodeWp T n.1 n.2 (fun v => v = #())
  | [], σs, _, _, _ => by
    simp only [List.zipWith_nil_left]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | nd :: nodes, [], _, hl, _ => by simp at hl
  | nd :: nodes, σ :: σs, Ps, hl, H => by
    simp only [List.zipWith_cons_cons]
    iintro Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H0, Hr⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · iapply H 0 nd σ rfl rfl $$ H0
    · iapply bigSepL_nodeWp T nodes σs (fun i => Ps (i + 1)) (by simpa using hl)
        (fun i nd' σ' h1 h2 => H (i + 1) nd' σ' h1 h2) $$ Hr

/-- The bridge: an update from the extension's start resources (every plan address unset) to a
share `Ps i` for each node `i`, and each node's boot program safe from its share on its host
(`NodeBootWpAt`), give `SafeDist`. -/
theorem safeDist_of_bootAt (nodes : List Node) (pl : List (GoString × GoString))
    (hosts : List GoString) (Hpl : PlanWellFormed pl) (Hlen : hosts.length = nodes.length)
    (Hstart : ∀ [GooseGlobalGS .hasLC netGF],
      ⊢ ⌜(NG (hlc := .hasLC) (GF := netGF)).plan = GMap.ofList pl⌝ -∗
        ([∗list] x ∈ pl, addrUnset x.1) ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (nd : Node) (h : GoString), nodes[i]? = some nd → hosts[i]? = some h →
            NodeBootWpAt nd h (Ps i)⌝ ∗
          [∗list] i ↦ _nd ∈ nodes, Ps i) :
    SafeDist nodes pl hosts := by
  refine ⟨Hpl, Hlen, ?_⟩
  intro σs g hlen hstart hhosts hnet n κs c hsteps i tp σ hi
  have hmem : ∀ x, x ∈ nodes.zipWith (fun nd σ => (nd.boot, σ)) σs →
      ∃ (j : Nat) (nd : Node), nodes[j]? = some nd ∧ σs[j]? = some x.2 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_zipWith]
    refine ⟨j, nodes[j]'(by simp at hj; omega), by simp, by simp⟩
  have hkeys : keysDistinct pl = true := by
    unfold PlanWellFormed at Hpl
    simp only [Bool.and_eq_true] at Hpl
    exact Hpl.1
  have H := goose_dist_adequacy (GF := netGF) (n + 1) (n + 2)
    (nodes.zipWith (fun (nd : Node) (σ : state) => (nd.boot, σ)) σs) g
    (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm)
    ⟨hnet.2, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩) ?_ n κs c hsteps (Nat.lt_succ_self n) ?_
    (DistThreadsBelow.of_single ?_) i tp σ hi
  · exact ⟨H.1, H.2.1, H.2.2⟩
  · intro G _
    iintro Hg
    ihave Hnet := net_globalStart g.globalWorld $$ Hg
    icases netStart_plan _ _ $$ Hnet with %hplan
    rw [hnet.1] at hplan
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) pl hnet.1 hkeys $$ Hnet
    imod Hstart $$ %hplan Hs with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply bigSepL_nodeWp (n + 2) nodes σs Ps hlen ?_ $$ HPs
    intro j nd σ' hnd hσ
    have hj : j < hosts.length := by
      rw [Hlen]; exact (List.getElem?_eq_some_iff.mp hnd).1
    have hh : hosts[j]? = some hosts[j] := List.getElem?_eq_getElem hj
    exact nodeWp_of_bootAt (n + 2) nd hosts[j] σ' (Ps j) (hstart j nd σ' hnd hσ)
      (hhosts j _ σ' hh hσ) (HP j nd _ hnd hh)
  · intro x hx
    obtain ⟨j, nd, hnd, hσ⟩ := hmem x hx
    exact (hstart j nd x.2 hnd hσ).threads
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    obtain ⟨k, nd, hnd, hσ⟩ := hmem x (List.mem_of_getElem? hx)
    exact (hstart k nd x.2 hnd hσ).threads

/-- `safeDist_of_bootAt` with the library's ghost state made first (`netProto_alloc`): the
obligation gets the registry's names and every plan address unset, and sets their protocols
itself (`addrs_set_proto`). -/
theorem safeDist_of_proto (nodes : List Node) (pl : List (GoString × GoString))
    (hosts : List GoString) (Hpl : PlanWellFormed pl) (Hlen : hosts.length = nodes.length)
    (Hstart : ∀ [GooseGlobalGS .hasLC netGF] [NetProtoGS],
      ⊢ regCtx -∗ ⌜(NG (hlc := .hasLC) (GF := netGF)).plan = GMap.ofList pl⌝ -∗
        ([∗list] x ∈ pl, addrUnset x.1)
        ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (nd : Node) (h : GoString), nodes[i]? = some nd → hosts[i]? = some h →
            NodeBootWpAt nd h (Ps i)⌝ ∗
          [∗list] i ↦ _nd ∈ nodes, Ps i) :
    SafeDist nodes pl hosts := by
  refine safeDist_of_bootAt nodes pl hosts Hpl Hlen ?_
  intro G
  iintro %hplan Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π $$ Hreg %hplan Hs

end bridge

end Net
end Perennial
