/-
**From a kit's boot WPs to its robustness statement** (proved; `notes/dsverify-net-port-plan.md`,
phase 4): a kit's machines never crash, so its statement is `Robust [] nodes g bound`
(`Robustness/Statement.lean`) under the kit's deployment (`KitDeploy`, `KitDeploy.lean`), and this
file proves it from one WP per machine.

- With no crashing machine, the executions `Robust` quantifies over are plain distributed
  executions (`distNsteps_of_crash_nil`: `DistCrashNsteps []` has no crash step), so Perennial's
  adequacy theorem without crashes (`goose_dist_adequacy`, instantiated with the ghost state `netGF`
  and the extensions `netExts`, `GooseLang/Ext/Net/Adequacy.lean`) proves it. This covers the case
  where **every** machine is stable; a deployment with crashing and stable machines both (kvnet's)
  needs an adequacy theorem with boot programs for some nodes only (`notes/robustness.md`, "Next").
- `robust_of_kitBoot`: an update from the extension's start resources for the plan's addresses
  (each address unset, `addrUnset`, the kits' protocol library `GooseLang/Ext/Net/Proto.lean`; and
  the plan, the ghost state's) to a share `Ps i` for each machine `i`, and each machine's boot
  program safe from its share on its host (`KitBootWp`), give the kit's statement. A program that
  keeps the network's resources in its own protocol rather than the library's gets them back from
  `addrUnset` (`netPend`, `netPlan`).
- `robust_of_kitProto`: the same with the library's ghost state made first (`netProto_alloc`).

`KitBootWp`'s WP is under any ghost state whose Go context is the statement's `lctx` (`Robust`'s
`Fresh`), so the kit's `[go.Semantics]` and its packages' `Assumptions`, instances over `lctx`,
apply to it once the context is substituted.
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.Golang.Defn
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Proto
public import Net.Statement.KitDeploy
public import Robustness.Statement

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- With no boot program, an execution has no crash: it is a plain distributed execution. -/
theorem distNsteps_of_crash_nil [GooseExts] [GooseSemantics] [GoGlobalContext] {n : Nat}
    {c c' : DistCfg} {κs : List Observation} (h : DistCrashNsteps [] n c κs c') :
    DistNsteps n c κs c' := by
  induction h with
  | refl c => exact .refl c
  | cons hs _ ih =>
    cases hs with
    | step hs => exact .cons hs ih
    | crash _ hb _ => simp at hb

attribute [local instance] GooseGlobalGS.gooseInvGS

section bridge
variable [GoGlobalContext]

/-- A kit machine's boot program `e`, on the host `h`, is safe from `P`: under every ghost state
`hG` over the global one `G` whose Go context is `lctx` (the statement's, `Robust`'s `Fresh`), from
no package initialized, given that its host is `h`, it returns `#()` (a Go `main`'s result) and is
not stuck. (A proof destructs `hG` and substitutes the context, so that the kit's instances over
`lctx`, `[go.Semantics]` and its packages' `Assumptions`, apply.) -/
def KitBootWp [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC netGF] (e : Expr) (h : GoString)
    (P : IProp netGF) : Prop :=
  ∀ hG : HeapGS .hasLC netGF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    P ⊢ ⌜(extLocalGS netExt (L := hG.goose_localGS)).host = h⌝ -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- A machine's obligation in `goose_dist_adequacy` (`nodeWp`) from `KitBootWp`. -/
theorem nodeWp_of_kitBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC netGF] (T : Nat)
    (e : Expr) (h : GoString) (σ : state) (P : IProp netGF) (hf : Fresh lctx σ)
    (hh : (extLocal netExt σ.world).host = h) (H : KitBootWp e h P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %_ %hL Hls Hgs -
  rw [hf.2.1]
  ihave Hl := net_localStart (L := L) σ.world $$ Hls
  iunfold lisStart at Hl
  icases Hl with ⟨%Hhost, -⟩
  imodintro
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) $$ HP [] Hgs
  ipureintro
  exact Hhost.trans hh

/-- **The bridge**: under the kit's deployment, an update from the extension's start resources
(every plan address unset) to a share `Ps i` for each machine `i`, and each machine's boot program
safe from its share on its host (`KitBootWp`), give the kit's statement, `Robust` with no
crashing machine, for any bound. -/
theorem robust_of_kitBoot [lctx : GoLocalContext] (plan : List (GoString × GoString))
    (hosts : List GoString) (nodes : List (Expr × state)) (g : GlobalState) (bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC netGF],
      ⊢ ⌜(NG (hlc := .hasLC) (GF := netGF)).plan = GMap.ofList plan⌝ -∗
        ([∗list] x ∈ plan, addrUnset x.1) ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (m : Expr × state) (h : GoString), nodes[i]? = some m →
            hosts[i]? = some h → KitBootWp m.1 h (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    KitDeploy plan hosts nodes g → Robust [] nodes g bound := by
  intro ⟨Hpl, Hplan, Hconns, Hlen, Hhosts⟩ hfresh n κs c hsteps _ i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have hkeys : keysDistinct plan = true := by
    unfold PlanWellFormed at Hpl
    simp only [Bool.and_eq_true] at Hpl
    exact Hpl.1
  have hhost : ∀ (j : Nat) (m : Expr × state), nodes[j]? = some m →
      ∃ h, hosts[j]? = some h ∧ (extLocal netExt m.2.world).host = h := by
    intro j m hm
    have hj : j < hosts.length := by rw [Hlen]; exact (List.getElem?_eq_some_iff.mp hm).1
    exact ⟨hosts[j], List.getElem?_eq_getElem hj,
      (Hhosts j _ m (List.getElem?_eq_getElem hj) hm).1⟩
  have H := goose_dist_adequacy (GF := netGF) (n + 1) (n + 2) nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c (distNsteps_of_crash_nil hsteps) (Nat.lt_succ_self n)
    (fun m hm => (hfresh m hm).2.2) (DistThreadsBelow.of_single ?_) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G _
    iintro Hg
    ihave Hnet := net_globalStart g.globalWorld $$ Hg
    icases netStart_plan _ _ $$ Hnet with %hplan
    rw [Hplan] at hplan
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) plan Hplan hkeys $$ Hnet
    imod Hstart $$ %hplan Hs with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    obtain ⟨h, hh, hmh⟩ := hhost j m hm
    exact nodeWp_of_kitBoot (n + 2) m.1 h m.2 (Ps j) (hfresh m (List.mem_of_getElem? hm)) hmh
      (HP j m h hm hh)
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    exact (hfresh x (List.mem_of_getElem? hx)).2.2

/-- `robust_of_kitBoot` with the library's ghost state made first (`netProto_alloc`): the
obligation gets the registry's names and every plan address unset, and sets their protocols
itself (`addrs_set_proto`). -/
theorem robust_of_kitProto [lctx : GoLocalContext] (plan : List (GoString × GoString))
    (hosts : List GoString) (nodes : List (Expr × state)) (g : GlobalState) (bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC netGF] [NetProtoGS],
      ⊢ regCtx -∗ ⌜(NG (hlc := .hasLC) (GF := netGF)).plan = GMap.ofList plan⌝ -∗
        ([∗list] x ∈ plan, addrUnset x.1)
        ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (m : Expr × state) (h : GoString), nodes[i]? = some m →
            hosts[i]? = some h → KitBootWp m.1 h (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    KitDeploy plan hosts nodes g → Robust [] nodes g bound := by
  refine robust_of_kitBoot plan hosts nodes g bound ?_
  intro G
  iintro %hplan Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π $$ Hreg %hplan Hs

end bridge

end Net
end Perennial
