/-
**From a distributed deployment's boot WPs to its robustness statement** (proved; `notes/dsverify-net-port-plan.md`,
phase 4): the deployment's machines never crash, so its statement is `Robust [] nodes g threads bound`
(`Robustness/Statement.lean`) under its start (`DistDeploy`, `DistDeploy.lean`), and this
file proves it from one WP per machine.

- With no crashing machine, the executions `Robust` quantifies over are plain distributed
  executions (`distNsteps_of_crash_nil`: `DistCrashNsteps []` has no crash step), so Perennial's
  adequacy theorem without crashes (`goose_dist_adequacy`, instantiated with the ghost state `netGF`
  and the extensions `netExts`, `GooseLang/Ext/Net/Adequacy.lean`) proves it. This covers the case
  where **every** machine is stable; a deployment with crashing and stable machines both (kvnet's)
  needs an adequacy theorem with boot programs for some nodes only (`notes/robustness.md`, "Next").
- `robust_of_distBoot`: an update from the extension's start resources for the deployment's
  addresses (each address unset, `addrUnset`, the net protocol library `GooseLang/Ext/Net/Proto.lean`) to a
  share `Ps i` for each machine `i`, and each machine's boot program safe from its share
  (`DistBootWp`), give the deployment's statement. A program that keeps the network's resources in its own
  protocol rather than the library's gets them back from `addrUnset` (`netPend`).
- `robust_of_distProto`: the same with the library's ghost state made first (`netProto_alloc`).

`DistBootWp`'s WP is under any ghost state whose Go context is the statement's `lctx` (`Robust`'s
`Fresh`), so the program's `[go.Semantics]` and its packages' `Assumptions`, instances over `lctx`,
apply to it once the context is substituted.
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.Golang.Defn
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Proto
public import Net.Statement.DistDeploy
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

/-- A machine's boot program `e` is safe from `P`: under every ghost state `hG` over the
global one `G` whose Go context is `lctx` (the statement's, `Robust`'s `Fresh`), from no package
initialized, it returns `#()` (a Go `main`'s result) and is not stuck. (A proof destructs `hG` and substitutes the context, so that the program's instances over
`lctx`, `[go.Semantics]` and its packages' `Assumptions`, apply.) -/
def DistBootWp [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC netGF] (e : Expr)
    (P : IProp netGF) : Prop :=
  ∀ hG : HeapGS .hasLC netGF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- A machine's obligation in `goose_dist_adequacy` (`nodeWp`) from `DistBootWp`. -/
theorem nodeWp_of_distBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC netGF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp netGF) (hf : Fresh lctx σ) (H : DistBootWp e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %_ %hL Hls Hgs -
  rw [hf.2.1]
  imodintro
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) $$ HP Hgs

/-- **The bridge**: under the deployment's start, an update from the extension's start resources
(every address of the deployment unset) to a share `Ps i` for each machine `i`, and each machine's boot
program safe from its share (`DistBootWp`), give the deployment's statement, `Robust` with no crashing
machine, for any thread bound and step bound. -/
theorem robust_of_distBoot [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC netGF],
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWp m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh _ _ n κs c hsteps _ i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy (GF := netGF) (n + 1) (n + 2) nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c (distNsteps_of_crash_nil hsteps.nsteps) (Nat.lt_succ_self n)
    (fun m hm => (hfresh m hm).2.2) (DistThreadsBelow.of_single ?_) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G _
    iintro Hg
    ihave Hnet := net_globalStart g.globalWorld $$ Hg
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod Hstart $$ Hs with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBoot (n + 2) m.1 m.2 (Ps j) (hfresh m (List.mem_of_getElem? hm))
      (HP j m hm)
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    exact (hfresh x (List.mem_of_getElem? hx)).2.2

/-- `robust_of_distBoot` with the library's ghost state made first (`netProto_alloc`): the
obligation gets the registry's names and every address of the deployment unset, and sets their protocols
itself (`addrs_set_proto`). -/
theorem robust_of_distProto [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC netGF] [NetProtoGS],
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWp m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distBoot addrs nodes g threads bound ?_
  intro G
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π $$ Hreg Hs

end bridge


/-! ## Over any ghost-state bundle, with the receipt bound (additive, 2026-11-22)

The bridge above is at `netGF`. A deployment whose proofs need ghost state `netGF` has no slot for (porcupine's
non-atomic invariants: `remote`'s counter, `notes/remote-port-plan.md`, R4) states its machines' WPs
over its own bundle `GF` (any with `GooseGpreS GF`); and a WP that needs the time receipts' bound
(lintest's clock: `receiptBound GF ≤ 2^63`) gets it from the step bound: `goose_dist_adequacy`'s
obligation has `receiptBound GF = n + 1` for an execution of `n < bound` steps. -/

section bridgeGF
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- `DistBootWp` over the bundle `GF`. -/
def DistBootWpG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (e : Expr)
    (P : IProp GF) : Prop :=
  ∀ hG : HeapGS .hasLC GF, hG.goose_globalGS = G →
    hG.goose_localGS.goose_go_local_context = lctx →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

theorem nodeWp_of_distBootG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ) (H : DistBootWpG e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  unfold nodeWpBody
  iintro %_ %hL Hls Hgs -
  rw [hf.2.1]
  imodintro
  iapply H ⟨G, L⟩ rfl (hL.trans hf.1) $$ HP Hgs

/-- `robust_of_distBoot` over the bundle `GF`, the obligation given `receiptBound GF ≤ bound`. -/
theorem robust_of_distBootRB [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  rintro ⟨Hnd, Hok, Hconns, -⟩ hfresh _ _ n κs c hsteps hn i tp σ hi e he
  simp only [List.map_nil, List.nil_append] at hfresh hsteps
  have H := goose_dist_adequacy (GF := GF) (n + 1) (n + 2) nodes g (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm) ⟨Hconns, trivial⟩ (fun _ _ => ⟨trivial, trivial⟩)
    ?_ n κs c (distNsteps_of_crash_nil hsteps.nsteps) (Nat.lt_succ_self n)
    (fun m hm => (hfresh m hm).2.2) (DistThreadsBelow.of_single ?_) i tp σ hi
  · exact ⟨H.2.1 e he, H.2.2 e he⟩
  · intro G HN
    iintro Hg
    ihave Hnet := net_globalStart g.globalWorld $$ Hg
    ihave Hs := addrs_start (Gg := G) (extGlobal netExt g.globalWorld) addrs Hnd Hok $$ Hnet
    imod Hstart (by omega) $$ Hs with ⟨%Ps, %HP, HPs⟩
    imodintro
    iapply BigSepL.bigSepL_mono ?_ $$ HPs
    intro j m hm
    exact nodeWp_of_distBootG (n + 2) m.1 m.2 (Ps j) (hfresh m (List.mem_of_getElem? hm))
      (HP j m hm)
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    exact (hfresh x (List.mem_of_getElem? hx)).2.2

/-- `robust_of_distProto` over the bundle `GF`, the obligation given `receiptBound GF ≤ bound`. -/
theorem robust_of_distProtoRB [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF] [NetProtoGS], receiptBound GF ≤ bound →
      ⊢ regCtx -∗ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distBootRB (GF := GF) addrs nodes g threads bound ?_
  intro G hb
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  iapply @Hstart G π hb $$ Hreg Hs

end bridgeGF

end Net
end Perennial
