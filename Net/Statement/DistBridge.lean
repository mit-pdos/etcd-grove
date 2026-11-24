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

Since 2026-11-23 each theorem here is `DistBridgeExts.lean`'s `robust_of_distBootE` (over any list of
extensions with the net extension) at `netExts`.

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
public import Net.Statement.DistBridgeExts
public import Robustness.Statement

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

attribute [local instance] GooseGlobalGS.gooseInvGS

section bridge
variable [GoGlobalContext]

/-- A machine's boot program `e` is safe from `P`: under every ghost state `hG` over the
global one `G` whose Go context is `lctx` (the statement's, `Robust`'s `Fresh`), from no package
initialized, it returns `#()` (a Go `main`'s result) and is not stuck. (A proof destructs `hG` and substitutes the context, so that the program's instances over
`lctx`, `[go.Semantics]` and its packages' `Assumptions`, apply.) -/
def DistBootWp [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC netGF] (e : Expr)
    (P : IProp netGF) : Prop :=
  DistBootWpE e P

/-- A machine's obligation in `goose_dist_adequacy` (`nodeWp`) from `DistBootWp`. -/
theorem nodeWp_of_distBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC netGF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp netGF) (hf : Fresh lctx σ) (H : DistBootWp e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) :=
  nodeWp_of_distBootE T e σ P hf H

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
    DistDeploy addrs nodes g → Robust [] nodes g threads bound :=
  robust_of_distBootE (GF := netGF) ⟨net_init_compat, trivial⟩ addrs nodes g threads bound
    (fun _ => Hstart)

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
  DistBootWpE e P

theorem nodeWp_of_distBootG [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF] (T : Nat)
    (e : Expr) (σ : state) (P : IProp GF) (hf : Fresh lctx σ) (H : DistBootWpG e P) :
    P ⊢ nodeWp T e σ (fun v => v = #()) :=
  nodeWp_of_distBootE T e σ P hf H

/-- `robust_of_distBoot` over the bundle `GF`, the obligation given `receiptBound GF ≤ bound`. -/
theorem robust_of_distBootRB [lctx : GoLocalContext] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound :=
  robust_of_distBootE (GF := GF) ⟨net_init_compat, trivial⟩ addrs nodes g threads bound Hstart

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
