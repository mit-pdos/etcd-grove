/-
# remote: the deployment's statement (`notes/remote-port-plan.md`, §6, R3)

A deployment of `remote` is machines that never crash (the orchestrator, the client nodes, the
servers), each serving or calling at addresses `addrs`, every one of which serves `remote`'s calls
(`remoteAddr`: its protocols are `reqP`/`repP` of one far-side store `R`). Its statement is a
distributed deployment's (`Robust []`, under `DistDeploy`: `Net/Statement/DistBridge.lean`), proved by
`robust_of_distProto`:

- `remote_start`: from the protocol library's registry and the addresses unset, the slot map
  (`mapCtx`, `mapCtx_alloc`) and, for any service `S` chosen later (a store `R.svc`, once the
  instance has made the ghost state its `R.sysState` names; or a report), every address's protocols
  (`addrs_set_proto`, `svcAddr`).
- `remote_robust`: for a store `R` (the counter's statement); the instance's obligation is an update from those to a share per machine, each
  machine's boot program safe from its share (`DistBootWp`); the machines' WPs are the instance's,
  from `Check.spec`, `ServeClient.spec` and `Serve.spec`.
-/
module

public import Net.Statement.DistBridge
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section start
variable [GoGlobalContext]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- **The deployment's start**: the slot map, and the addresses' protocols for a service chosen
later. -/
theorem remote_start {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]
    (addrs : List GoString) :
    ⊢ regCtx (Gg := G) -∗ ([∗list] a ∈ addrs, addrUnset (Gg := G) a) ={⊤}=∗
      ∃ ρ : RemoteGS, mapCtx (Gg := G) (ρ := ρ) (I := I) ∗
        ∀ S : RSvc GF I O, |={⊤}=> [∗list] a ∈ addrs, svcAddr (Gg := G) S a := by
  iintro #Hreg Hs
  imod mapCtx_alloc (Gg := G) (I := I) ⊤ with ⟨%ρ, #Hm⟩
  imodintro
  iexists ρ
  iframe Hm
  iintro %S
  unfold svcAddr
  iapply addrs_set_proto (Gg := G) ⊤ (fun _ => reqP (Gg := G) S) (fun _ => repP (Gg := G) S) addrs
    $$ Hreg Hs

end start

section robust
variable [GoGlobalContext] [lctx : GoLocalContext]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- **remote's deployments are robust** (see the file header): from the instance's update, for the
slot map and the addresses' protocols set for a store of its choice, to a share per machine from
which the machine's boot program is safe, `Robust []` under the deployment. -/
theorem remote_robust (addrs : List GoString) (nodes : List (Expr × state)) (g : GlobalState)
    (threads bound : Nat)
    (Hstart : ∀ [G : GooseGlobalGS .hasLC netGF] [π : NetProtoGS] [ρ : RemoteGS],
      ⊢ regCtx (Gg := G) -∗ mapCtx (Gg := G) (I := I) -∗
        (∀ R : RBase netGF St I O, |={⊤}=> [∗list] a ∈ addrs, remoteAddr (Gg := G) R a) ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWp m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distProto addrs nodes g threads bound ?_
  intro G π
  iintro #Hreg Hs
  imod remote_start (GF := netGF) (I := I) (O := O) addrs $$ Hreg Hs with ⟨%ρ, #Hm, Hset⟩
  iapply @Hstart G π ρ $$ Hreg Hm [Hset]
  iintro %R
  iapply Hset

/-- `remote_robust` over any ghost bundle `GF`, the obligation given the receipt bound
(`robust_of_distProtoRB`): what an instance whose machines need porcupine's non-atomic invariants or
lintest's clock uses (the counter, R4). -/
theorem remote_robustRB {GF : BundledGFunctors} [GooseGpreS GF] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hstart : ∀ [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS] [ρ : RemoteGS],
      receiptBound GF ≤ bound →
      ⊢ regCtx (Gg := G) -∗ mapCtx (Gg := G) (I := I) -∗
        (∀ R : RBase GF St I O, |={⊤}=> [∗list] a ∈ addrs, remoteAddr (Gg := G) R a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distProtoRB (GF := GF) addrs nodes g threads bound ?_
  intro G π hb
  iintro #Hreg Hs
  imod remote_start (GF := GF) (I := I) (O := O) addrs $$ Hreg Hs with ⟨%ρ, #Hm, Hset⟩
  iapply @Hstart G π ρ hb $$ Hreg Hm [Hset]
  iintro %R
  iapply Hset

end robust

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
