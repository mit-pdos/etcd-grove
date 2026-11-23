/-
# remote: the deployment's statement (`notes/remote-port-plan.md`, §6, R3)

A deployment of `remote` is machines that never crash (the orchestrator, the client nodes, the
servers), each serving or calling at addresses `addrs`, every one of which serves `remote`'s calls
(`remoteAddr`: its protocols are `reqP`/`repP` of one far-side store `R`). Its statement is a
distributed deployment's (`Robust []`, under `DistDeploy`: `Net/Statement/DistBridge.lean`), proved by
`robust_of_distProto`:

- `remote_start`: from the protocol library's registry and the addresses unset, the slot map
  (`mapCtx`, `mapCtx_alloc`), the call budgets (`N` for each of the distinct addresses `baddrs`, the
  client nodes', with their units; none for the others) and, for any service `S` chosen later (a store `R.svc`, once the
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

/-- **The deployment's start**: the slot map, the call budgets (`N` for each of `baddrs`, with
their units), and the addresses' protocols for a service chosen later. -/
theorem remote_start {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]
    (addrs baddrs : List GoString) (N : Nat) (hnd : baddrs.Nodup) :
    ⊢ regCtx (Gg := G) -∗ ([∗list] a ∈ addrs, addrUnset (Gg := G) a) ={⊤}=∗
      ∃ ρ : RemoteGS, ⌜∀ a, ρ.bud a = if a ∈ baddrs then some N else none⌝ ∗
        mapCtx (Gg := G) (ρ := ρ) (I := I) ∗
        ([∗list] a ∈ baddrs, budUnits (Gg := G) (ρ := ρ) a N) ∗
        ∀ S : RSvc GF I O, |={⊤}=> [∗list] a ∈ addrs, svcAddr (Gg := G) S a := by
  iintro #Hreg Hs
  imod mapCtx_alloc (Gg := G) (I := I) ⊤ baddrs N hnd with ⟨%ρ, %Hb, #Hm, Hu⟩
  imodintro
  iexists ρ
  iframe Hm Hu
  isplitr
  · ipureintro; exact Hb
  iintro %S
  unfold svcAddr
  iapply addrs_set_proto (Gg := G) ⊤ (fun a => reqP (Gg := G) S a) (fun _ => repP (Gg := G) S) addrs
    $$ Hreg Hs

end start

section robust
variable [GoGlobalContext] [lctx : GoLocalContext]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- **remote's deployments are robust** (see the file header): from the instance's update, for the
slot map and the addresses' protocols set for a store of its choice, to a share per machine from
which the machine's boot program is safe, `Robust []` under the deployment. -/
theorem remote_robust (addrs : List GoString) (nodes : List (Expr × state)) (g : GlobalState)
    (threads bound : Nat) (baddrs : List GoString) (N : Nat) (hnd : baddrs.Nodup)
    (Hstart : ∀ [G : GooseGlobalGS .hasLC netGF] [π : NetProtoGS] [ρ : RemoteGS],
      (∀ a, ρ.bud a = if a ∈ baddrs then some N else none) →
      ⊢ regCtx (Gg := G) -∗ mapCtx (Gg := G) (I := I) -∗
        ([∗list] a ∈ baddrs, budUnits (Gg := G) a N) -∗
        (∀ R : RBase netGF St I O, |={⊤}=> [∗list] a ∈ addrs, remoteAddr (Gg := G) R a) ={⊤}=∗
        ∃ Ps : Nat → IProp netGF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWp m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distProto addrs nodes g threads bound ?_
  intro G π
  iintro #Hreg Hs
  imod remote_start (GF := netGF) (I := I) (O := O) addrs baddrs N hnd $$ Hreg Hs
    with ⟨%ρ, %Hb, #Hm, Hu, Hset⟩
  iapply @Hstart G π ρ Hb $$ Hreg Hm Hu [Hset]
  iintro %R
  iapply Hset

/-- `remote_robust` over any ghost bundle `GF`, the obligation given the receipt bound
(`robust_of_distProtoRB`): what an instance whose machines need porcupine's non-atomic invariants or
lintest's clock uses (the counter, R4). -/
theorem remote_robustRB {GF : BundledGFunctors} [GooseGpreS GF] (addrs : List GoString)
    (nodes : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (baddrs : List GoString) (N : Nat) (hnd : baddrs.Nodup)
    (Hstart : ∀ [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS] [ρ : RemoteGS],
      receiptBound GF ≤ bound → (∀ a, ρ.bud a = if a ∈ baddrs then some N else none) →
      ⊢ regCtx (Gg := G) -∗ mapCtx (Gg := G) (I := I) -∗
        ([∗list] a ∈ baddrs, budUnits (Gg := G) a N) -∗
        (∀ R : RBase GF St I O, |={⊤}=> [∗list] a ∈ addrs, remoteAddr (Gg := G) R a) ={⊤}=∗
        ∃ Ps : Nat → IProp GF,
          ⌜∀ (i : Nat) (m : Expr × state), nodes[i]? = some m → DistBootWpG m.1 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ nodes, Ps i) :
    DistDeploy addrs nodes g → Robust [] nodes g threads bound := by
  refine robust_of_distProtoRB (GF := GF) addrs nodes g threads bound ?_
  intro G π hb
  iintro #Hreg Hs
  imod remote_start (GF := GF) (I := I) (O := O) addrs baddrs N hnd $$ Hreg Hs
    with ⟨%ρ, %Hbud, #Hm, Hu, Hset⟩
  iapply @Hstart G π ρ hb Hbud $$ Hreg Hm Hu [Hset]
  iintro %R
  iapply Hset

end robust

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
