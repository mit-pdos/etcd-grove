/-
# `etcd/dist/client`: the vocabulary of the kv dispatch's specs (N7-kv, M1)

M1 (`etcd_kv_safe_nocrash`, `notes/etcd-dist-plan.md` §11.3) is `etcd_safe_nocrash` at deployments whose
workloads are all `kv` (`KvOnly`). The dispatch of `examples/etcd/dist/client` (`Orchestrator`,
`MainDeployment`, `MainReady`, `RunKV`; `NodeDeployment`, `NodeMain`) then reaches only its kv arms, which
call `kvremote.Orch` (the orchestrator) and `kvremote.Node` (a client machine). Their specs (P9, §11.3 steps
3-4) are not written yet, so the dispatch is proved for **any** precondition of theirs:

* `OP nodes ops`: what `Orch(nodes, ops, timeout)` needs beyond its package and its address slice (the
  pending library's names, the budget units, the client machines' `remoteAddr`s, ...: step 5's share for
  the orchestrator);
* `NP c addr eps`: what `Node(c, addr, eps)` needs beyond its package and its endpoint slice (step 5's
  share for client machine `c`).

`orchShare OP d j` and `nodeShare NP d n` are those preconditions at the arguments the dispatch computes from
the deployment: the share a machine's boot hands its program (§11.3 step 6). `KvOnly` is M1's premise. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI

/-- **M1's premise**: every workload of the deployment is `kv` (`deployment.KV`, kind 0). -/
def KvOnly (d : Deployment) : Prop := ∀ w ∈ d.workloads, w.kind = W64 0

/-- Go's `client.Rotate(xs, i)` for `0 ≤ i`: `xs` from its `i`-th (mod length) element on. -/
def rotateL {α : Type} [Inhabited α] (xs : List α) (i : Nat) : List α :=
  (List.range xs.length).map (fun j => xs[(i + j) % xs.length]!)

theorem rotateL_length {α : Type} [Inhabited α] (xs : List α) (i : Nat) :
    (rotateL xs i).length = xs.length := by
  simp [rotateL]


theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, b, hb => by simp at hb
  | _, _, .cons h t, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨a, ha, h'⟩ := forall₂_mem_right t b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

/-- **A well-formed `kv`-only deployment's sizes**: at most `maxMembers` members, and every workload's
client count below `2 ^ 31` (its `BoundsOk`): what `NodeMain`'s `Rotate` needs. -/
theorem kvOnly_bounds {d : Deployment} (hw : d.WellFormed) (hkv : KvOnly d) :
    d.members.length ≤ 64 ∧ ∀ w ∈ d.workloads, 0 ≤ sint.Z w.clients ∧ sint.Z w.clients < 2 ^ 31 := by
  obtain ⟨t, he, hwf⟩ := hw
  obtain ⟨hm, -, -, hws, -⟩ := he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hb, -, -, -, hmax, -, -, -⟩ := hwf
  refine ⟨?_, ?_⟩
  · rw [← hm]; simpa [typed.maxMembers] using hmax
  · intro w hw
    obtain ⟨tw, htw, henc⟩ := forall₂_mem_right hws w hw
    have hk := hkv w hw
    have hbw := hb tw htw
    cases tw with
    | kv c o =>
      obtain ⟨-, hc, -⟩ := henc
      simp only [typed.Workload.BoundsOk] at hbw
      omega
    | _ => simp [typed.Workload.Encodes, hk] at henc

/-- A well-formed deployment has one list of client machines per workload. -/
theorem wellFormed_nodes_length {d : Deployment} (hw : d.WellFormed) :
    d.nodes.length = d.workloads.length := by
  obtain ⟨t, he, hwf⟩ := hw
  obtain ⟨-, -, -, hws, hn⟩ := he
  obtain ⟨-, -, -, -, -, hl, -⟩ := hwf
  rw [← hn, hl]
  exact hws.length_eq

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A function value `f` of Go type `func()` that can be called any number of times, returning (the
`ready` observer of `client.MainReady`). -/
def readySpec (f : GoFunc) : IProp GF :=
  iprop({{ True }} (App (Val #f) (Val #())) {{ RET #(); True }})

instance readySpec_persistent (f : GoFunc) : Persistent (readySpec (GF := GF) f) := by
  unfold readySpec; infer_instance

/-- **The orchestrator machine `j`'s share**: `OP` at workload `j`'s client machines' addresses and its
operation count, when the deployment has a workload `j` (otherwise the program returns at once). -/
def orchShare (OP : List GoString → w64 → IProp GF) (d : Deployment) (j : w64) : IProp GF :=
  if 0 ≤ sint.Z j then
    match d.workloads[sint.nat j]?, d.nodes[sint.nat j]? with
    | some w, some ns => OP ns w.ops
    | _, _ => iprop(True)
  else iprop(True)

/-- **The `n`-th client machine's share**: `NP` at its index `c` in its workload, its address, and the
members' client addresses rotated by `c` (the endpoints its client prefers), when the deployment has an
`n`-th client machine (otherwise the program returns at once). -/
def nodeShare (NP : w64 → GoString → List GoString → IProp GF) (d : Deployment) (n : w64) : IProp GF :=
  if 0 ≤ sint.Z n then
    match d.nodeList[sint.nat n]? with
    | some (_, c, a) => NP (W64 c) a (rotateL (d.members.map Member.client) c)
    | none => iprop(True)
  else iprop(True)

end defs

end etcd_dist
end EtcdGrove
end Perennial
