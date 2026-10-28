/-
**S1's invariant, in Iris** (phase 5 of `notes/k8s-daemonset-plan.md`, first round). Lean-first.

For the DaemonSet `d` (its owner key `d.o`, UID `d.u`), the invariant `s1Inv` owns the API
state's clients' half (`apiState`: every client's logically atomic operation opens it; reads
change nothing), the consistency store's abstract state (`consState`), and the bookkeeping of
the pure invariant (`s1Ok`, `S1Steps.lean`):
* `L`, a version the pod informer's store has reached for good (`infRvLb`, persistent);
* the **pending creates** (`P : GMap (Key × Nat) (Nat × GoString)`, a ghost map `γ.pend`): a pod
  of `d.u` (key and version) the sync holding the owner's token created and has not accounted for
  yet, with the index of the create goroutine that made it and its node; the goroutine's
  **permit** (`permit γ i`, an exclusive token) the entry holds;
* the **claimed nodes** (`C : GMap GoString Nat`, `γ.claim`): a node the sync found with no pod
  of `d.u` (in a pod cache covering the API state, `acct`) and will create one on, by the
  goroutine `i`: every pod of `d.u` there is that goroutine's pending one (`claimsOk`).

So a create for a claimed node keeps S1 and leaves its pod pending (`create_step`), and the
goroutine gets its permit back only when the pod is accounted for, by `WroteAt` (`wrote_step`). A sync's worker hands out the permits (it owns their ghost
map's authority, `permitAuth`, with its token) and gets them back from the goroutines at
`createWait.Wait()`: with every permit back no create is pending (`pend_empty`).

**The ambiguous create**: a create that commits and returns the timeout leaves its pod pending,
its permit in the invariant: the goroutine cannot return it (`syncNodes`' proof, the create
goroutine's ambiguous branch; `ambiguous_create_breaks_S1` shows no proof can: the next sync
duplicates the pod).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Steps
public import Proof.k8s_io.client_go.tools.cache.InformerInv
public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer consistency

/-! ## The ghost state and the invariant -/

/-- The ghost names of S1's invariant. -/
structure S1Names where
  api : ApiNames
  cons : ConsNames
  podInf : InfNames
  /-- the pending creates: (pod key, version) ↦ (permit index, node) -/
  pend : GName
  /-- the claimed nodes: node name ↦ permit index -/
  claim : GName
  /-- the create goroutines' permits -/
  permit : GName
  /-- the per-owner sync tokens (the consistency store's permissions `T`) -/
  tok : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The sync token of owner `o`** at fraction `q` (the consistency store's `T`): the work
queue's per-key token, traded at the sync's start (`processNextWorkItem`). -/
def syncTok (γ : S1Names) (o : Owner) (q : Qp) : IProp GF := ghostMapElem γ.tok o (DFrac.own q) ()

/-- **A create goroutine's permit** `i`. -/
def permit (γ : S1Names) (i : Nat) : IProp GF := ghostMapElem γ.permit i (DFrac.own 1) ()

/-- **The permits' authority** (the syncing worker's): the permits handed out are `R`'s. -/
def permitAuth (γ : S1Names) (R : GMap Nat Unit) : IProp GF := ghostMapAuth γ.permit 1 R

/-- **A pending create** (the goroutine `i`'s pod at key `k` and version `c`, on node `n`): its
receipt. -/
def pendTok (γ : S1Names) (k : Key) (c : Nat) (i : Nat) (n : GoString) : IProp GF :=
  ghostMapElem γ.pend (k, c) (DFrac.own 1) (i, n)

/-- **A claimed node** `n`, by the goroutine `i`. -/
def claimTok (γ : S1Names) (n : GoString) (i : Nat) : IProp GF :=
  ghostMapElem γ.claim n (DFrac.own 1) i

/-- **S1's invariant's content.** -/
def s1Res (γ : S1Names) (d : DsId) : IProp GF :=
  iprop(∃ (σ : St) (M : GMap Owner consistency.Rec) (L : Nat)
      (P : GMap (Key × Nat) (Nat × GoString)) (C : GMap GoString Nat),
    apiState γ.api σ ∗ consState γ.cons M ∗ infRvLb γ.podInf L ∗
    ghostMapAuth γ.pend 1 P ∗ ([∗map] _k ↦ v ∈ P, permit γ v.1) ∗
    ghostMapAuth γ.claim 1 C ∗
    ⌜s1Ok d σ M L P C⌝)

/-- The invariant's namespace. -/
def s1N : Namespace := nroot.@"daemonset_s1"

/-- **S1's invariant.** -/
def s1Inv (γ : S1Names) (d : DsId) : IProp GF := inv s1N (s1Res γ d)

instance s1Inv_persistent (γ : S1Names) (d : DsId) : Persistent (s1Inv (GF := GF) γ d) := by
  unfold s1Inv; infer_instance

/-- The sync tokens exclude each other (the consistency store's `tokExcl`). -/
theorem syncTok_excl (γ : S1Names) : ⊢ tokExcl (GF := GF) (syncTok γ) := by
  unfold tokExcl syncTok
  iintro !> %o %q H1 H2
  ihave %Hv := ghostMapElem_valid_2 (K := Owner) (V := Unit) o γ.tok (DFrac.own 1) (DFrac.own q)
    () () $$ H1 H2
  exfalso
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

end defs

end dsctl
end EtcdGrove
end Perennial
