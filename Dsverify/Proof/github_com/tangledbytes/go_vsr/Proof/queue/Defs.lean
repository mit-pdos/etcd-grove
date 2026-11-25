/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/queue/Defs.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The representation of a `*Queue[T]` (the body of the sealed `queue.isQueue`): a mutex whose
invariant owns the head, tail and len fields and the linked list of nodes, each node's value
`v` with its resource `P v`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.queue.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : queue.Assumptions]

/-- The first node of `ns`, or `nxt` if `ns` is empty. -/
def queue.headOf {V : Type} (ns : List (Loc × V)) (nxt : Loc) : Loc :=
  match ns with
  | [] => nxt
  | n :: _ => n.1

/-- The last node of `ns`, or `null`. -/
def queue.lastOf {V : Type} (ns : List (Loc × V)) : Loc :=
  match ns.getLast? with
  | none => null
  | some n => n.1

/-- The nodes `ns` (location, value), linked in order, the last one's `next` being `nxt`; each
value with its resource. -/
def queue.nodesOwn {V : Type} [TypedPointsto (GF := GF) V] (P : V → IProp GF) :
    List (Loc × V) → Loc → IProp GF
  | [], _ => iprop(True)
  | n :: ns, nxt => iprop(n.1 ↦ (queue.node.mk n.2 (queue.headOf ns nxt) : queue.node V) ∗
      P n.2 ∗ queue.nodesOwn P ns nxt)

/-- The lock invariant: the fields, and the list of nodes from `head` to `tail`. -/
def queue.lockInv {V : Type} [TypedPointsto (GF := GF) V] (q : Loc)
    (P : V → IProp GF) : IProp GF :=
  iprop(∃ (ns : List (Loc × V)) (n : w64),
    "head" ∷ q.[queue.Queue V, go!"head"] ↦ queue.headOf ns null ∗
    "tail" ∷ q.[queue.Queue V, go!"tail"] ↦ queue.lastOf ns ∗
    "len" ∷ q.[queue.Queue V, go!"len"] ↦ n ∗
    "Hns" ∷ queue.nodesOwn P ns null ∗
    "%Hnn" ∷ ⌜∀ x ∈ ns, x.1 ≠ null⌝)

def queue.isQueueDef {V : Type} [TypedPointsto (GF := GF) V] (q : Loc)
    (P : V → IProp GF) : IProp GF :=
  iprop(∃ mu : Loc,
    "#Hmu" ∷ q.[queue.Queue V, go!"mu"] ↦□ mu ∗
    "#Hlock" ∷ sync.isMutex mu (queue.lockInv q P))

instance queue.isQueueDef_persistent {V : Type} [TypedPointsto (GF := GF) V] (q : Loc)
    (P : V → IProp GF) : Persistent (queue.isQueueDef q P) := by
  unfold queue.isQueueDef; simp only [named]; infer_instance

end defs

end Perennial.github_com.tangledbytes.go_vsr.pkg
