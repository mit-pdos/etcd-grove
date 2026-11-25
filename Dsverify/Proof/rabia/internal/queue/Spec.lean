/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/queue/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/internal/queue`'s specs used by other packages (interface, stage 1a): a `PQueue` (a
priority queue of consensus objects, a heap by `ProxySeqIdLessThan`) through `container/heap`
(`Init`, `Push`, `Pop`, called by the consensus package with `&c.Queue`), as a multiset: `Push`
adds an object, `Pop` removes one (the least, which safety does not need: the spec says some
element). The heap functions are Go's own code (`Harness/Code/container/heap.lean`); their
proofs over `PQueue`'s methods are this package's.
-/
module

public import Dsverify.GeneratedProof.rabia.internal.queue
public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Proof.container.heap.Init
public import Dsverify.Proof.rabia.internal.queue.Base



@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.queue

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `PQueue` at `q` holds the objects `xs` (in its slice's order; read-only slices). -/
def pqOwn (q : Loc) (xs : List ObjV) : IProp GF :=
  iprop(∃ (sl : GoSlice) (vs : List ConsensusObj), q ↦ sl ∗ sl ↦* vs ∗ ownSliceCap ConsensusObj sl (DFrac.own 1) ∗
    ⌜vs.length = xs.length⌝ ∗ [∗list] i ↦ v ∈ vs, ∃ o, ⌜xs[i]? = some o⌝ ∗ objRep v o)

/-- The `heap.Interface` value of `&q`. -/
def pqIface (q : Loc) : GoInterface := interface.mkOk (go.GoType.PointerType PQueue.ty) #q

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.queue.Assumptions]

/-- `heap.Init(&q)`: a permutation. -/
abbrev heapInit.spec : Prop :=
  ∀ (q : Loc) (xs : List ObjV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue ∗ pqOwn q xs }}
    (App (Val (@! container.heap.Init)) (Val #(pqIface q)))
  {{ RET #(); ∃ xs', ⌜xs'.Perm xs⌝ ∗ pqOwn q xs' }}

/-- `heap.Push(&q, obj)`: the object added. -/
abbrev heapPush.spec : Prop :=
  ∀ (q : Loc) (xs : List ObjV) (v : ConsensusObj) (o : ObjV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue ∗ pqOwn q xs ∗ objRep v o }}
    (App (App (Val (@! container.heap.Push)) (Val #(pqIface q)))
      (Val #(interface.mkOk ConsensusObj.ty #v)))
  {{ RET #(); ∃ xs', ⌜xs'.Perm (o :: xs)⌝ ∗ pqOwn q xs' }}

/-- `heap.Pop(&q)` of a nonempty queue: one of its objects, removed. -/
abbrev heapPop.spec : Prop :=
  ∀ (q : Loc) (xs : List ObjV),
  xs ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue ∗ pqOwn q xs }}
    (App (Val (@! container.heap.Pop)) (Val #(pqIface q)))
  {{ (v : ConsensusObj), RET #(interface.mkOk ConsensusObj.ty #v);
      ∃ o xs', ⌜(o :: xs').Perm xs⌝ ∗ objRep v o ∗ pqOwn q xs' }}

/-- `q.Len()` (read through `c.Queue.Len()` by `QPop`). -/
abbrev PQueue.Len.spec : Prop :=
  ∀ (q : Loc) (xs : List ObjV) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.queue ∗ pqOwn q xs }}
    (App (Val (q @!! go.GoType.PointerType PQueue.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 xs.length); pqOwn q xs }}

end spec

end Perennial.rabia.internal.queue
