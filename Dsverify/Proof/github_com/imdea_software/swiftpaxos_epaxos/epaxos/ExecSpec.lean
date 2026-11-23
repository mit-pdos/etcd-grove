/-
The executor's internal specs (exec.go): the resources of a scan pass (`exCtx`, persistent;
`exHeap`, the replica's instances with the search state, the executed-up-to row, the store, the
Tarjan stack, the ghost fragments), and the specs of `strongconnect`, `findSCC`,
`executeCommand` against the pure Tarjan invariant (`Tarjan.lean`) and the model's executor
steps (`execSCC`/`execCmd`/`instDone`, taken inside, at the pop of each component).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecRep

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof tarjan

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The Tarjan stack `e.stack` holding the instances `S` (pointer lists `F`), capacity positive. -/
def stackOwn (e : Loc) (F : Nat → List Loc) (S : List InstId) : IProp GF :=
  iprop(∃ s : GoSlice, structFieldRef epaxos.Exec go!"stack" e ↦ s ∗ s ↦* S.map (ptrOf F) ∗
    ownSliceCap Loc s (DFrac.own 1) ∗ ⌜0 < sint.Z s.cap⌝)

/-- What a scan pass reads and never writes (persistent). -/
def exCtx (γ : EpNames) (i : Nat) (r e rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : IProp GF :=
  iprop(pkgInit_epaxos ∗ pkgInit_replica ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state ∗
    isPkgInit (PROP := IProp GF) pkg_id.sort ∗
    efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ isReplicaFw γ rr i L p Rext ∗
    efld r go!"transconf" ↦□ false ∗ efld r go!"exec" ↦□ e ∗
    structFieldRef epaxos.Exec go!"r" e ↦□ r ∗ inv protoN (epInv γ))

instance exCtx_persistent (γ : EpNames) (i : Nat) (r e rr : Loc) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) : Persistent (exCtx γ i r e rr L p Rext) := by
  unfold exCtx; infer_instance

/-- The executor's state during a search: instances (with the search's `Index`/`Lowlink`), the
executed-up-to row, the store, the stack, the counter `*index`, the ghost fragment (idle). -/
def exHeap (γ : EpNames) (i : Nat) (r e : Loc) (F : Nat → List Loc) (σ : RState)
    (t : St InstId) (idxp : Loc) : IProp GF :=
  iprop(repInstsX γ i r F σ.inst t.ix ∗ repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗
    repStore r σ.store ∗ stackOwn e F t.S ∗ idxp ↦ W64 t.n ∗
    repFrag γ i σ ∗ pendFrag γ i none ∗ curFrag γ i [] 0)

/-- The visited instances are a duplicate-free list of slots of the rows, counted by `*index`
(so `*index` never overflows). -/
def VisCount (t : St InstId) : Prop :=
  ∃ V : List InstId, V.Nodup ∧ (∀ x, t.vis x ↔ x ∈ V) ∧ t.n = V.length + 1 ∧
    ∀ x ∈ V, x.q < nR ∧ x.i < MAX_INSTANCE

/-- The pure facts a search keeps. -/
structure SearchOk (i : Nat) (σ : RState) (t : St InstId) : Prop where
  wf : ExecWf σ
  ib : instBounds σ.inst
  hi : i < nR
  inv : TInv (gr σ) t
  cnt : VisCount t

/-- The callee's result on `true` (`n0` the counter at the call, `A` the caller's active
calls): `v` popped and executed (`low v = num v`), or left on the stack finished. -/
def scTrue (σ' : RState) (t' : St InstId) (A : List InstId) (v : InstId) (n0 : Nat) : Prop :=
  ∃ lv, t'.ix v = some (n0, lv) ∧
    ((σ'.executed v ∧ lv = n0 ∧ t'.A = A) ∨
     (v ∈ t'.S ∧ lv < n0 ∧ t'.A = A ++ [v] ∧ DoneAll (gr σ') t' v ∧
       t'.par v = A.getLast?.getD v))

/-- **`strongconnect(v, index)`** (exec.go): from a search state satisfying Tarjan's invariant,
`v` unvisited and committed, its caller the innermost active call (with an edge to `v`); on
`true`, the invariant again, extended (`Ext`), the state reached by executing the popped
components (`ExRel`, the model's executor steps taken), and `v` popped or finished
(`scTrue`); on `false`, every visited non-executed instance on the stack (`WInv`, for
`findSCC`'s reset). -/
def StrongconnectSpec (γ : EpNames) (i : Nat) (r e rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : Prop :=
  ∀ (F : Nat → List Loc) (σ : RState) (t : St InstId) (v : InstId) (idxp : Loc) (wv : InstRec),
    SearchOk i σ t → ¬ t.vis v → σ.inst v = some wv → wv.status = stCOMMITTED →
    (t.A = [] → t.S = []) → (∀ a, t.A.getLast? = some a → σ.depEdge a v) →
  {{ exCtx γ i r e rr L p Rext ∗ exHeap γ i r e F σ t idxp }}
    (App (App (Val (e @!! go.GoType.PointerType epaxos.Exec.ty @!! go!"strongconnect"))
      (Val #(ptrOf F v))) (Val #idxp))
  {{ (b : Bool), RET #b; ∃ (σ' : RState) (t' : St InstId),
      exHeap γ i r e F σ' t' idxp ∗ ⌜ExRel σ σ' ∧ ExecWf σ' ∧ instBounds σ'.inst ∧
        VisCount t' ∧ Ext (gr σ) t (gr σ') t' ∧ t.n ≤ t'.n ∧
        (if b then TInv (gr σ') t' ∧ scTrue σ' t' t.A v t.n
          else WInv (gr σ') t' ∧ ∀ x ∈ t'.S, ∃ w, σ'.inst x = some w)⌝ }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
