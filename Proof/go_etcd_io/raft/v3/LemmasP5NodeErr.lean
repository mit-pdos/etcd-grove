/-
The node methods' errors (raft-final phase 2, track P5; K5, the user's decision of 2026-10-29).

* The raw errors' introductions (`nodeErrRaw`, `propErrRaw`, `InvNodeChan`; the stopped answer
  carries `nodeStoppedRaw`): `nodeErrRaw_nil`/`_ctx`/`_stopped`, `propErrRaw_*`, and
  `stepWithWaitOption`'s `if wait then propErrRaw else nodeErrRaw` (`waitErrRaw_*`).
* From the raw errors to the API's (`nodeErrS`, `propErrS`, `InvNode`, sealed: stated at their
  bodies, `ApiImpl.nodeStopped`): `ApiImpl.nodeErrRaw_nodeErrS`, `ApiImpl.propErrRaw_propErrS`, at
  a node's names (`NodeOk`, `isNodeChan`, `nodeTabOk`, what `isNode` opens to);
  `ApiImpl.nodeStoppedRaw_nodeStopped` for the stopped answer alone.

Imported non-publicly by the node methods' proof files (it publicly imports `InvApi`, raft's
internals).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem nodeErrRaw_nil (γ : NodeNames) (cd : context.ContextDesc (IProp GF)) :
    ⊢ nodeErrRaw (GF := GF) γ cd interface.nil := by
  unfold nodeErrRaw
  ileft
  ipureintro; rfl

theorem nodeErrRaw_ctx (γ : NodeNames) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : ctxErr (GF := GF) cd err ⊢ nodeErrRaw γ cd err := by
  unfold nodeErrRaw
  iintro H
  iright; iright
  iexact H

theorem nodeErrRaw_stopped (γ : NodeNames) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : errStopped (GF := GF) err ∗ nodeStoppedRaw γ ⊢ nodeErrRaw γ cd err := by
  unfold nodeErrRaw
  iintro H
  iright; ileft
  iexact H

theorem propErrRaw_of_nodeErrRaw (γ : NodeNames) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : nodeErrRaw (GF := GF) γ cd err ⊢ propErrRaw γ cd err := by
  unfold propErrRaw
  iintro H
  ileft
  iexact H

theorem propErrRaw_nil (γ : NodeNames) (cd : context.ContextDesc (IProp GF)) :
    ⊢ propErrRaw (GF := GF) γ cd interface.nil := by
  iapply propErrRaw_of_nodeErrRaw
  iapply nodeErrRaw_nil

theorem propErrRaw_of_stepErr (γ : NodeNames) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) : stepErr (GF := GF) err ⊢ propErrRaw γ cd err := by
  unfold propErrRaw
  iintro H
  iright
  iexact H

theorem waitErrRaw_stopped (γ : NodeNames) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) (wait : Bool) :
    errStopped (GF := GF) err ∗ nodeStoppedRaw γ ⊢
      (if wait then propErrRaw γ cd err else nodeErrRaw γ cd err) := by
  iintro H
  cases wait
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply nodeErrRaw_stopped $$ H
  · simp only [↓reduceIte]
    iapply propErrRaw_of_nodeErrRaw
    iapply nodeErrRaw_stopped $$ H

theorem waitErrRaw_nil (γ : NodeNames) (cd : context.ContextDesc (IProp GF)) (wait : Bool) :
    ⊢ (if wait then propErrRaw (GF := GF) γ cd interface.nil else nodeErrRaw γ cd interface.nil) := by
  cases wait
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply nodeErrRaw_nil
  · simp only [↓reduceIte]
    iapply propErrRaw_nil

theorem waitErrRaw_ctx (γ : NodeNames) (cd : context.ContextDesc (IProp GF))
    (err : GoInterface) (wait : Bool) :
    ctxErr (GF := GF) cd err ⊢ (if wait then propErrRaw γ cd err else nodeErrRaw γ cd err) := by
  iintro H
  cases wait
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply nodeErrRaw_ctx $$ H
  · simp only [↓reduceIte]
    iapply propErrRaw_of_nodeErrRaw
    iapply nodeErrRaw_ctx $$ H

end lemmas

/-! The bridge to the API's errors, in `ApiImpl`'s terms: the conclusions are `nodeErrS`/`propErrS`
with `nodeStopped` and `Cluster` unfolded (sealed in `InvNode`), which a wrapper unfolds its goal
to. -/

namespace ApiImpl

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The node stopped, at its names: `nodeStopped`'s body. -/
theorem nodeStoppedRaw_nodeStopped (n : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (γn : NodeNames) (Hok : NodeOk γ γn) :
    EtcdGrove.isNodeChan (GF := GF) γn id n ∗ nodeTabOk γ id γn ∗ EtcdGrove.nodeStoppedRaw γn ⊢
      nodeStopped n γ N := by
  unfold nodeStopped
  iintro ⟨#Hch, #Htab, #Hst⟩
  iexists γn, id
  iframe Hch Htab Hst
  ipureintro; exact Hok

/-- `nodeErrRaw` at a node's names: `nodeErrS`'s body. -/
theorem nodeErrRaw_nodeErrS (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (γn : NodeNames)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) (Hok : NodeOk γ γn) :
    EtcdGrove.isNodeChan (GF := GF) γn id n ∗ nodeTabOk γ id γn ∗ nodeErrRaw γn cd err ⊢
      iprop(⌜err = interface.nil⌝ ∨ (errStopped err ∗ nodeStopped n γ N) ∨ ctxErr cd err) := by
  unfold nodeErrRaw
  iintro ⟨#Hch, #Htab, (%H | ⟨#He, #Hst⟩ | #H)⟩
  · ileft; ipureintro; exact H
  · iright; ileft
    iframe He
    iapply nodeStoppedRaw_nodeStopped n γ N id γn Hok
    iframe Hch Htab Hst
  · iright; iright; iexact H

/-- `propErrRaw` at a node's names: `propErrS`'s body. -/
theorem propErrRaw_propErrS (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (γn : NodeNames)
    (cd : context.ContextDesc (IProp GF)) (err : GoInterface) (Hok : NodeOk γ γn) :
    EtcdGrove.isNodeChan (GF := GF) γn id n ∗ nodeTabOk γ id γn ∗ propErrRaw γn cd err ⊢
      iprop((⌜err = interface.nil⌝ ∨ (errStopped err ∗ nodeStopped n γ N) ∨ ctxErr cd err) ∨
        stepErr err) := by
  unfold propErrRaw
  iintro ⟨#Hch, #Htab, (#H | #H)⟩
  · ileft
    iapply nodeErrRaw_nodeErrS n γ N id γn cd err Hok
    iframe Hch Htab H
  · iright; iexact H

end bridge

end ApiImpl

end EtcdGrove
end Perennial
