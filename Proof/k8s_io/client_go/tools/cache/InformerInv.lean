/-
**The informer invariant** (phase 4 of `notes/k8s-daemonset-plan.md`, fourth round): the Iris
invariant tying the model API server's history (`apiState`'s lower bounds `pastSt`), the informer's
FIFO (`fifoSt`), its store (`storeSt`) and the pure contract `InfP` (`InformerContract.lean`), for
one informer of one resource (all namespaces). Lean-first.

* `InfNames`: the registry of the Go objects the informer handles (`reg`, each a read-only copy of a
  model object, registered once: `infObj`), the reflector's last version (`last`, halves: the
  invariant's and the reflector's), the deltas popped and not yet applied (`pop`, halves: the
  invariant's and the processing goroutine's, with their Go deltas), the store's state as its writer
  knows it (`sw`), and a lower bound of the store's version (`rvlb`, a mono counter: the contract's
  monotonicity, persistent).
* `infObj γi r x`: the FIFO's and the store's object contract `OK`: `x` registered with a model
  object `o` of resource `r`, owned read-only (`objAt x DFrac.discard o`).
* `infInv`: there is a past state `σp` of the server and an abstract state `s` such that
  `s.ok (σp's log of r)` (`InfP.ok`), the reflector's last version at most `σp`'s, the FIFO's deltas
  are `s.fifo`'s (`fdRel`), the store is `s.store` (`storeRel`), the popped deltas are `s.popped`.

The contract's statements over it are in `InformerSpec.lean`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerRel
public import Proof.k8s_io.client_go.tools.cache.FIFODefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs
public import Perennial.Ghost.MonoNat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI apimodel cache

/-- The informer's ghost names (see the file header). -/
structure InfNames where
  reg : GName
  last : GName
  pop : GName
  sw : GName
  rvlb : GName

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An object the informer handles** (the FIFO's and the store's `OK`, persistent). -/
def infObj (γi : InfNames) (r : Res) (x : GoInterface) : IProp GF :=
  iprop(∃ o : Obj, x ↪[γi.reg]□ o ∗ □ objAt x DFrac.discard o ∗ ⌜o.res = r⌝)

instance infObj_persistent (γi : InfNames) (r : Res) (x : GoInterface) :
    Persistent (infObj (GF := GF) γi r x) := by
  unfold infObj; infer_instance

/-- **The informer invariant's content.** -/
def infRes (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames) : IProp GF :=
  iprop(∃ (σp : apimodel.St) (s : InfP) (q : FQ) (σs : cache.St) (R : Reg)
      (pd : List cache.FD) (ap : Bool),
    pastSt γa σp ∗ ghostMapAuth γi.reg 1 R ∗ ([∗map] x ↦ o ∈ R, x ↪[γi.reg]□ o) ∗
    fifoSt γf q ∗ storeSt γt σs ∗
    ghostVar γi.sw (1 : Qp).half σs ∗
    ghostVar γi.last (1 : Qp).half s.last ∗
    ghostVar γi.pop (1 : Qp).half (pd, ap) ∗
    monoNatAuthOwn γi.rvlb 1 (rvNat s.store.rv) ∗
    ⌜s.ok (σp.tbl r).log ∧ rvLe s.last (some σp.rev.toNat) ∧
      List.Forall₂ (fdRel R) q.items s.fifo ∧ poppedRel R σs pd ap s.popped ∧
      storeRel R σs s.store ∧ (∀ x o, R !! x = some o → o.res = r) ∧
      (∀ c ∈ (σp.tbl r).log, keyGood c.obj.key) ∧ fqOk q pd⌝)

instance ite_timeless' (c : Prop) [Decidable c] (P Q : IProp GF) [Timeless P] [Timeless Q] :
    Timeless (if c then P else Q) := by
  split <;> infer_instance

instance fifoSyncedLb_timeless (γf : FifoNames) : Timeless (fifoSyncedLb (GF := GF) γf) := by
  unfold fifoSyncedLb; infer_instance

instance infRes_timeless (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames) :
    Timeless (infRes (GF := GF) γa r γf γt γi) := by
  unfold infRes pastSt fifoSt syncedPart storeSt
  infer_instance

/-- **What a reader of the store learns** at its linearization point, at the store's state `σs`: a
past state of the server `σp` and a view `v` of the store, the store being `v` (`storeRel`, through
the registry `R`, whose entries it gets) and `v` the log's table at its version (`View.ok`), and a
lower bound of the store's version from now on. -/
def readFacts (γa : ApiNames) (r : Res) (γi : InfNames) (σs : cache.St) : IProp GF :=
  iprop(∃ (σp : apimodel.St) (v : View) (R : Reg), pastSt γa σp ∗
    ([∗map] x ↦ o ∈ R, x ↪[γi.reg]□ o) ∗ monoNatLbOwn γi.rvlb (rvNat v.rv) ∗
    ⌜storeRel R σs v ∧ v.ok (σp.tbl r).log⌝)

/-- The invariant's namespace. -/
def infN : Namespace := nroot.@"informer"

/-- **The informer invariant.** -/
def infInv (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames) : IProp GF :=
  inv infN (infRes γa r γf γt γi)

instance infInv_persistent (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) : Persistent (infInv (GF := GF) γa r γf γt γi) := by
  unfold infInv; infer_instance

/-- **A lower bound of the store's version** (persistent): the store's version is at least `n` from
now on. -/
def infRvLb (γi : InfNames) (n : Nat) : IProp GF := monoNatLbOwn γi.rvlb n

end defs

end informer
end EtcdGrove
end Perennial
