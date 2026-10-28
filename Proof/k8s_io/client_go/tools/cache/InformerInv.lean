/-
**The informer invariant** (phase 4 of `notes/k8s-daemonset-plan.md`, fourth round): the Iris
invariant tying the model API server's history (`apiState`'s lower bounds `pastSt`), the informer's
FIFO (`fifoSt`), its store (`storeSt`) and the pure contract `InfP` (`InformerContract.lean`), for
one informer of one resource (all namespaces). Lean-first.

* `InfNames`: the registry of the Go objects the informer handles (`reg`, each a read-only copy of a
  model object, registered once: `infObj`), the reflector's last version (`last`, halves: the
  invariant's and the reflector's), the deltas popped and not yet applied (`pop`, halves: the
  invariant's and the processing goroutine's, with their Go deltas), the store's state as its writer
  knows it (`sw`), a lower bound of the store's version (`rvlb`, a mono counter: the contract's
  monotonicity, persistent), and the first list's version (`first`, persistent once set).
* `infObj γi r x`: the FIFO's and the store's object contract `OK`: `x` registered with a model
  object `o` of resource `r`, owned read-only (`objAt x DFrac.discard o`).
* `infInv`: there is a past state `σp` of the server and an abstract state `s` such that
  `s.ok (σp's log of r)` (`InfP.ok`), the reflector's last version at most `σp`'s, the FIFO's deltas
  are `s.fifo`'s (`fdRel`), the store is `s.store` (`storeRel`), the popped deltas are `s.popped`,
  and the FIFO's initial count is the first list's position (`syncOk`, `InformerSync.lean`: once
  synced, the store's version is at least the first list's).

The contract's statements over it are in `InformerSpec.lean`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerSync
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
  first : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An object the informer handles** (the FIFO's and the store's `OK`, persistent). -/
def infObj (γi : InfNames) (r : Res) (x : GoInterface) : IProp GF :=
  iprop(∃ o : Obj, x ↪[γi.reg]□ o ∗ □ apimodel.objAt x DFrac.discard o ∗ ⌜o.res = r⌝)

instance infObj_persistent (γi : InfNames) (r : Res) (x : GoInterface) :
    Persistent (infObj (GF := GF) γi r x) := by
  unfold infObj; infer_instance

/-- The first list's ghost variable's fraction: owned until set, then persistent. -/
def firstDq : Option Nat → DFrac
  | none => .own 1
  | some _ => .discard

/-- **The informer's first list was at version `v`** (persistent). -/
def infFirst (γi : InfNames) (v : Nat) : IProp GF := dghostVar γi.first .discard (some v)

instance infFirst_persistent (γi : InfNames) (v : Nat) : Persistent (infFirst (GF := GF) γi v) := by
  unfold infFirst; infer_instance

/-- **The informer invariant's content.** -/
def infRes (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames) : IProp GF :=
  iprop(∃ (σp : apimodel.St) (s : InfP) (q : FQ) (σs : cache.St) (R : Reg)
      (pd : List cache.FD) (ap : Bool) (f : Option Nat),
    pastSt γa σp ∗ ghostMapAuth γi.reg 1 R ∗ ([∗map] x ↦ o ∈ R, x ↪[γi.reg]□ o) ∗
    ([∗map] x ↦ o ∈ R, □ apimodel.objAt x DFrac.discard o) ∗
    fifoSt γf q ∗ storeSt γt σs ∗
    ghostVar γi.sw (1 : Qp).half σs ∗
    ghostVar γi.last (1 : Qp).half s.last ∗
    ghostVar γi.pop (1 : Qp).half (pd, ap) ∗
    monoNatAuthOwn γi.rvlb 1 (rvNat s.store.rv) ∗ dghostVar γi.first (firstDq f) f ∗
    ⌜s.ok (σp.tbl r).log ∧ rvLe s.last (some σp.rev.toNat) ∧
      List.Forall₂ (fdRel R) q.items s.fifo ∧ poppedRel R σs pd ap s.popped ∧
      storeRel R σs s.store ∧ (∀ x o, R !! x = some o → o.res = r) ∧
      (∀ c ∈ (σp.tbl r).log, keyGood c.obj.key) ∧ fqOk q pd ∧ pdReg R pd ∧
      syncOk q pd ap s f⌝)

instance ite_timeless' (c : Prop) [Decidable c] (P Q : IProp GF) [Timeless P] [Timeless Q] :
    Timeless (if c then P else Q) := by
  split <;> infer_instance

instance fifoSyncedLb_timeless (γf : FifoNames) : Timeless (fifoSyncedLb (GF := GF) γf) := by
  unfold fifoSyncedLb; infer_instance

instance objAt_timeless (x : GoInterface) (dq : DFrac) (o : Obj) :
    Timeless (apimodel.objAt (GF := GF) x dq o) := by
  cases o <;> unfold apimodel.objAt <;>
    first | (unfold podAt; infer_instance) | (unfold nodeAt; infer_instance) |
      (unfold dsAt; infer_instance) | (unfold crAt; infer_instance)

instance objAt_persistent (x : GoInterface) (o : Obj) :
    Persistent (apimodel.objAt (GF := GF) x DFrac.discard o) := by
  cases o <;> unfold apimodel.objAt <;>
    first | (unfold podAt; infer_instance) | (unfold nodeAt; infer_instance) |
      (unfold dsAt; infer_instance) | (unfold crAt; infer_instance)

open Iris.ProofMode in
/-- A string field owned exclusively and read-only at once: impossible. -/
theorem string_pointsto_excl (l : Loc) (s1 s2 : GoString) :
    (typedPointsto l s1 (DFrac.own 1) : IProp GF) ∗ typedPointsto l s2 DFrac.discard ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  rw [show typedPointstoDef (GF := GF) l s1 (DFrac.own 1) = heapPointsto l (DFrac.own 1) #s1 from rfl,
    show typedPointstoDef (GF := GF) l s2 DFrac.discard = heapPointsto l DFrac.discard #s2 from rfl]
  icombine H1 H2 gives %h
  ipureintro
  exact dfrac_own_one_op_invalid _ h.1

open Iris.ProofMode in
/-- A `TypeMeta` owned exclusively and read-only at once: impossible. -/
theorem typeMeta_pointsto_excl (l : Loc) (v1 v2 : k8s_io.apimachinery.pkg.apis.«meta».v1.TypeMeta) :
    (typedPointsto l v1 (DFrac.own 1) : IProp GF) ∗ typedPointsto l v2 DFrac.discard ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases H1 with ⟨H1, -, -⟩
  icases H2 with ⟨H2, -, -⟩
  iapply string_pointsto_excl
  iframe

open Iris.ProofMode in
theorem pod_pointsto_excl (l : Loc) (v1 v2 : k8s_io.api.core.v1.Pod) :
    (typedPointsto l v1 (DFrac.own 1) : IProp GF) ∗ typedPointsto l v2 DFrac.discard ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply typeMeta_pointsto_excl
  iframe

open Iris.ProofMode in
theorem node_pointsto_excl (l : Loc) (v1 v2 : k8s_io.api.core.v1.Node) :
    (typedPointsto l v1 (DFrac.own 1) : IProp GF) ∗ typedPointsto l v2 DFrac.discard ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply typeMeta_pointsto_excl
  iframe

open Iris.ProofMode in
theorem ds_pointsto_excl (l : Loc) (v1 v2 : k8s_io.api.apps.v1.DaemonSet) :
    (typedPointsto l v1 (DFrac.own 1) : IProp GF) ∗ typedPointsto l v2 DFrac.discard ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply typeMeta_pointsto_excl
  iframe

open Iris.ProofMode in
theorem cr_pointsto_excl (l : Loc) (v1 v2 : k8s_io.api.apps.v1.ControllerRevision) :
    (typedPointsto l v1 (DFrac.own 1) : IProp GF) ∗ typedPointsto l v2 DFrac.discard ⊢ ⌜False⌝ := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  simp only [TypedPointsto.typedPointstoDef]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply typeMeta_pointsto_excl
  iframe

open Iris.ProofMode in
/-- **An object owned exclusively is not one owned read-only** (so it is not yet registered). -/
theorem objAt_excl (x : GoInterface) (o o' : Obj) :
    (apimodel.objAt x (DFrac.own 1) o : IProp GF) ∗ apimodel.objAt x DFrac.discard o' ⊢ ⌜False⌝ := by
  cases o <;> cases o' <;> simp only [apimodel.objAt, apimodel.podAt, apimodel.nodeAt,
      apimodel.dsAt, apimodel.crAt] <;>
    iintro ⟨⟨%l1, %h1, %v1, H1, -⟩, ⟨%l2, %h2, %v2, H2, -⟩⟩ <;>
    rw [h1] at h2 <;>
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h2 <;>
    obtain ⟨ht, hl⟩ := h2 <;>
    first
    | (exfalso
       (try unfold k8s_io.api.core.v1.Pod.ty at ht)
       (try unfold k8s_io.api.core.v1.Node.ty at ht)
       (try unfold k8s_io.api.apps.v1.DaemonSet.ty at ht)
       (try unfold k8s_io.api.apps.v1.ControllerRevision.ty at ht)
       simp only [go.GoType.PointerType.injEq, go.GoType.Named.injEq] at ht
       exact absurd ht.1 (by decide))
    | (have hl' : l1 = l2 := intoVal_eq_iff.1 hl
       subst hl'
       first
       | (iapply pod_pointsto_excl; iframe; done) | (iapply node_pointsto_excl; iframe; done)
       | (iapply ds_pointsto_excl; iframe; done) | (iapply cr_pointsto_excl; iframe; done))

open Iris.ProofMode in
/-- **An object can be made read-only.** -/
theorem objAt_persist (x : GoInterface) (dq : DFrac) (o : Obj) :
    (apimodel.objAt x dq o : IProp GF) ⊢ |==> apimodel.objAt x DFrac.discard o := by
  cases o with
  | pod d =>
    simp only [apimodel.objAt, apimodel.podAt]
    iintro ⟨%l, %h, %v, Hp, Hown⟩
    imod (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq $$ Hp with Hp
    imod (DeepPersist.persist (GF := GF) (inner := kd.core.Pod.own) _ _ _) $$ Hown with Hown
    imodintro; iexists l; iframe; ipureintro; exact h
  | node d =>
    simp only [apimodel.objAt, apimodel.nodeAt]
    iintro ⟨%l, %h, %v, Hp, Hown⟩
    imod (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq $$ Hp with Hp
    imod (DeepPersist.persist (GF := GF) (inner := kd.core.Node.own) _ _ _) $$ Hown with Hown
    imodintro; iexists l; iframe; ipureintro; exact h
  | ds d =>
    simp only [apimodel.objAt, apimodel.dsAt]
    iintro ⟨%l, %h, %v, Hp, Hown⟩
    imod (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq $$ Hp with Hp
    imod (DeepPersist.persist (GF := GF) (inner := kd.apps.DaemonSet.own) _ _ _) $$ Hown with Hown
    imodintro; iexists l; iframe; ipureintro; exact h
  | cr d =>
    simp only [apimodel.objAt, apimodel.crAt]
    iintro ⟨%l, %h, %v, Hp, Hown⟩
    imod (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq $$ Hp with Hp
    imod (DeepPersist.persist (GF := GF) (inner := kd.apps.ControllerRevision.own) _ _ _) $$ Hown
      with Hown
    imodintro; iexists l; iframe; ipureintro; exact h

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

instance infRvLb_persistent (γi : InfNames) (n : Nat) : Persistent (infRvLb (GF := GF) γi n) := by
  unfold infRvLb; infer_instance

end defs

end informer
end EtcdGrove
end Perennial
