/-
`(*DaemonSetsController).syncNodes(ctx, ds, podsToDelete, nodesNeedingDaemonPods, hash)`
(`daemon_controller.go:1040`): set the expectations, create a pod on each node needing one (at most
`burstReplicas`, in slow-start batches of goroutines, each `CreatePods` of the template with the
node's affinity; a failure lowers the expectations and stops later batches), wait, then delete the
pods (goroutines, `DeletePod`), wait, and aggregate the errors. Lean-first; Stage 3, track B.

**The S1 argument.** The caller holds the owner's permission whole and its bound `(L, r)`; if it
asks for creates, the owner is ready (`r`) and the nodes are free at a version at least `L`
(`nodesFree`: its pod cache shows no pod of the DaemonSet on them), distinct. The proof claims each
node (`claim_step`: no pod of the DaemonSet on it now), hands each create goroutine its claim and a
fraction of the permission; a create that commits makes the pod the claim's (`create_step`, the
pod `podOf` the DaemonSet: its template, its hash `hash`, its controller reference), its
`OnWrite` (`WroteAt`) writes the claim (`wrote_step`); a create with no effect unclaims
(`unclaim_step`). After `createWait.Wait()` the proof releases the written claims
(`release_step`), so every fraction is back: the sync token.

**The ambiguous create** (`createErrOutcome`'s `.ok (true, _)`, `AmbiguousWrites`): the pod is the
claim's, unwritten: the claim can be neither written nor released, its fraction of the permission
stays in the invariant, and the sync token cannot be given back. The proof leaves exactly that
branch `sorry` (`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`,
`ambiguous_create_breaks_S1`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`dsc.syncNodes(ctx, ds, podsToDelete, nodesNeeding, hash)`**: see the file header. -/
abbrev DaemonSetsController.syncNodes.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (pdl : GoSlice) (dq : DFrac) (pds : List GoString) (nnl : GoSlice)
    (dq' : DFrac) (nns : List GoString) (hash : GoString) (L : Nat) (r : Bool),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗
      pdl ↦*{dq} pds ∗ nnl ↦*{dq'} nns ∗ ⌜nns.Nodup ∧ hash = dsHash d⌝ ∗
      ownerTok c o 1 ∗ seenTok γ o (L, r) ∗
      (⌜nns = []⌝ ∨ ⌜r = true⌝ ∗ nodesFree γa d.ObjectMeta'.UID' L nns) }}
    (App (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"syncNodes")) (Val #ctx)) (Val #ds)) (Val #pdl)) (Val #nnl)) (Val #hash))
  {{ (err : GoInterface), RET #err; threadTok ∗ syncTok γ c o ∗ fmt.argOk err ∗
      pdl ↦*{dq} pds ∗ nnl ↦*{dq'} nns }}

end spec

end dsctl
end EtcdGrove
end Perennial
