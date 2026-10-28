/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/newRevision.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.CtxLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.newRevision.wp_proof :
    v3compactor.newRevision.spec (GF := GF) (hG := hG) := by
  intro lg clk ret E
  wp_start as ⟨%Hlgnn, #Hclk⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  iStructNamed «$r0»
  -- `mu` over `paused`
  imod sync.init_Mutex (revPausedInv «$r0_ptr») ⊤ (structFieldRef v3compactor.Revision go!"mu" «$r0_ptr»)
    $$ [mu] [paused] with #Hmu
  · iexact mu
  · inext; unfold revPausedInv; iexists false; iexact paused
  -- the fields are read-only once stored: persisted under the postcondition's update
  iapply wp_fupd
  wp_apply _root_.Perennial.context.wp_Background
  -- `WithCancel(Background())`, carrying no trace (M2's freeze repair)
  wp_apply traceutil.wp_WithCancelBackground_noTrace as %ctx %γctx %cancel ⟨#Hcs, #Hctx, #Htr⟩
  ipersist lg
  ipersist clock
  ipersist retention
  ipersist rg
  ipersist c
  ipersist ctx
  ipersist cancel
  imodintro
  iapply HΦ
  unfold isRevision
  iexists lg, clk, ret, ctx, { Values := ∅, Deadline := none, Done_gn := γctx, PDone := iprop(True) },
    γctx, cancel
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hlgnn
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
