/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/Orchestrator.lean`. Lean-first.
`Orchestrator.wp_proofKv` (N7-kv, M1) and `Orchestrator.wp_proof` (F8): `MainDeployment` with a `ready` that does
nothing.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Orchestrator
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainDeployment

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem Orchestrator.wp_proofKv (OP : List GoString → w64 → IProp GF)
    (hMD : MainDeployment.specKv (GF := GF) (hG := hG) OP) :
    Orchestrator.specKv (GF := GF) (hG := hG) OP := by
  intro v d j
  wp_start as ⟨%Hp, #Hd, Hsh⟩
  wp_auto
  wp_apply (hMD v d j _) $$ [Hsh] as %r -
  · iframe #
    iframe
    isplit
    · ipureintro; exact Hp
    iunfold readySpec
    wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial
  iapply HΦ; ipureintro; trivial

end proof

section proofFull
open Net client etcd_dist_client etcd_dist.view
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Orchestrator.wp_proof
    (hMD : MainDeployment.spec (GF := GF) (hG := hG)) :
    Orchestrator.spec (GF := GF) (hG := hG) := by
  intro π ρ errA fmtA rpcA v d j
  wp_start as ⟨%Hp, Htok, #Hd, Hsh⟩
  wp_auto
  wp_apply (hMD v d j _) $$ [Htok Hsh] as %r -
  · iframe #
    iframe
    isplitr
    · ipureintro; exact Hp
    iunfold readySpec
    wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial
  iapply HΦ; ipureintro; trivial

end proofFull

end etcd_dist
end EtcdGrove
end Perennial
