/-
Proof of `collectFor.spec`: `AfterFunc` (its function `cancel`, which returns), `Collect`, the timer's `Stop`
and `cancel` (as `RunWatch.lean`'s same three calls). Lean-first (no Rocq counterpart); F7 stage S6.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.collectFor
public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.Timer__Stop
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
theorem collectFor.wp_proof
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG))
    (wp_Collect : etcdstart.Collect.spec (GF := GF) (hG := hG)) :
    collectFor.spec (GF := GF) (hG := hG) := by
  intro _ Ok I F A wch γ cancel upTo c0 hI hP hC hS
  wp_start as ⟨Hcons, #HA, #Hcancel⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  -- `t := time.AfterFunc(readTimeout, cancel)`
  wp_apply (wp_AfterFunc _ cancel) $$ [] as %t Ht
  · wp_apply Hcancel $$ [] as -
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- `evs, ok := etcdstart.Collect(wch, upTo)`
  wp_apply (wp_Collect Ok I F A wch γ upTo c0 hI hP hC hS) $$ [Hcons] as %sl %ok Hcol
  · iframe; iframe #
  (try wp_auto)
  -- `t.Stop()`, `cancel()`
  wp_apply (wp_Stop t) $$ [Ht] as %b -
  · iright; iexact Ht
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  (try wp_auto)
  iapply HΦ
  iexact Hcol

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
