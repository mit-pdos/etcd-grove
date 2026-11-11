/- Lean-first (no Rocq counterpart). The proof of `runner.checkHook`: proved.

The outline: `saved.Load`, `check`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.checkHook.wp_proof
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    runner.checkHook.spec (GF := GF) (hG := hG) := by
  intro x mp i
  wp_start as Hs
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Load (mF go!"saved" mp) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists i
  iframe
  iintro Hs
  imod Hcl with -
  imodintro
  wp_auto
  wp_apply wp_check
  · itrivial
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
