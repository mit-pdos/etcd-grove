/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/Main.lean` (restart S7.5, step g,
2026-11-14): `zap.NewNop()`, then `Run` (`Run.spec`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Main
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro N id ctxs boot ThB RcB RcN Hbf hlv HwbN Haf Hbuq Hdbo
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_apply wp_NewNop as %lg #Hlgz
  wp_apply (wp_Run lg N id ctxs boot Hbf hlv HwbN Haf Hbuq Hdbo) $$ [Hstart Htok] as %b -
  · iframe; iframe #
  iapply HΦ; itrivial

end proof

end etcd_restart1
end EtcdGrove
end Perennial
