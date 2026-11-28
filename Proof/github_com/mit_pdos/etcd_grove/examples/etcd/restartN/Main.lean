/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/Main.lean` (`notes/restartN-plan.md`):
`Run(k, zap.NewNop())`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Main
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro k N ids ps ctxs boot ThB RcB RcN hk Hlen Hbf HLv HwbN Haf Hbuq Hdbo
  wp_start as ⟨Hss, Htok, #Hprem⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  wp_apply (wp_Run k lg N ids ps ctxs boot hk Hlen Hbf HLv HwbN Haf Hbuq Hdbo) $$ [Hss Htok]
  · iframe; iframe #
  iintro %b -
  wp_auto
  iapply HΦ; itrivial

end proof

end etcd_restartN
end EtcdGrove
end Perennial
