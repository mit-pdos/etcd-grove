/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/Main.lean` (the restart plan's R2a,
2026-11-02): `Run(zap.NewNop())`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.Main
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CR CE N id₁ id₂ id₃ ctxs boot Hp Hms Has
  wp_start as Hres
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_apply wp_NewNop as %lg %Hlg
  wp_apply (wp_Run lg N id₁ id₂ id₃ ctxs boot Hlg Hp Hms Has) $$ [Hres]
  · iframe
  iapply HΦ; itrivial

end proof

end restart3
end EtcdGrove
end Perennial
