/- Lean-first (no Rocq counterpart).

# `(*driverClient).Fail`'s proof

`unary` of the method's full name.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__Fail
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.driverClient__unary

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem driverClient.Fail.wp_proof (wp_unary : driverClient.unary.spec (GF := GF) (hG := hG)) :
    driverClient.Fail.spec (GF := GF) (hG := hG) := by
  intro dc conn addrs Spec m Φ Ψe ctx cd om inp opts vs
  wp_start as ⟨#Hcc, #Hconn, #Hrpc, #Hom, Hspec, #Hctx, Hsend, #Hopts, %Hvs⟩
  wp_auto
  wp_apply (wp_unary dc conn addrs Spec m Φ Ψe ctx cd om inp opts vs failName) $$ [Hspec Hsend]
    as %resp %err H
  · iframe #
    iframe
    ipureintro; exact Hvs
  wp_auto
  iapply HΦ
  iexact H

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
