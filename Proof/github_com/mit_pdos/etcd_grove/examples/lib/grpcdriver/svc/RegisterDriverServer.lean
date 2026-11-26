/- Lean-first (no Rocq counterpart).

# `svc.RegisterDriverServer`'s proof

`s.RegisterService(&Driver_ServiceDesc, srv)` on the `*grpc.Server` (`RegisterService.spec`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.RegisterDriverServer
public import Spec.google_golang_org.grpc.Server__RegisterService

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem RegisterDriverServer.wp_proof
    (wp_RegisterService : grpc.Server.RegisterService.spec (GF := GF) (hG := hG)) :
    RegisterDriverServer.spec (GF := GF) (hG := hG) := by
  intro gs srv ics sics svcs regs sregs sn ht mds sds
  wp_start as ⟨Hs, #Hd, %Hsn, %Himpl, %Hnd, %Hfl⟩
  wp_auto
  wp_apply (wp_RegisterService gs _ srv ics sics svcs regs sregs sn ht mds sds) $$ [Hs] as Hs
  · iframe; iframe #; ipureintro; exact ⟨Hsn, Himpl, Hnd, Hfl⟩
  iapply HΦ
  iexact Hs

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
