/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/grant.lean`. Lean-first.

The client's `Lease` field (`isNewClient`: a `*lessor` over the connection, `lessorRemoteAt`), the
context with the request timeout (`client.wp_WithTimeout_bg`), `lessor.Grant` at the caller's
`Spec` and `Q`, and the cancel.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.grant
public import Perennial.Spec.context.Background

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

theorem grant.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG)) :
    grant.spec (GF := GF) (hG := hG) := by
  intro CRE CEC cl eps V Spec Q
  wp_start as ⟨#Hnc, #Hrpc, #HS, %hAs⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  iunfold isNewClient at Hnc
  icases Hnc with ⟨-, -, -, -, ⟨%lp, #Hlf, #Hla⟩, -⟩
  iunfold lessorAt at Hla
  icases Hla with ⟨%dc, %γd, %sc, %scd, %llg, %d, %γr, -, -, -, -, -, -, -, #Hrem, -, -⟩
  wp_auto
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  wp_apply (wp_Grant lp eps Spec Q gctx gcd) as %gr %gerr Hgr
  · iframe #
  (try wp_auto)
  wp_apply Hgcancel
  (try wp_auto)
  icases Hgr with (⟨%Hgerr, %mg, %hg, -, -, #Hgid, -, HQg⟩ | ⟨%Hgfail, -⟩)
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Hgerr
    iexists mg
    iframe; iframe #
  · iapply HΦ
    iright
    ipureintro; exact Hgfail.1

end proof

end etcd_leasecatchup
end EtcdGrove
end Perennial
