/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/leases.lean`. Lean-first.

The client's `Lease` field (`isNewClient`: a `*lessor` over the connection, `lessorRemoteAt`), the
context with the request timeout (`client.wp_WithTimeout_bg`), `lessor.Leases` at the caller's
`Spec` and `Q`, and the cancel.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.leases
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

theorem leases.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG)) :
    leases.spec (GF := GF) (hG := hG) := by
  intro CRE CEC cl eps V Spec Q hAs
  wp_start as ⟨#Hnc, #Hrpc, #HS⟩
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
  wp_apply (wp_Leases lp eps Spec Q gctx gcd) as %gr %gerr Hgr
  · iframe #
  icases Hgr with (⟨%Hgerr, %mg, %hg, %sl, -, -, #Hgsl, Hsl, HQg⟩ | ⟨%Hgfail, -⟩)
  · imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    (try wp_auto)
    wp_apply Hgcancel
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Hgerr
    iexists mg, sl
    iframe; iframe #
  · (try wp_auto)
    wp_apply Hgcancel
    (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact Hgfail.1

end proof

end etcd_leasecatchup
end EtcdGrove
end Perennial
