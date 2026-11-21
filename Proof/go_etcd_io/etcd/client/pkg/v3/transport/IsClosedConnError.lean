/-
The proof of `transport.IsClosedConnError` (`client/pkg/transport/listener.go`: `err != nil &&
strings.Contains(err.Error(), "closed")`), over `strings.Contains`'s spec and the error's `Error`
method (`http.errStrOk`). Until 2026-11-20 (prove-etcdapi) a trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.IsClosedConnError
public import Spec.strings.Contains

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.transport.Assumptions]

theorem transport.IsClosedConnError.wp_proof
    (hContains : strings.Contains.spec (GF := GF) (hG := hG)) :
    transport.IsClosedConnError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Herr
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  iunfold http.errStrOk at Herr
  icases Herr with (%hnil | ⟨%ei, %hei, #Hs, -, -⟩)
  · subst hnil
    wp_auto
    iapply HΦ; ipureintro; trivial
  · subst hei
    wp_auto
    wp_bind (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
    iapply Hs
    inext
    iintro %s
    wp_auto
    wp_apply hContains
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
