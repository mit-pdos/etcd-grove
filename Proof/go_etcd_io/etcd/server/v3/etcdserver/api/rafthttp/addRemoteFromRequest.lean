/-
`addRemoteFromRequest` (rafthttp stage 6d). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.addRemoteFromRequest
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDFromString
public import Perennial.Spec.strings.Split

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.addRemoteFromRequest.wp_proof
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hIDFrom : types.IDFromString.spec (GF := GF) (hG := hG))
    (hSplit : _root_.Perennial.strings.Split.spec (GF := GF) (hG := hG)) :
    rafthttp.addRemoteFromRequest.spec (GF := GF) (hG := hG) := by
  intro Rh lid ti r R rd
  wp_start as ⟨#HR, %Hfrom, #HAR⟩
  obtain ⟨f, Hf, Hfm, Hfne⟩ := Hfrom
  iunfold http.reqAt at HR
  icases HR with ⟨-, -, ⟨%hm, #HHm, #Hhs⟩, -, -, -⟩
  wp_auto
  wp_apply hHeaderGetPtr _ hm R.hdr _ $$ []
  · iframe #
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_apply hIDFrom _ as %fid %ferr ⟨-, %Hid⟩
  obtain ⟨hfid, hferr⟩ := Hid f Hf
  subst hfid hferr
  wp_auto
  wp_apply hHeaderGetPtr _ hm R.hdr _ $$ []
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; itrivial
  · ihave #Hstrp : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
    · iPkgInit
    wp_apply hSplit _ _ (by decide) as %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply HAR $$ [Hsl]
    · iframe Hsl; ipureintro; exact ⟨Hfm, Hfne⟩
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
