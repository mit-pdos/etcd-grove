/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/createPostRequest.lean` (rafthttp
stage 6e, 2026-10-24). Lean-first. The URL's path set and rendered (`URLString_spec`, a plain URL),
the request built (`NewRequest_spec`: it does not fail, so `lg.Panic` is not reached), five
headers set, the peer URLs' header last (`setPeerURLsHeader`, which keeps the others).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createPostRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.setPeerURLsHeader
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem rafthttp.createPostRequest.wp_proof
    (hURLString : http.URLString_spec (GF := GF))
    (hNewRequest : http.NewRequest_spec (GF := GF))
    (hSet : http.HeaderSetPtr_spec (GF := GF))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hSetPeer : rafthttp.setPeerURLsHeader.spec (GF := GF) (hG := hG)) :
    rafthttp.createPostRequest.spec (GF := GF) (hG := hG) := by
  intro lg u path body K ct urls uvs fr cid Hlg Hu
  wp_start as ⟨Hbody, #Hurls⟩
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hhost⟩ := Hu
  wp_auto
  wp_apply (hURLString uu_ptr (DFrac.own 1) { u with Path' := path } hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
      hs9) $$ [uu] as uu
  · iexact uu
  (try wp_auto)
  wp_apply (hNewRequest go!"POST" _ body K u.Host' path rfl hhost (Or.inl rfl)) $$ [Hbody]
    as %req ⟨Hreq, Hstr⟩
  · iexact Hbody
  (try wp_auto)
  -- the headers
  iunfold http.reqOwn at Hreq
  icases Hreq with ⟨%hm, #Hhf, Hhm, Hrest⟩
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hpver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
      globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0") $$ []
  · iapply isPkgInit_access $$ Hpver
  icases Hvi with ⟨#HVer, -, #HMCV⟩
  wp_apply (hSet _ hm _ _ _) $$ [Hhm] as Hhm
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hIDStringPtr from_ptr (DFrac.own 1) fr) $$ [«from»] as %fs ⟨«from», %Hfs⟩
  · iframe; try iframe #
  (try wp_auto)
  wp_apply (hSet _ hm _ _ _) $$ [Hhm] as Hhm
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hSet _ hm _ _ _) $$ [Hhm] as Hhm
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hSet _ hm _ _ _) $$ [Hhm] as Hhm
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hIDStringPtr cid_ptr (DFrac.own 1) cid) $$ [cid] as %cs ⟨cid, -⟩
  · iframe; try iframe #
  (try wp_auto)
  wp_apply (hSet _ hm _ _ _) $$ [Hhm] as Hhm
  · iframe; iframe #
  (try wp_auto)
  -- the peer URLs' header, the others kept
  ihave Hreq : http.reqOwn req ⟨go!"POST", u.Host', path, _, K.bytes⟩ $$ [Hhm Hrest]
  · iunfold http.reqOwn
    iexists hm
    iframe; iframe #
    iunfold http.reqRest at Hrest
    iunfold http.reqRest
    iexact Hrest
  wp_apply (hSetPeer req _ urls uvs) $$ [Hreq] as ⟨%hs, %Hhs, Hreq⟩
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexists hs
  iframe Hreq Hstr
  ipureintro
  rw [Hhs _ (by decide)]
  simp only
  rw [http.hdrGet_hdrSet_ne _ _ _ _ (by decide), http.hdrGet_hdrSet_ne _ _ _ _ (by decide),
    http.hdrGet_hdrSet_ne _ _ _ _ (by decide), http.hdrGet_hdrSet_eq]
  exact Hfs

end proof

end EtcdGrove
end Perennial
