/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/hashKVHandler__ServeHTTP.lean` (PR
etcd#22243, 2026-10-17). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.hashKVHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Int64
public import Spec.net.http.MaxBytesReader
public import Spec.net.http.Error
public import Spec.net.http.Header__Get
public import Spec.net.http.Header__Set
public import Spec.io.ReadAllMaxBytes
public import Spec.encoding.json.UnmarshalHashKVRequest
public import Spec.encoding.json.MarshalHashKVResponse
public import Spec.errors.AsExact

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- `h.lg.Warn(msg, fields...)`: the fields' slice literal, then `Warn` (`hWarn`, `Hlgn`). -/
local macro "warn" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWarn _ _ _ $$ []
  · ipureintro; exact Hlgn
  (try wp_auto)))

set_option hygiene false in
/-- After the body is read: `http.Error(w, msg, code)`, `return`, the deferred `r.Body.Close()`,
and the postcondition's last case with the events `evs` (`pf`: its pure part). -/
local macro "err_close " evs:term ", " pf:term : tactic => `(tactic| (
  wp_apply hErr $$ [Hlog] as Hlog
  · iexact Hlog
  wp_pures
  wp_auto
  wp_bind (App (Val #(methods bi.ty _ bi.v)) (Val #()))
  iapply HbC $$ %_ [HB]
  · iexact HB
  iintro !> %e0 HB
  wp_auto
  iapply HΦ
  iexists $evs
  iframe
  iright; iright; iright
  iframe
  ipureintro
  exact $pf))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem hashKVHandler.ServeHTTP.wp_proof
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cluster.spec (GF := GF) (hG := hG))
    (hRCID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hIDS : types.ID.String.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hMBR : http.MaxBytesReader.spec (GF := GF) (hG := hG))
    (hErr : http.Error.spec (GF := GF) (hG := hG))
    (hGet : http.Header.Get.spec (GF := GF) (hG := hG))
    (hSet : http.Header.Set.spec (GF := GF) (hG := hG))
    (hRA : io.ReadAllMaxBytes.spec (GF := GF) (hG := hG))
    (hUM : json.UnmarshalHashKVRequest.spec (GF := GF) (hG := hG))
    (hM : json.MarshalHashKVResponse.spec (GF := GF) (hG := hG))
    (hAs : errors.AsExact.spec (GF := GF) (hG := hG)) :
    hashKVHandler.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro h r w q c cid R evs
  haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
  -- `r`'s fields through `net/http`'s type assumption (`Request.TypeAssumptions`), not the
  -- generated instance of the axiomatized `http.Request` (a `sorry`), which instance search
  -- finds first otherwise
  haveI : go.TypeReprUnderlying _root_.Perennial.net.http.Request.underlying
      _root_.Perennial.net.http.Request :=
    _root_.Perennial.net.http.Request.TypeAssumptions.type_repr
  haveI : TypeRepr _root_.Perennial.net.http.Request.ty _root_.Perennial.net.http.Request :=
    go.type_repr_underlying (u := _root_.Perennial.net.http.Request.underlying)
  haveI : TypeRepr _root_.Perennial.net.http.Request.underlying
      _root_.Perennial.net.http.Request :=
    go.type_repr_underlying (u := _root_.Perennial.net.http.Request.underlying)
  wp_start as ⟨#Hh, #Hw, Hlog, #Hr, #Hb, HB, #Hbe⟩
  iunfold hashKVHandlerOk at Hh
  icases Hh with ⟨%lg, %s, %cl, %kv, %em, #Hlg, %Hlgn, #Hs, #Hcl, #Hcid, #Hkv, #Hkvok,
    #Hem, #Hems⟩
  iunfold http.respWriterOk at Hw
  icases Hw with ⟨%wi, %Hwi, #HwH, #HwW⟩
  iunfold http.reqIs at Hr
  icases Hr with ⟨%u, #Hmeth, #Hurl, #Hpath, #Hhdr, #Hbody⟩
  iunfold http.bodyOk at Hb
  icases Hb with ⟨%bi, %Hbi, #HbC⟩
  subst Hwi
  wp_apply wp_with_defer as %defer defer
  wp_if_destruct
  rotate_left
  · -- not a GET: `Allow: GET`, 405
    wp_bind (App (Val #(methods wi.ty _ wi.v)) (Val #()))
    iapply HwH $$ %evs [Hlog]
    · iexact Hlog
    iintro !> %hm ⟨Hlog, #Hhm⟩
    wp_auto
    wp_apply hSet $$ [Hlog] as Hlog
    · iframe #; iexact Hlog
    wp_apply hErr $$ [Hlog] as Hlog
    · iexact Hlog
    wp_pures
    wp_auto
    iapply HΦ
    iexists [.header go!"Allow" go!"GET", .error (W64 405) go!"Method Not Allowed"]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    iframe
    ileft
    iframe
    ipureintro
    exact ⟨Hif, by trivial⟩
  have Hget := Hif
  clear Hif
  wp_if_destruct
  rotate_left
  · -- another path: 400
    wp_apply hErr $$ [Hlog] as Hlog
    · iexact Hlog
    wp_pures
    wp_auto
    iapply HΦ
    iexists [.error (W64 400) go!"bad path"]
    iframe
    iright; ileft
    iframe
    ipureintro
    exact ⟨Hget, Hif, by trivial⟩
  have Hpath := Hif
  clear Hif
  wp_apply hGet $$ [] as -
  · iframe #
  -- `gcid != "" && gcid != h.server.cluster.ID().String()`
  wp_join (Q := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗
      ⌜(b = true → q.clusterHdr ≠ [] ∧ q.clusterHdr ≠ types.idStr cid) ∧
        (b = false → q.clusterHdr = [] ∨ q.clusterHdr = types.idStr cid)⌝ ∗
      h_ptr ↦ h ∗ gcid_ptr ↦ q.clusterHdr)) at (If _ _ (Val #false)) with [h gcid]
  · wp_if_destruct
    · iexists false
      iframe
      ipureintro
      exact ⟨rfl, by simp, fun _ => Or.inl Hif⟩
    try wp_auto
    wp_apply hRCID $$ [] as -
    · iframe #
    wp_apply hIDS as %sid %Hsid
    subst Hsid
    iexists _
    iframe
    ipureintro
    refine ⟨rfl, ?_, ?_⟩
    · intro hb
      refine ⟨Hif, ?_⟩
      simp_all
    · intro hb
      right
      simp_all
  iintro ⟨%b, %Hv, %Hb, h, gcid⟩
  subst Hv
  cases b
  rotate_left
  · -- another cluster's id: 412
    wp_auto
    iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at Hems
    wp_bind (App (Val #(methods em.ty _ em.v)) (Val #()))
    iapply Hems
    iintro !> %str
    wp_auto
    wp_apply hErr $$ [Hlog] as Hlog
    · iexact Hlog
    wp_pures
    wp_auto
    iapply HΦ
    iexists [.error (W64 412) str]
    iframe
    iright; iright; ileft
    iframe
    ipureintro
    exact ⟨Hget, Hpath, (Hb.1 rfl).1, (Hb.1 rfl).2, str, rfl⟩
  wp_auto
  rw [Hbi]
  wp_auto
  -- the body, through `http.MaxBytesReader(w, r.Body, maxHashKVHTTPRequestSize)`
  have Hcl := Hb.2 rfl
  wp_apply hMBR as %lr Hlr
  wp_apply hRA $$ [HB Hlr] as %sl %err ⟨HB, Hres⟩
  · iframe
    try (ipureintro; word)
  have Hn : uint.nat (W64 65536) = maxHashKVBody := by word
  rw [Hn]
  icases Hres with (⟨%Hlen, Hsl, %m, %Herr⟩ | ⟨%Hlen, Hsl, %e, %He⟩ | ⟨%Hok, Hsl⟩)
  · -- longer than the bound: 413
    subst Herr
    wp_auto
    wp_apply hAs _ m maxBytesErr_ptr _ http.maxBytesError_asTarget $$ [maxBytesErr] as maxBytesErr
    · iexact maxBytesErr
    wp_apply hErr $$ [Hlog] as Hlog
    · iexact Hlog
    wp_pures
    wp_auto
    wp_bind (App (Val #(methods bi.ty _ bi.v)) (Val #()))
    iapply HbC $$ %_ [HB]
    · iexact HB
    iintro !> %e0 HB
    wp_auto
    iapply HΦ
    iexists [.error (W64 413) go!"request body too large"]
    iframe
    iright; iright; iright
    iframe
    ipureintro
    exact ⟨Hget, Hpath, Hcl, Or.inl ⟨Hlen, rfl⟩⟩
  · -- a read error within the bound: 413 if `errors.As` finds a `MaxBytesError`, else 400
    obtain ⟨Hce, rfl⟩ := He
    ihave Htree := http.bodyErrOk_some c e Hce $$ Hbe
    icases Htree with ⟨%S, %HS, #Htree⟩
    wp_auto
    wp_apply _root_.Perennial.errors.wp_As S (GoInterface.ok e) maxBytesErr_ptr
      (T := go.GoType.PointerType _root_.Perennial.net.http.MaxBytesError.ty) (null : Loc)
      http.maxBytesError_asTarget $$ [maxBytesErr] as %b %v' maxBytesErr
    · iframe #; iframe; ipureintro; exact HS
    cases b
    · try wp_auto
      wp_apply hErr $$ [Hlog] as Hlog
      · iexact Hlog
      wp_pures
      wp_auto
      wp_bind (App (Val #(methods bi.ty _ bi.v)) (Val #()))
      iapply HbC $$ %_ [HB]
      · iexact HB
      iintro !> %e0 HB
      wp_auto
      iapply HΦ
      iexists [.error (W64 400) go!"error reading body"]
      iframe
      iright; iright; iright
      iframe
      ipureintro
      exact ⟨Hget, Hpath, Hcl, Or.inr (Or.inl ⟨Hlen, by simp [Hce], Or.inr rfl⟩)⟩
    · try wp_auto
      wp_apply hErr $$ [Hlog] as Hlog
      · iexact Hlog
      wp_pures
      wp_auto
      wp_bind (App (Val #(methods bi.ty _ bi.v)) (Val #()))
      iapply HbC $$ %_ [HB]
      · iexact HB
      iintro !> %e0 HB
      wp_auto
      iapply HΦ
      iexists [.error (W64 413) go!"request body too large"]
      iframe
      iright; iright; iright
      iframe
      ipureintro
      exact ⟨Hget, Hpath, Hcl, Or.inr (Or.inl ⟨Hlen, by simp [Hce], Or.inl rfl⟩)⟩
  · -- the body, whole
    obtain ⟨Hlen, Hce, rfl⟩ := Hok
    wp_auto
    wp_apply hUM $$ [Hsl «$r0»] as %err2 ⟨Hsl, %v, Hreq, %Hdec⟩
    · iframe
    rcases Hj : json.hashKVReqOf c.data with _ | rev <;> rw [Hj] at Hdec <;> simp only at Hdec
    · -- not a request: 400
      rcases err2 with e2 | _
      rotate_left
      · exact absurd rfl Hdec
      wp_auto
      wp_apply hZE as %f -
      warn
      err_close [.error (W64 400) go!"error unmarshalling request"],
        ⟨Hget, Hpath, Hcl, Or.inr (Or.inr ⟨Hlen, Hce, by rw [Hj]⟩)⟩
    · -- the request's revision `rev`: `h.server.KV().HashStorage().HashByRev(rev)`
      obtain ⟨rfl, Hrev⟩ := Hdec
      wp_auto
      wp_apply hKV s kv $$ []
      · iframe #
      iunfold hashKVOk at Hkvok
      icases Hkvok with ⟨%ki, %Hki, #HHS⟩
      subst Hki
      wp_auto
      wp_bind (App (Val #(methods ki.ty _ ki.v)) (Val #()))
      iapply HHS
      · itrivial
      iintro !> %hs #Hhs
      iunfold hashByRevOk at Hhs
      icases Hhs with ⟨%hi, %Hhi, #HHR⟩
      subst Hhi
      wp_auto
      wp_bind (App (Val #(methods hi.ty _ hi.v)) (Val #v.Revision'))
      iapply HHR $$ %v.Revision'
      · itrivial
      iintro !> %kvh %crev %err3 ⟨%HR, #Herr3⟩
      wp_auto
      rcases err3 with e3 | _
      · -- `HashByRev` fails: 400
        wp_auto
        wp_apply hZI as %f1 -
        wp_apply hZE as %f2 -
        warn
        ihave #He3 := Herr3 $$ %e3 %rfl
        iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at He3
        wp_bind (App (Val #(methods e3.ty _ e3.v)) (Val #()))
        iapply He3
        iintro !> %str
        wp_auto
        err_close [.error (W64 400) str],
          ⟨Hget, Hpath, Hcl, Or.inr (Or.inr ⟨Hlen, Hce, by rw [Hj]; exact Or.inl ⟨str, rfl⟩⟩)⟩
      have HR' := HR rfl
      rw [Hrev] at HR'
      wp_auto
      wp_apply hM «$r0_ptr» «$v0_ptr» crev kvh.CompactRevision' kvh.Revision' kvh.Hash'
        $$ [«$r0» «$v0»] as %sl2 %err4 ⟨Hjs, #Herr4⟩
      · unfold hkvResp hkvRespHeader
        iframe
      rcases err4 with e4 | _
      · -- `json.Marshal` fails: 500
        wp_auto
        wp_apply hZE as %f2 -
        warn
        ihave #He4 := Herr4 $$ %e4 %rfl
        iunfold go_etcd_io.etcd.cache.v3.errorStringSpec at He4
        wp_bind (App (Val #(methods e4.ty _ e4.v)) (Val #()))
        iapply He4
        iintro !> %str
        wp_auto
        err_close [.error (W64 500) str],
          ⟨Hget, Hpath, Hcl, Or.inr (Or.inr ⟨Hlen, Hce, by
            rw [Hj]; exact Or.inr ⟨kvh, crev, HR', Or.inl ⟨str, rfl⟩⟩⟩)⟩
      ihave Hjs := Hjs $$ %rfl
      wp_auto
      -- the response: its headers, then the hash
      wp_apply hCl s cl $$ []
      · iframe #
      wp_apply hRCID $$ [] as -
      · iframe #
      wp_apply hIDS as %sid %Hsid
      subst Hsid
      wp_bind (App (Val #(methods wi.ty _ wi.v)) (Val #()))
      iapply HwH $$ %_ [Hlog]
      · iexact Hlog
      iintro !> %hm1 ⟨Hlog, #Hhm1⟩
      wp_auto
      wp_apply hSet $$ [Hlog] as Hlog
      · iframe #; iexact Hlog
      wp_bind (App (Val #(methods wi.ty _ wi.v)) (Val #()))
      iapply HwH $$ %_ [Hlog]
      · iexact Hlog
      iintro !> %hm2 ⟨Hlog, #Hhm2⟩
      wp_auto
      wp_apply hSet $$ [Hlog] as Hlog
      · iframe #; iexact Hlog
      wp_pures
      wp_auto
      wp_bind (App (Val #(methods wi.ty _ wi.v)) (Val #sl2))
      iapply HwW $$ %_ %_ %_ %_ [Hlog Hjs]
      · iframe
      iintro !> %n %ew ⟨Hlog, Hjs⟩
      wp_auto
      wp_bind (App (Val #(methods bi.ty _ bi.v)) (Val #()))
      iapply HbC $$ %_ [HB]
      · iexact HB
      iintro !> %e0 HB
      wp_auto
      iapply HΦ
      iexists [.header go!"X-Etcd-Cluster-ID" (types.idStr cid), .header go!"Content-Type" go!"application/json",
        .write (json.hashKVRespJSON crev kvh.Hash' kvh.CompactRevision' kvh.Revision')]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      iframe
      iright; iright; iright
      iframe
      ipureintro
      exact ⟨Hget, Hpath, Hcl, Or.inr (Or.inr ⟨Hlen, Hce, by
        rw [Hj]; exact Or.inr ⟨kvh, crev, HR', Or.inr rfl⟩⟩)⟩

end proof

end EtcdGrove
end Perennial
