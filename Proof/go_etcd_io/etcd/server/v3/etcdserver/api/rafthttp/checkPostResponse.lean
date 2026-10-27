/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/checkPostResponse.lean` (rafthttp
stage 6e, 2026-10-24). Lean-first. The status switch (as `streamReader.dial`'s): `412` and the
body naming `errIncompatibleVersion` or `ErrClusterIDMismatch` (each logged), or an `Errorf`
error; `403` `errMemberRemoved`; `204` `nil`; any other status an `Errorf` error. The errors other
than `errMemberRemoved` are told from it by their `errorString`'s cell (`errStrCell`: a package
variable's, from rafthttp's facts, or `Errorf`'s, whose message begins with its format's text).
-/
module

public import Proof.strings.TrimSuffixAny
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkPostResponse
public import Spec.strings.TrimSuffix
public import Spec.fmt.ErrorfPlain
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Codec

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [ErrorStringLeaf]

/-- An `errors.New` error whose cell holds a message other than `errMemberRemoved`'s is a post's
leaf error (`postErr`). -/
theorem postErr_errorString (st : w64) (x xR : Loc) (m mR : GoString) (hm : m ≠ mR) :
    ⊢ (□ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }}) -∗
      errStrCell x m -∗
      globalAddr rafthttp.errMemberRemoved ↦□
        interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xR -∗
      errStrCell xR mR -∗
      postErr st (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #HM #Hc #Hg #HcR
  iunfold postErr
  isplitr
  · iapply errorString_errStrOk $$ HM
  iright; iright
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; exact ⟨rfl, errorString_leaf x⟩
  imodintro
  iintro %eR #HeR
  icombine Hg HeR gives %Heq
  subst Heq
  ihave %Hne := errStrCell_ne x xR m mR hm $$ Hc HcR
  ipureintro
  intro he
  apply Hne
  injection he with h1
  injection h1 with _ hv
  exact go.intoVal_inj (V := Loc) hv

set_option hygiene false in
/-- A log call (`lg.Error(...)`): its fields' strings, the call. -/
local macro "zap_log" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply hIDStringPtr _ (DFrac.own 1) _ $$ [«to»] as %_ ⟨«to», -⟩; iframe; iframe #)
    | (wp_apply hZString as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply hError lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
    | wp_auto)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.checkPostResponse.wp_proof
    (hTrim : strings.TrimSuffix.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.ErrorfPlain.spec (GF := GF) (hG := hG))
    (hError : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hHeaderGetPtr : http.HeaderGetPtr_spec (GF := GF))
    (hHeaderGetOwnPtr : http.HeaderGetOwnPtr_spec (GF := GF))
    (hStatusText : http.StatusText_spec (GF := GF))
    (hURLString : http.URLStringAny_spec (GF := GF))
    (hReqURL : http.reqURL_spec (GF := GF)) :
    rafthttp.checkPostResponse.spec (GF := GF) (hG := hG) := by
  intro lg resp st rd b bs req R to Hd Hlgnn
  wp_start as ⟨Hresp, Hb, Hreq⟩
  -- the errors' facts and cells (rafthttp's)
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, #HIV, #HCM, -, #HMR, -, -, -, -, -, -, -, -, -, -, -,
    #Hcells, -⟩
  iunfold EtcdGrove.errorsNewVar at HIV HCM HMR
  icases HIV with ⟨%xIV, #HxIVg, #HxIVM⟩
  icases HCM with ⟨%xCM, #HxCMg, #HxCMM⟩
  icases HMR with ⟨%xMR, #HxMRg, #HxMRM⟩
  simp only [EtcdGrove.errVarCells, EtcdGrove.errVarCell] at *
  icases Hcells with ⟨⟨%cIV, #HcIVg, #HcIV⟩, ⟨%cCM, #HcCMg, #HcCM⟩, ⟨%cMR, #HcMRg, #HcMR⟩, -⟩
  icombine HxIVg HcIVg gives %h1
  icombine HxCMg HcCMg gives %h2
  icombine HxMRg HcMRg gives %h3
  have e1 : xIV = cIV := by injection h1 with h1; injection h1 with _ h1; exact go.intoVal_inj (V := Loc) h1
  have e2 : xCM = cCM := by injection h2 with h2; injection h2 with _ h2; exact go.intoVal_inj (V := Loc) h2
  have e3 : xMR = cMR := by injection h3 with h3; injection h3 with _ h3; exact go.intoVal_inj (V := Loc) h3
  subst e1 e2 e3
  iunfold http.respAt at Hresp
  icases Hresp with ⟨#Hst, ⟨%rhm, %rhs, #Hrhf, #Hrh, %Hrhd⟩, #Hbody, %Hrdnn⟩
  iunfold http.reqOwn at Hreq
  icases Hreq with ⟨%qhm, #Hqhf, Hqh, Hqrest⟩
  ihave #Htyp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hfpkg : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hstrp : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  by_cases h412 : st = W64 412
  · -- a precondition failed: the body says which
    subst h412
    (try wp_auto)
    wp_apply wp_bytes_to_string _ _ _ $$ [Hb] as Hb
    · iframe Hb
    wp_apply (strings.TrimSuffix.any hTrim _ _) as %ts -
    (try wp_auto)
    wp_apply HxIVM
    (try wp_auto)
    by_cases hiv : ts = go!"incompatible version"
    · rw [_root_.decide_eq_true hiv]
      (try wp_auto)
      rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
      zap_log
      iapply HΦ
      iapply (postErr_errorString _ _ _ _ _ (by decide)) $$ HxIVM HcIV HxMRg HcMR
    rw [_root_.decide_eq_false hiv]
    (try wp_auto)
    wp_apply HxCMM
    (try wp_auto)
    by_cases hcm : ts = go!"cluster ID mismatch"
    · rw [_root_.decide_eq_true hcm]
      (try wp_auto)
      rw [_root_.decide_eq_false (show ¬ lg = null from Hlgnn)]
      zap_log
      wp_apply hHeaderGetPtr _ rhm rhs _ $$ []
      · iframe #
      zap_log
      wp_apply hHeaderGetOwnPtr _ qhm _ _ $$ [Hqh] as Hqh
      · iframe Hqh; iframe #
      zap_log
      iapply HΦ
      iapply (postErr_errorString _ _ _ _ _ (by decide)) $$ HxCMM HcCM HxMRg HcMR
    -- another body
    rw [_root_.decide_eq_false hcm]
    (try wp_auto)
    wp_apply wp_bytes_to_string _ _ _ $$ [Hb] as Hb
    · iframe Hb
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ (by decide) $$ [Hasl] as %x ⟨-, %msg, #Hc, %Hpre, #HE⟩
    · iframe #; iframe Hasl
      simp only [fmt.argsOk, fmt.argOk]
      isplitr
      · ileft; ipureintro
        apply fmt.argWf_of_argsWf
        exact .cons_string _ _ .nil
      itrivial
    iapply HΦ
    iapply (postErr_errorString _ _ _ msg _ (fun h => by subst h; exact absurd Hpre (by decide)))
      $$ HE Hc HxMRg HcMR
  rw [_root_.decide_eq_false (show ¬ st = W64 412 from h412)]
  (try wp_auto)
  by_cases h403 : st = W64 403
  · -- the member removed: `errMemberRemoved`
    subst h403
    (try wp_auto)
    iapply HΦ
    iunfold postErr
    isplitr
    · iapply errorString_errStrOk $$ HxMRM
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexact HxMRg
  rw [_root_.decide_eq_false (show ¬ st = W64 403 from h403)]
  (try wp_auto)
  by_cases h204 : st = W64 204
  · subst h204
    (try wp_auto)
    iapply HΦ
    iunfold postErr
    isplitr
    · iapply http.errStrOk_nil
    ileft; ipureintro; rfl
  rw [_root_.decide_eq_false (show ¬ st = W64 204 from h204)]
  (try wp_auto)
  -- another status: its text and the request's URL
  wp_apply (hStatusText _) as %stt -
  (try wp_auto)
  ihave ⟨Hqrest, %up, %u, #Hupf, #Hu⟩ := hReqURL req _ $$ Hqrest
  (try wp_auto)
  wp_apply (hURLString up DFrac.discard u) $$ [] as %us -
  · iexact Hu
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply hErrorf _ _ _ _ (by decide) $$ [Hasl] as %x ⟨-, %msg, #Hc, %Hpre, #HE⟩
  · iframe #; iframe Hasl
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, List.set_cons_succ, List.set_cons_zero,
      fmt.argsOk, fmt.argOk]
    isplitr
    · ileft; ipureintro
      apply fmt.argWf_of_argsWf
      exact .cons_string _ _ .nil
    isplitr
    · ileft; ipureintro
      apply fmt.argWf_of_argsWf
      exact .cons_string _ _ .nil
    itrivial
  iapply HΦ
  iapply (postErr_errorString _ _ _ msg _ (fun h => by subst h; exact absurd Hpre (by decide)))
    $$ HE Hc HxMRg HcMR

end proof

end EtcdGrove
end Perennial
