/- Lean-first (no Rocq counterpart).

# `echo`'s proof

The request is one of the driver's under `/echo` (`servePre`'s `pathUnder`, `pathUnder_lit`; `drvP.hreq`):
an `/echo` request `(m, v, b)`. `io.ReadAll(r.Body)` (`io.ReadAll.spec` over `bodyOps`' reader): on an
error, `WriteHeader(500)` (an answer `drvRespEnd` allows on `/echo`); at `io.EOF`, the body read is the
request's (`bodyOps`' evidence, `drvP.body`, agrees with `drvP.hreq`'s `dghostVar`: it is `b`). Then three
`w.Header().Set(..)` (`respOps`' `Header`, `Header.Set.spec`) with the method, `r.URL.Path` and
`r.Header.Get("X-Driver")` (`srvReq`, `Header.Get.spec_ro`), `WriteHeader(200)` (`echoHdrs_ok`), and
`Write(body)`: the complete answer `drvRespEnd` asks for, or a failed writer.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.echo
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.HandlerOps
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas
public import Net.Spec.net.http.Header__Get
public import Net.Spec.net.http.Header__Set
public import Perennial.Spec.io.ReadAll

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto HdrLine RespSt HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem echo.wp_proof (wp_ReadAll : io.ReadAll.spec (GF := GF) (hG := hG))
    (wp_Set : net.http.Header.Set.spec (GF := GF) (hG := hG))
    (wp_GetRO : net.http.Header.Get.spec_ro (GF := GF) (hG := hG)) :
    echo.spec (GF := GF) (hG := hG) := by
  intro w r R τ rd I S E HSb
  iintro ⟨#Hpkg, Hpre⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave ⟨%eof, #Heof⟩ : (∃ eof : GoInterface, globalAddr io.EOF ↦□ eof : IProp GF) $$ []
  · ihave #Hn := io.eof_of_init $$ Hio
    isimp only [_root_.Perennial.errors.newVar] at Hn
    icases Hn with ⟨%eofl, #Heof, -⟩
    iexists _
    iexact Heof
  iunfold net.http.servePre at Hpre
  icases Hpre with ⟨%Hp, #Hsr, -, #Hhreq, #Hops, HI, #Hbody, HS0, Htok⟩
  obtain ⟨-, -, Hunder, -⟩ := Hp
  have Hpath : R.path = go!"/echo" := pathUnder_lit _ _ (by decide) Hunder
  isimp only [drvP] at Hhreq
  icases Hhreq with ⟨%B, %HdB, #HgB⟩
  obtain ⟨d, hd, hj, hR, hB⟩ := HdB
  obtain ⟨m, v, b, rfl⟩ : ∃ m v b, d = .echo m v b := by
    cases d with
    | echo m v b => exact ⟨m, v, b, rfl⟩
    | status =>
      exfalso; rw [hR] at Hpath
      exact absurd Hpath (by decide)
    | nope w0 =>
      exfalso; rw [hR] at Hpath
      have h1 := congrArg List.length Hpath
      simp only [DReq.hreq, List.length_append] at h1
      have h2 : (go!"/nope/" : GoString).length = 6 := rfl
      have h3 : (go!"/echo" : GoString).length = 5 := rfl
      omega
    | junk => exact absurd rfl hj
  obtain ⟨hm, hv, hb⟩ := hd
  subst hR
  subst B
  have hRx : net.http.hdrGetL (DReq.echo m v b).hreq.hdr go!"X-Driver" = v := by
    simp [DReq.hreq, net.http.hdrGetL]
  have hst200 : 200 ≤ uint.nat (W64 200) ∧ uint.nat (W64 200) ≤ 999 ∧
      net.http.bodyAllowed (W64 200) = true ∧ net.http.hdrsOk (echoHdrs m v) :=
    ⟨by word, by word, by unfold net.http.bodyAllowed; decide, echoHdrs_ok m v hm hv⟩
  have hst500 : 200 ≤ uint.nat (W64 500) ∧ uint.nat (W64 500) ≤ 999 ∧
      net.http.bodyAllowed (W64 500) = true ∧ net.http.hdrsOk [] :=
    ⟨by word, by word, by unfold net.http.bodyAllowed; decide, hdrsOk_nil⟩
  iunfold net.http.srvReq at Hsr
  icases Hsr with ⟨#Hmeth, ⟨%u, #Hurl, #Hu⟩, -, -, -, -, -, ⟨%hm0, #Hhm, #Hro⟩, #Hbd, -⟩
  ihave Hu2 := Hu
  iStructNamedPrefix Hu2 "U"
  ihave #Hops2 := Hops
  iunfold net.http.respOps at Hops2
  icases Hops2 with ⟨%wi, %Hw, -, -, -⟩
  subst Hw
  iunfold net.http.bodyOps at Hbody
  icases Hbody with ⟨%ri, %Hri, #Hrd, #Hev⟩
  subst Hri
  wp_func_call
  wp_auto
  wp_apply (wp_ReadAll ri S E [] eof HSb) $$ [$HS0 $Hrd $Heof] as %sl %err ⟨%ys, Hsl, HS, Hres⟩
  icases Hres with (⟨%He, #HE⟩ | ⟨⟨%He1, %He2⟩, #HE⟩)
  · -- the whole body
    subst He
    ihave ⟨-, Hk⟩ := Hev $$ %([] ++ ys) %eof HE
    ihave #HgY := Hk $$ Heof
    isimp only [drvP] at HgY
    ihave %Hag := dghostVar_agree τ _ DFrac.discard ([] ++ ys) DFrac.discard $$ HgB HgY
    try wp_auto
    wp_apply (wp_resp_Header wi (DReq.echo m v b).hreq τ drvP I [] [] true) $$ [HI] as %h1 ⟨Hh1, Hb1⟩
    · iframe HI; iexact Hops
    wp_apply (wp_Set h1 [] go!"X-Method" m (by decide)) $$ [$Hh1] as Hh1
    ihave HI := Hb1 $$ Hh1
    try wp_auto
    wp_apply (wp_resp_Header wi (DReq.echo m v b).hreq τ drvP I _ [] true) $$ [HI] as %h2 ⟨Hh2, Hb2⟩
    · iframe HI; iexact Hops
    wp_apply (wp_Set h2 _ go!"X-Path" go!"/echo" (by decide)) $$ [$Hh2] as Hh2
    ihave HI := Hb2 $$ Hh2
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply (wp_GetRO hm0 (DReq.echo m v b).hreq.hdr go!"X-Driver" (by decide)) $$ [$Hro]
    rw [echoReq_xdriver]
    wp_apply (wp_resp_Header wi (DReq.echo m v b).hreq τ drvP I _ [] true) $$ [HI] as %h3 ⟨Hh3, Hb3⟩
    · iframe HI; iexact Hops
    wp_apply (wp_Set h3 _ go!"X-Echo" v (by decide)) $$ [$Hh3] as Hh3
    ihave HI := Hb3 $$ Hh3
    rw [echoHdrs_eq m v]
    try wp_auto
    wp_bind (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #(W64 200)))
    iapply (wp_resp_WriteHeader wi (DReq.echo m v b).hreq τ drvP I (echoHdrs m v) [] true (W64 200)
        hst200) $$ [HI]
    · iframe HI
      isplitr
      · iexact Hops
      imodintro
      simp only [drvP]
      ipureintro; simp
    inext
    iintro HI
    try wp_auto
    wp_apply (wp_resp_Write wi (DReq.echo m v b).hreq τ drvP I (some (W64 200)) (echoHdrs m v) [] true sl ys
        (DFrac.own 1) (fun h => by cases h)) $$ [HI Hsl] as %n %err ⟨Hsl, Hres⟩
    · iframe HI Hsl
      isplitr
      · iexact Hops
      simp only [drvP]
      imodintro; ipureintro
      rw [← Hag]; exact hb.1
    try wp_auto
    isplitr
    · ipureintro; left; rfl
    iunfold net.http.serveDone
    isplitl [Htok]
    · iexact Htok
    isplitl [HS]
    · iexists _; iexact HS
    icases Hres with (⟨%He, HI⟩ | ⟨%bs', HI⟩)
    · ileft
      iexists (W64 200), (echoHdrs m v), ([] ++ ys)
      simp only [Option.getD_some]
      iframe HI
      simp only [drvP]
      imodintro
      iexists (DReq.echo m v b).body
      iframe HgB
      ipureintro
      obtain ⟨g1, g2, g3⟩ := echoHdrs_get m v
      refine ⟨fun _ _ => ⟨g1, g2, g3.trans hRx.symm, Hag.symm⟩,
        fun h => absurd h (show ¬ ((go!"/echo" : GoString) = go!"/status") by decide),
        fun h _ => (h rfl).elim⟩
    · iright; ileft
      iexists _, _, _
      iexact HI
  · -- an error: `500`
    cases err with
    | nil => exact absurd rfl He1
    | ok ei =>
    try wp_auto
    wp_bind (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #(W64 500)))
    iapply (wp_resp_WriteHeader wi (DReq.echo m v b).hreq τ drvP I [] [] true (W64 500)
        hst500) $$ [HI]
    · iframe HI
      isplitr
      · iexact Hops
      imodintro
      simp only [drvP]
      ipureintro; simp
    inext
    iintro HI
    try wp_auto
    isplitr
    · ipureintro; left; rfl
    iunfold net.http.serveDone
    isplitl [Htok]
    · iexact Htok
    isplitl [HS]
    · iexists _; iexact HS
    ileft
    iexists (W64 500), [], []
    iframe HI
    simp only [drvP]
    imodintro
    iexists (DReq.echo m v b).body
    iframe HgB
    ipureintro
    exact ⟨fun _ h => absurd h (by decide),
      fun h => absurd h (show ¬ ((go!"/echo" : GoString) = go!"/status") by decide),
      fun h _ => (h rfl).elim⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
