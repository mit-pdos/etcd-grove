/- Lean-first (no Rocq counterpart).

# `Server`'s proof

`NewServeMux()`, the right to register on it (`muxOwnS_init`: Go 1.22's matcher, `maxSlice`'s value),
`HandleFunc("/echo", echo)` and `HandleFunc("/status", teapotHandler)` (literal patterns, function
values that are not `nil`: `functions_ne_nil`), the mux frozen with its two patterns (`muxAt`, an
invariant of `muxOwn`), `net.Listen` at `Addr` (the right to listen from `protoLis`'s `lisProto`,
`listen_lis_au`; a failure returns), the listener shared (`lisInv_alloc`), then `http.Serve` with the
mux as the handler of every request (`handlerOk`, from `ServeMux.ServeHTTP.spec` over the routes
`drvRoutes`: the patterns are `drvPats`, `WireLemmas.drvPats_ok`; the requests it answers itself are
the driver's (`drvP.hreq`), never redirected and answered `404` under no pattern (`DReq.route`,
`drvMuxNoRoute`); each handler's `handlerOk` from `handlerOk_func` and its spec).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Server
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.echo
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.teapotHandler
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas
public import Net.Spec.net.http.NewServeMux
public import Net.Spec.net.http.ServeMux__HandleFunc
public import Net.Spec.net.http.ServeMux__ServeHTTP
public import Net.Spec.net.http.Serve
public import Net.Proof.net.http.HandlerFuncOk
public import Net.Spec.net.Listen

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto HdrLine RespSt HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section pure
variable [GooseExts]

/-- The mux's routes, as `Server` registers them (latest first), `hS` and `hE` the handlers. -/
abbrev drvRoutes (hS hE : GoInterface) : List (GoString × GoInterface) :=
  [(go!"/status", hS), (go!"/echo", hE)]

theorem drvRoutes_pats (hS hE : GoInterface) :
    ∀ ph ∈ drvRoutes hS hE, net.http.litPattern ph.1 ∧ net.http.pathClean ph.1 := by
  intro ph hph
  apply drvPats_ok
  exact List.mem_map_of_mem (f := Prod.fst) hph

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The mux's own answers to the driver's requests: none is redirected, and one under no pattern is
answered `404`, which `drvRespEnd` allows. -/
theorem drvMuxNoRoute (hS hE : GoInterface) : net.http.muxNoRoute (drvP (GF := GF)) (drvRoutes hS hE) := by
  intro R τ _hR
  refine ⟨fun hred hs w0 => ⟨?_, ?_⟩, fun _hnred hnp => ⟨fun hs w0 hw => ?_, fun hs => ?_⟩⟩
  · simp only [drvP]
    iintro ⟨%B, %HdB, -⟩
    obtain ⟨d, hd, hj, rfl, -⟩ := HdB
    exact absurd hred (DReq.route d hd hj).1
  · simp only [drvP]
    iintro ⟨%B, %HdB, -⟩
    obtain ⟨d, hd, hj, rfl, -⟩ := HdB
    exact absurd hred (DReq.route d hd hj).1
  · simp only [drvP]
    iintro -
    imodintro
    ipureintro
    have := hw.length_le
    simp [net.http.notFoundBody] at this
    omega
  · simp only [drvP]
    iintro ⟨%B, -, #HgB⟩
    imodintro
    iexists B
    iframe HgB
    ipureintro
    refine ⟨fun _ h => absurd h (by decide), fun h => absurd (show net.http.pathUnder go!"/status" R.path from Or.inl h)
      (hnp _ List.mem_cons_self),
      fun _ _ => rfl⟩

theorem Server.wp_proof (wp_NewServeMux : net.http.NewServeMux.spec (GF := GF) (hG := hG))
    (wp_HandleFunc : net.http.ServeMux.HandleFunc.spec (GF := GF) (hG := hG))
    (wp_SH : net.http.HandlerFunc.ServeHTTP.spec (GF := GF) (hG := hG))
    (wp_MuxSH : net.http.ServeMux.ServeHTTP.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : net.http.Serve.spec (GF := GF) (hG := hG))
    (wp_echo : echo.spec (GF := GF) (hG := hG))
    (wp_teapot : teapotHandler.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro ms
  wp_start as ⟨%Hb, #Hu, #Hms, #Henv, #Hlis⟩
  ihave #Hhttp : isPkgInit (PROP := IProp GF) pkg_id.net.http $$ []
  · iPkgInit
  ihave #Henv2 := Henv
  iunfold net.http.httpSrvEnv at Henv2
  icases Henv2 with ⟨-, -, #Hse, -⟩
  have hne : ∀ (f : GoString) (impl : val) [FuncUnfold f [] impl] (x : Binder) (e : Expr),
      impl = RecV BAnon x e → x ≠ BAnon → functions f [] ≠ func.nil := by
    intro f impl _ x e himpl hx h
    have h2 : (#(functions f []) : val) = impl := func_unfold
    rw [h, himpl] at h2
    have h3 : (#(func.nil : GoFunc) : val) = RecV BAnon BAnon (Val (LitV LitPoison)) :=
      (recv_eq_func_mk BAnon BAnon (Val (LitV LitPoison))).symm
    rw [h3] at h2
    cases h2
    exact hx rfl
  have hE : functions echo [] ≠ func.nil := hne echo echo.impl "w" _ rfl (by intro h; cases h)
  have hT : functions teapotHandler [] ≠ func.nil :=
    hne teapotHandler teapotHandler.impl "w" _ rfl (by intro h; cases h)
  try wp_auto
  wp_apply wp_NewServeMux as %m Hm
  iapply fupd_wp
  imod (net.http.muxOwnS_init (GF := GF) (hG := hG) (E := ⊤) m false ms Hb) $$ Hm Hu Hms
    with Hown
  imodintro
  try wp_auto
  wp_apply (wp_HandleFunc m [] go!"/echo" (functions echo []) (by unfold net.http.litPattern; decide) (by simp) hE) $$ [Hown]
    as ⟨Hown, #HrE⟩
  · iunfold net.http.muxOwn
    iframe Hown
    iexact Hse
  try wp_auto
  wp_apply (wp_HandleFunc m [go!"/echo"] go!"/status" (functions teapotHandler [])
      (by unfold net.http.litPattern; decide) (by decide) hT) $$ [$Hown] as ⟨Hown, #HrS⟩
  try wp_auto
  -- the mux frozen with its two patterns
  iapply fupd_wp
  imod (inv_alloc (net.http.muxFrozenN m) ⊤
      (net.http.muxOwn (GF := GF) (hG := hG) m [go!"/status", go!"/echo"])) $$ [Hown] with #Hat
  · inext; iexact Hown
  imodintro
  -- listen at `Addr`
  ihave #Hlis2 := Hlis
  iunfold net.http.protoLis at Hlis2
  icases Hlis2 with ⟨#Hlp, -⟩
  ihave #Hlp2 := Hlp
  iunfold lisProto at Hlp2
  icases Hlp2 with ⟨-, -, %Hok⟩
  rw [show (Addr : val) = #addrS from rfl]
  wp_apply wp_Listen go!"tcp" net.tcpNet_tcp addrS as %lv %lerr Hl
  · isplitr
    · ipureintro; exact Hok
    iapply listen_lis_au (Gg := hG.goose_globalGS) addrS _ _ $$ Hlp
  icases Hl with (⟨%He, %l, #Hli, Hnl, #Hon⟩ | ⟨%x, -, #Hre⟩)
  rotate_left
  · ihave %Hne := net.resErr_netErr $$ Hre
    have hne := net.netErr_ne_nil (Hne.2 (by simp))
    rcases lerr with ei | _
    · try wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl hne
  subst He
  try wp_auto
  iapply fupd_wp
  imod (lisInv_alloc ⊤ _ l addrS true) $$ Hnl with #Hinv
  imodintro
  wp_apply (wp_Serve drvP addrS lv (interface.mkOk (go.GoType.PointerType net.http.ServeMux.ty) #m) l)
    $$ [] as %e3 -
  · iframe Henv Hlis Hli Hon Hinv
    iunfold net.http.handlerOk
    iexists ⟨go.GoType.PointerType net.http.ServeMux.ty, #m⟩
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %w %r %R %τ %rd %I %S %E %HS Hpre
    iapply (wp_MuxSH m (drvRoutes (interface.mkOk net.http.HandlerFunc.ty #(functions teapotHandler []))
      (interface.mkOk net.http.HandlerFunc.ty #(functions echo []))) drvP go!"/" w r R τ rd I S E
      (drvRoutes_pats _ _) (drvMuxNoRoute _ _) HS)
    isplitr
    · ipureintro; exact Hb
    isplitr
    · iexact Hhttp
    isplitr
    · iexact Hu
    isplitr
    · simp only [drvRoutes, List.map_cons, List.map_nil]
      iunfold net.http.muxAt
      iexact Hat
    isplitr
    · iapply BigSepL.bigSepL_cons.2
      isplitr
      · isplitr
        · iexact HrS
        iapply (net.http.handlerOk_func wp_SH (functions teapotHandler []) drvP go!"/status")
        imodintro
        iintro %w' %r' %R' %τ' %rd' %I' %S' %E' %HS' Hpre'
        iapply (wp_teapot w' r' R' τ' rd' I' S' E' HS')
        iframe Hpre'
        iexact Hpkg
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · isplitr
        · iexact HrE
        iapply (net.http.handlerOk_func wp_SH (functions echo []) drvP go!"/echo")
        imodintro
        iintro %w' %r' %R' %τ' %rd' %I' %S' %E' %HS' Hpre'
        iapply (wp_echo w' r' R' τ' rd' I' S' E' HS')
        iframe Hpre'
        iexact Hpkg
      iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
      itrivial
    · iexact Hpre
  try wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
