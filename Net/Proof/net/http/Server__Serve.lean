/-
The proof of `Server.Serve` (`Net/Spec/net/http/Server__Serve.lean`) over its body: the listener
wrapped in an `onceCloseListener` (closed by the deferred `Close`, `wp_oclClose`), HTTP/2 not
configured (`wp_setupHTTP2_Serve`), the listener tracked (`wp_trackListener_add`/`_remove`), the base
context `Background()` with the server under `ServerContextKey` (`context.WithValue.specPtr`); the
loop's invariant is the tracking's `ownDone`, the deferred calls and the retry delay. Each `Accept`
(through the `onceCloseListener`'s promoted method, `net.Listener.Accept.spec` with
`accept_addrs_shared_rdl_au` at the address dialed) gives a connection, made (`wp_newConn`,
`connNew_alloc`), marked `StateNew` (`wp_setState`) and served by `conn.serve` in a goroutine of its
own (`wp_fork_tok_body`); or an error (an `*OpError`): `Temporary()` (`OpError.Temporary.spec`)
true, it is logged (`wp_logf_argOk`) and the loop sleeps and retries; else `Serve` returns it.
-/
module

public import Net.Spec.net.http.Server__Serve
public import Net.Spec.net.http.conn__serve
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Listener__Close
public import Net.Spec.net.OpError__Temporary
public import Net.Spec.context.WithValuePtr
public import Net.Proof.net.http.ServeLoopLemmas
public import Net.Proof.net.AtAddr
public import Net.Proof.net.rpc.Errs
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS] [net.Assumptions] [log.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.Serve.wp_proof
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Close : net.Listener.Close.spec (GF := GF) (hG := hG))
    (wp_Temporary : net.OpError.Temporary.spec (GF := GF) (hG := hG))
    (wp_WithValue : context.WithValue.specPtr (GF := GF) (hG := hG))
    (wp_serve : conn.serve.spec (GF := GF) (hG := hG)) :
    Server.Serve.spec (GF := GF) (hG := hG) := by
  intro s lis l la P Q path hpath hlen
  wp_start as ⟨#Henv, #Hre, #Hse, #Hctxi, #Hlogi, #Hsc, #Hsd, #Hss, Hrest, #Hkeys, #Hwp, #Hrp,
    #Htm, #Haddrs, #Hlis, #Hon, #Hli⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold net.isListener at Hlis
  icases Hlis with ⟨%tl, %x, %Hlis, #HlisAt⟩
  subst Hlis
  have h2c : go.typeSetContains (go.GoType.PointerType net.TCPListener.ty)
      http2ExternalServerConfig.ty = false := by
    go_type_set
  simp only [h2c]
  try wp_auto
  iunfold serveEnv at Hse
  icases Hse with ⟨#Hth, -⟩
  try wp_auto
  wp_apply (IntoValTyped.wp_alloc (V := net.http.onceCloseListener)
    (t := net.http.onceCloseListener.ty)) as %oc Hoc
  try wp_auto
  iunfold srvServeRest at Hrest
  icases Hrest with ⟨#Htls, #Hbc, #Hcc, #Hel, Honce, Hnpe, Hlg⟩
  wp_apply wp_setupHTTP2_Serve $$ [$Htls $Honce $Hnpe] as Hnpe
  try wp_auto
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ Hlg with ⟨%γwg, Hwg⟩
  imod sync.join.init _ γwg $$ Hwg with Hadd
  wp_apply wp_trackListener_add $$ [$Hsc $Hss $Hadd] as Hdone
  try wp_auto
  wp_apply context.wp_Background
  try wp_auto
  ihave #Hk := Hkeys
  iunfold ctxKeys at Hk
  icases Hk with ⟨%sk, %lk, #Hsk, #Hlk⟩
  try wp_auto
  wp_apply wp_WithValue _ contextKey.ty sk _ $$ [$Hctxi] as %q ⟨#Hq1, #Hq2, #Hq3⟩
  try wp_auto
  ihave #Hbg : context.ctxBg (GF := GF)
      (interface.mk (go.GoType.PointerType context.valueCtx.ty) #q) $$ []
  · iunfold context.ctxBg
    iexists 1
    simp only [context.ctxBgN]
    iright
    iexists q, context.backgroundCtxVal, (interface.mk (go.GoType.PointerType contextKey.ty) #sk), _
    iframe #
    ipureintro; exact ⟨rfl, rfl⟩
  -- the onceCloseListener's fields
  icases typedPointsto_split _ _ _ $$ Hoc with Hoc
  simp only [TypedPointsto.typedPointstoDef, named]
  icases Hoc with ⟨HocL, HocO, HocE, -⟩
  ipersist HocL
  imod sync.init_Once (structFieldRef net.http.onceCloseListener go!"once" oc)
    iprop(structFieldRef net.http.onceCloseListener go!"closeErr" oc ↦ (interface.nil : GoInterface))
    iprop(∃ e : GoInterface, structFieldRef net.http.onceCloseListener go!"closeErr" oc ↦□ e) ⊤
    $$ [HocO HocE] with #HocOnce
  · iframe HocO HocE
  ihave #Hocl : oclOnce (GF := GF) oc $$ [HocOnce]
  · iunfold oclOnce; iexact HocOnce
  iclear HocOnce
  -- the accepted addresses' protocols
  ihave #Hap : □ (∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ →
      addrProto (Gg := hG.goose_globalGS) a (P a) (Q a)) $$ [Haddrs]
  · imodintro
    iintro %a %ha
    ihave Ha := Haddrs $$ %a %ha
    iunfold srvAddr at Ha
    icases Ha with ⟨-, Hp, -⟩
    iexact Hp
  ihave HI : (∃ td : w64, tempDelay_ptr ↦ td) $$ [tempDelay]
  · iexists _; iexact tempDelay
  wp_for HI
  rw [method_unfold (t := go.GoType.PointerType net.http.onceCloseListener.ty) (m := go!"Accept")]
  try wp_auto
  wp_apply wp_Accept tl l x la (fun _ => iprop(True))
      (fun a cn => iprop(connEnd (Gg := hG.goose_globalGS) cn true (Q a) (P a) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true ∗ rdlTok (Gg := hG.goose_globalGS) cn true false))
      $$ [$HlisAt $Hon]
    as %c %err (⟨%Herr, %cn, %a, %Ha, #Hc, Hend, Hfr, Hrdl⟩ | ⟨%k, -, #HE⟩)
  · iapply accept_addrs_shared_rdl_au la P Q $$ Hap Hli
  · -- a connection
    subst Herr
    iunfold net.isConn at Hc
    icases Hc with ⟨%t, %la', %ra, %Hct, #Hca⟩
    subst Hct
    try wp_auto
    wp_apply wp_newConn s t as %cc ⟨%hcn, Hcv⟩
    imod connNew_alloc cc s t $$ Hcv with Hcn
    iunfold connNew at Hcn
    icases Hcn with ⟨#Hsrv, #Hrwc, Hccx, Hra, Htls', Hwerr, Hr, Hbr, Hbw, Hlm, Hcr, Hcs, Hmu, Hhj⟩
    try wp_auto
    wp_apply wp_setState cc s _ (W64 0) ⟨by decide, by decide⟩ $$ [$Hsrv $Hsc $Hcs] as Hcs
    try wp_auto
    ihave #Hsa := Haddrs $$ %a %Ha
    iunfold srvAddr at Hsa
    icases Hsa with ⟨%hQ, -, ⟨%Z, #Hhl, #Hzl⟩, #Hbad, #Hh⟩
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    wp_bind (Fork _)
    iapply wp_fork_tok_body $$ [Hsend Hrecv Hfr Hrdl Hccx Hra Htls' Hwerr Hr Hbr Hbw Hlm Hcr Hcs Hmu Hhj]
    · inext
      iintro Htok
      wp_apply wp_serve cc s t cn a la' ra (P a) (Q a) Z path
          (interface.mk (go.GoType.PointerType context.valueCtx.ty) #q) hcn hpath hlen hQ
        $$ [$Henv $Hre $Hctxi $Hsc $Hsd $Hss $Hkeys $Hwp $Hrp $Htm $Hbg $Hca $Hsend $Hrecv $Hfr $Hrdl
          $Hhl $Hzl $Htok Hccx Hra Htls' Hwerr Hr Hbr Hbw Hlm Hcr Hcs Hmu Hhj] as Htok
      · isplitl [Hccx Hra Htls' Hwerr Hr Hbr Hbw Hlm Hcr Hcs Hmu Hhj]
        · iunfold connNew; iframe Hsrv Hrwc; iframe
        isplitr
        · iapply Hbad
        iapply Hh
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    inext
    try wp_auto
    wp_for_post
    iframe
    iexists _; iexact HI
  · -- `Accept` failed
    iunfold net.resErr at HE
    icases HE with ⟨%e, Hop, -⟩
    iunfold net.opErr at Hop
    icases Hop with ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩
    subst Herr
    try wp_auto
    wp_apply wp_shuttingDown $$ [$Hss]
    try wp_auto
    have hne : go.typeSetContains (go.GoType.PointerType net.OpError.ty) net.Error.ty = true := by
      go_type_set
    simp only [hne]
    try wp_auto
    wp_apply wp_Temporary pe _ $$ [$Hpe] as %b -
    cases b
    · -- not temporary: `Serve` returns the error
      try wp_auto
      wp_for_post
      wp_apply wp_trackListener_remove $$ [$Hsc $Hdone]
      try wp_auto
      wp_apply wp_oclClose wp_Close oc tl l x la $$ [$Hocl $HocL $HlisAt $Hon $Hli] as %cerr -
      try wp_auto
      iapply HΦ; itrivial
    · -- temporary: logged, a sleep, and the loop again
      wp_auto
      wp_if_destruct
      all_goals try wp_auto
      all_goals try wp_if_destruct
      all_goals try wp_auto
      all_goals (
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        rw [show ∀ (a b c : GoInterface), [a, b].set (sint.nat (W64 (0 + 1))) c = [a, c] from
          fun _ _ _ => rfl]
        try wp_auto
        wp_apply wp_logf_accept $$ [$Hlogi $Hel $Hpe $Hsl]
        try wp_auto
        wp_apply time.wp_Sleep
        try wp_auto
        wp_for_post
        iframe
        iexists _; iexact HI)


end proof

end net.http
end Perennial
