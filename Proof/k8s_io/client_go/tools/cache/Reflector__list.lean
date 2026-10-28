/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__list.lean`, over the pager's proofs and the
boundary hypotheses of `meta` (pending approval) and `isTooLargeResourceVersionError` (pending).
Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__list
public import Spec.k8s_io.client_go.tools.cache.Reflector__relistResourceVersion
public import Spec.k8s_io.client_go.tools.cache.Reflector__setIsLastSyncResourceVersionUnavailable
public import Spec.k8s_io.client_go.tools.cache.Reflector__setLastSyncResourceVersion
public import Spec.k8s_io.client_go.tools.cache.Reflector__syncWith
public import Spec.k8s_io.client_go.tools.cache.isExpiredError
public import Spec.k8s_io.client_go.tools.cache.isTooLargeResourceVersionError
public import Spec.k8s_io.client_go.tools.cache.isUnsupportedTableListObject
public import Spec.k8s_io.client_go.tools.pager.New
public import Spec.k8s_io.client_go.tools.pager.SimplePageFunc
public import Spec.k8s_io.client_go.tools.pager.ListPager__ListWithAlloc
public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import Spec.k8s_io.apimachinery.pkg.api.meta.ExtractListWithAlloc
public import Spec.k8s_io.apimachinery.pkg.api.meta.LenList
public import Spec.k8s_io.utils.trace.New
public import Spec.k8s_io.utils.trace.Trace__LogIfLong
public import Spec.k8s_io.utils.trace.Trace__Step
public import Perennial.Proof.context.Background
public import Perennial.Golang.Theory.Defer
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ClientLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel informer

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The reflector's list options (`metav1.ListOptions{ResourceVersion: rv}`). -/
abbrev listOpts (rv : GoString) : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions :=
  { (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) with ResourceVersion' := rv }

set_option maxHeartbeats 3200000 in
theorem Reflector.list.wp_proof
    (wp_relistResourceVersion : Reflector.relistResourceVersion.spec (GF := GF) (hG := hG))
    (wp_setUnavailable :
      Reflector.setIsLastSyncResourceVersionUnavailable.spec (GF := GF) (hG := hG))
    (wp_setLastSyncResourceVersion : Reflector.setLastSyncResourceVersion.spec (GF := GF) (hG := hG))
    (wp_syncWith : Reflector.syncWith.spec (GF := GF) (hG := hG))
    (wp_isExpiredError : isExpiredError.spec (GF := GF) (hG := hG))
    (wp_isTooLarge : isTooLargeResourceVersionError.spec (GF := GF) (hG := hG))
    (wp_isUnsupported : isUnsupportedTableListObject.spec (GF := GF) (hG := hG))
    (wp_pagerNew : pager.New.spec (GF := GF) (hG := hG))
    (wp_SimplePageFunc : pager.SimplePageFunc.spec (GF := GF) (hG := hG))
    (wp_ListWithAlloc : pager.ListPager.ListWithAlloc.spec (GF := GF) (hG := hG))
    (wp_ListAccessor : apimeta.ListAccessor.spec (GF := GF) (hG := hG))
    (wp_Extract : apimeta.ExtractListWithAlloc.spec (GF := GF) (hG := hG))
    (wp_LenList : apimeta.LenList.spec (GF := GF) (hG := hG))
    (wp_traceNew : trace.New.spec (GF := GF) (hG := hG))
    (wp_LogIfLong : trace.Trace.LogIfLong.spec (GF := GF) (hG := hG))
    (wp_Step : trace.Trace.Step.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    Reflector.list.spec (GF := GF) (hG := hG) := by
  intro r f lw et dh ctx dch γd γa cfg res γf γt γi n
  wp_start as ⟨#Hfix, #Henv, #Hctx, Hst⟩
  iunfold reflSt at Hst
  icases Hst with ⟨%v, %u, %σ0, Hown, Hmisc, Hlast, #Hσ0, %hrv⟩
  ihave #Henv2 := Henv
  iunfold reflEnv at Henv2
  icases Henv2 with ⟨#Hinv, #Hfifo, #Hlw, #Hty, #Hkeys⟩
  iunfold lwOk at Hlw
  icases Hlw with ⟨#HList, #HWatch⟩
  ihave #Hctx2 := Hctx
  iunfold stableCtx at Hctx2
  icases Hctx2 with ⟨#HDone, #HErr, #Hdch⟩
  iunfold reflFixed at Hfix
  icases Hfix with ⟨#Hf1, #Hf2, #Hdh⟩
  iunfold reflFixed1 at Hf1
  icases Hf1 with ⟨%c, #Hstore, #Hlwf, #Het, #Hgvk, #Hrp, #Huwl, #Hclock⟩
  iunfold reflFixed2 at Hf2
  icases Hf2 with ⟨%name, %td, %ps, %md, %sr, %weh, #Hdhf, #Hname, #Htd, #Hps, #Hmd, #Hsr, #Hweh⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (wp_relistResourceVersion r v u) $$ [$Hpkg $Hown] as Hown
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨-, -⟩
  (try wp_auto)
  wp_apply wp_traceNew as %tr -
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := Unit) (W64 1)) as %lch %γl ⟨#Hlch, -, Hlown⟩
  · ipureintro; decide
  imod (start_spsc lch (fun _ _ => iprop(False))
    (fun _ => iprop(∃ (obj : GoInterface) (pg : Bool) (e : GoInterface) (u' : Bool),
      list_ptr ↦ obj ∗ paginatedResult_ptr ↦ pg ∗ err_ptr ↦ e ∗ reflOwn r v u' ∗
      options_ptr ↦ listOpts (relistRV v u) ∗
      reflMisc r ∗ pager.pageRes res (listS γa σ0 res) obj e)) γl) $$ Hlch [Hlown]
    with ⟨%γls, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hlown
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %pch %γp ⟨#Hpch, -, Hpown⟩
  · ipureintro; decide
  imod inv_alloc (nroot.@"panicCh") ⊤ (ownChan γp GoInterface (.Buffered [])) $$ [Hpown] with #Hpinv
  · inext; iexact Hpown
  (try wp_auto)
  ipersist r
  ipersist ctx
  ipersist listCh
  ipersist panicCh
  wp_apply wp_fork $$ [Hprod Hown Hmisc list paginatedResult err options]
  · wp_pures
    iapply wp_with_defer_recover
    iintro %gdefer %gpnc gdefer gpnc
    (try wp_auto)
    simp only [recv_eq_func_mk]
    wp_apply (wp_SimplePageFunc _ res (listS γa σ0 res)) $$ [] as %pfn #Hpfn
    · unfold pager.fnOk
      imodintro
      iintro %opts %dq %lo %Φ2 Hlo HΦ2
      wp_auto
      wp_apply HList $$ Hlo Hσ0 as %q %err %σ Hlo Hret Hae %hle
      (try wp_auto)
      iapply HΦ2 $$ Hlo
      iapply (typedListRet_pageRes γa cfg res _ σ0 σ q err hle) $$ [Hret Hae]
      iframe
    (try wp_auto)
    wp_apply (wp_pagerNew pfn) as %pgr Hpgr
    iunfold reflMisc at Hmisc
    icases Hmisc with ⟨%pr, %mn, %mx, Hpr, Hmn, Hmx⟩
    (try wp_auto)
    wp_if_destruct <;> (try wp_auto) <;> (try (wp_if_destruct <;> (try wp_auto))) <;>
      (try (wp_if_destruct <;> (try wp_auto))) <;> (try (wp_if_destruct <;> (try wp_auto))) <;>
      (try (wp_if_destruct <;> (try wp_auto)))
    all_goals
      wp_apply context.Background.wp_proof
      (try wp_auto)
      wp_apply (wp_ListWithAlloc pgr _ _ res (listS γa σ0 res) rfl rfl) $$ [$Hpgr $Hpfn]
        as %obj %pag %err1 ⟨Hpgr, Hres⟩
      (try wp_auto)
      wp_apply (wp_isExpiredError _) $$ [$Hpkg] as %b1 -
      (try wp_auto)
      cases b1
      · (try wp_auto)
        wp_apply (wp_isTooLarge _) $$ [$Hpkg] as %b2 -
        (try wp_auto)
        cases b2
        · (try wp_auto)
          iunfold pager.pageRes at Hres
          icases Hres with (⟨%herr, Hae⟩ | ⟨%he, %q, %os, %rv, %hobj, Hl, HS⟩)
          · obtain ⟨hne, hobj⟩ := herr
            cases err1 with
            | nil => exact absurd rfl hne
            | ok ei =>
              (try wp_auto)
              wp_apply (wp_spsc_close γls lch _ _ []) $$ [$Hspsc $Hprod list paginatedResult err Hown Hpr Hmn Hmx options Hae]
              · iexists _, _, _, _
                iframe
                isplitl [Hpr Hmn Hmx]
                · unfold reflMisc; iexists _, _, _; iframe
                unfold pager.pageRes
                ileft; iframe; ipureintro; exact ⟨hne, hobj⟩
              (try wp_auto)
              wp_apply wp_recoverPanic $$ gpnc as gpnc
              (try wp_auto)
              ipureintro; exact isPanic_intoVal _
          · subst he hobj
            (try wp_auto)
            wp_apply (wp_isUnsupported res q) $$ [$Hpkg] as %gvk -
            (try wp_auto)
            wp_apply (wp_spsc_close γls lch _ _ []) $$ [$Hspsc $Hprod list paginatedResult err Hown Hpr Hmn Hmx options Hl HS]
            · iexists _, _, _, _
              iframe
              isplitl [Hpr Hmn Hmx]
              · unfold reflMisc; iexists _, _, _; iframe
              unfold pager.pageRes
              iright
              isplitr
              · ipureintro; rfl
              iexists q, os, rv
              iframe
              ipureintro; rfl
            (try wp_auto)
            wp_apply wp_recoverPanic $$ gpnc as gpnc
            (try wp_auto)
            ipureintro; exact isPanic_intoVal _
        · (try wp_auto)
          wp_apply (wp_setUnavailable r v u true) $$ [$Hpkg $Hown] as Hown
          (try wp_auto)
          wp_apply context.Background.wp_proof
          (try wp_auto)
          wp_apply (wp_relistResourceVersion r v true) $$ [$Hpkg $Hown] as Hown
          (try wp_auto)
          iclear Hres
          wp_apply (wp_ListWithAlloc pgr _ _ res (listS γa σ0 res) rfl rfl) $$ [$Hpgr $Hpfn]
            as %obj %pag %err1 ⟨Hpgr, Hres⟩
          (try wp_auto)
          iunfold pager.pageRes at Hres
          icases Hres with (⟨%herr, Hae⟩ | ⟨%he, %q, %os, %rv, %hobj, Hl, HS⟩)
          · obtain ⟨hne, hobj⟩ := herr
            cases err1 with
            | nil => exact absurd rfl hne
            | ok ei =>
              (try wp_auto)
              wp_apply (wp_spsc_close γls lch _ _ []) $$ [$Hspsc $Hprod list paginatedResult err Hown Hpr Hmn Hmx options Hae]
              · iexists _, _, _, _
                iframe
                isplitl [Hpr Hmn Hmx]
                · unfold reflMisc; iexists _, _, _; iframe
                unfold pager.pageRes
                ileft; iframe; ipureintro; exact ⟨hne, hobj⟩
              (try wp_auto)
              wp_apply wp_recoverPanic $$ gpnc as gpnc
              (try wp_auto)
              ipureintro; exact isPanic_intoVal _
          · subst he hobj
            (try wp_auto)
            wp_apply (wp_isUnsupported res q) $$ [$Hpkg] as %gvk -
            (try wp_auto)
            wp_apply (wp_spsc_close γls lch _ _ []) $$ [$Hspsc $Hprod list paginatedResult err Hown Hpr Hmn Hmx options Hl HS]
            · iexists _, _, _, _
              iframe
              isplitl [Hpr Hmn Hmx]
              · unfold reflMisc; iexists _, _, _; iframe
              unfold pager.pageRes
              iright
              isplitr
              · ipureintro; rfl
              iexists q, os, rv
              iframe
              ipureintro; rfl
            (try wp_auto)
            wp_apply wp_recoverPanic $$ gpnc as gpnc
            (try wp_auto)
            ipureintro; exact isPanic_intoVal _
      · (try wp_auto)
        wp_apply (wp_setUnavailable r v u true) $$ [$Hpkg $Hown] as Hown
        (try wp_auto)
        wp_apply context.Background.wp_proof
        (try wp_auto)
        wp_apply (wp_relistResourceVersion r v true) $$ [$Hpkg $Hown] as Hown
        (try wp_auto)
        iclear Hres
        wp_apply (wp_ListWithAlloc pgr _ _ res (listS γa σ0 res) rfl rfl) $$ [$Hpgr $Hpfn]
          as %obj %pag %err1 ⟨Hpgr, Hres⟩
        (try wp_auto)
        iunfold pager.pageRes at Hres
        icases Hres with (⟨%herr, Hae⟩ | ⟨%he, %q, %os, %rv, %hobj, Hl, HS⟩)
        · obtain ⟨hne, hobj⟩ := herr
          cases err1 with
          | nil => exact absurd rfl hne
          | ok ei =>
            (try wp_auto)
            wp_apply (wp_spsc_close γls lch _ _ []) $$ [$Hspsc $Hprod list paginatedResult err Hown Hpr Hmn Hmx options Hae]
            · iexists _, _, _, _
              iframe
              isplitl [Hpr Hmn Hmx]
              · unfold reflMisc; iexists _, _, _; iframe
              unfold pager.pageRes
              ileft; iframe; ipureintro; exact ⟨hne, hobj⟩
            (try wp_auto)
            wp_apply wp_recoverPanic $$ gpnc as gpnc
            (try wp_auto)
            ipureintro; exact isPanic_intoVal _
        · subst he hobj
          (try wp_auto)
          wp_apply (wp_isUnsupported res q) $$ [$Hpkg] as %gvk -
          (try wp_auto)
          wp_apply (wp_spsc_close γls lch _ _ []) $$ [$Hspsc $Hprod list paginatedResult err Hown Hpr Hmn Hmx options Hl HS]
          · iexists _, _, _, _
            iframe
            isplitl [Hpr Hmn Hmx]
            · unfold reflMisc; iexists _, _, _; iframe
            unfold pager.pageRes
            iright
            isplitr
            · ipureintro; rfl
            iexists q, os, rv
            iframe
            ipureintro; rfl
          (try wp_auto)
          wp_apply wp_recoverPanic $$ gpnc as gpnc
          (try wp_auto)
          ipureintro; exact isPanic_intoVal _
  (try wp_auto)
  wp_apply (lc := 2) HDone
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply stableCtx_is_chan $$ Hctx
    iapply stableCtx_recv $$ Hctx
    iintro #Hseen
    wp_auto
    wp_apply (wp_LogIfLong tr _)
    (try wp_auto)
    iapply HΦ
    iright; iright
    iframe #
    ipureintro; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, pch, γp
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hpch
    iapply never_recv_au $$ Hpinv
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, lch, γls.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold isSpsc at Hspsc; icases Hspsc with ⟨#Hc, -⟩; iexact Hc
    iapply spsc_rcv_au γls lch _ _ [] _ $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %uv %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨⟨%obj, %pag, %e, %u', Hlist, Hpag, Herr, Hown, Hopt, Hmisc, Hres⟩, -⟩
      ihave #Hmeta : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» $$ []
      · iPkgInit
      ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
      · iPkgInit
      wp_auto
      iunfold pager.pageRes at Hres
      icases Hres with (⟨%herr, Hae⟩ | ⟨%he, %q, %os, %rv, %hobj, Hl, HS⟩)
      · -- the list failed: its error, wrapped
        obtain ⟨hne, hobj⟩ := herr
        wp_apply (wp_LenList res obj null [] go!"") $$ [$Hmeta]
        · unfold apimeta.lenListArg
          rcases hobj with rfl | rfl
          · ileft; ipureintro; rfl
          · iright; ileft; ipureintro; exact ⟨rfl, rfl⟩
        iintro %nl -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨-, -⟩
        (try wp_auto)
        wp_apply (wp_Step tr _ _)
        (try wp_auto)
        cases e with
        | nil => exact absurd rfl hne
        | ok ei =>
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        (try wp_auto)
        wp_apply (wp_Errorf _ _ _ _) $$ [$Hfmt $Hsl2 Hae] as %e2 ⟨-, -⟩
        · rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
          simp only [List.set_cons_succ, List.set_cons_zero, fmt.argsOk]
          isplitr
          · simp only [fmt.argOk]
            ileft; ipureintro; apply fmt.argWf_of_argsWf; exact .cons_string _ _ .nil
          isplitl [Hae]
          · iexact Hae
          itrivial
        (try wp_auto)
        wp_apply (wp_LogIfLong tr _)
        (try wp_auto)
        iapply HΦ
        iright; ileft
        isplitr
        · ipureintro; simp
        unfold reflSt
        iexists v, u', σ0
        iframe
        iframe #
        ipureintro; exact hrv
      · -- the list: its items registered, pushed as the relist's `Replace`
        subst he hobj
        iunfold listS at HS
        icases HS with ⟨%σ, #Hσ, %hS⟩
        obtain ⟨hrvS, hlist, hle⟩ := hS
        subst hrvS
        ihave ⟨Hl, %hqn⟩ := typedListAt_ne_null res q os _ $$ Hl
        wp_apply (wp_LenList res _ q os (rvStr σ.rev)) $$ [$Hmeta Hl] as %nl Hl
        · unfold apimeta.lenListArg; iright; iright; iframe; ipureintro; rfl
        ihave Hl : typedListAt res q os (rvStr σ.rev) $$ [Hl]
        · unfold apimeta.lenListArg
          icases Hl with (%h | %h | ⟨-, Hl⟩)
          · simp [interface.mkOk] at h
          · exact absurd h.2 hqn
          · iexact Hl
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨-, -⟩
        (try wp_auto)
        wp_apply (wp_Step tr _ _)
        (try wp_auto)
        iunfold reflMisc at Hmisc
        icases Hmisc with ⟨%pr, %mn, %mx, Hpr, Hmn, Hmx⟩
        wp_if_destruct <;> (try wp_auto) <;> (try (wp_if_destruct <;> (try wp_auto)))
        all_goals
          wp_apply (wp_setUnavailable r v u' false) $$ [$Hpkg $Hown] as Hown
          (try wp_auto)
          wp_apply (wp_ListAccessor res q os (rvStr σ.rev)) $$ [$Hmeta $Hl] as %m %merr ⟨%hmerr, Hl, #Hacc⟩
          subst hmerr
          iunfold apimeta.listAccOk at Hacc
          icases Hacc with ⟨%hm, #HrvM, #HcontM⟩
          subst hm
          (try wp_auto)
          wp_apply HrvM $$ Hl as Hl
          (try wp_auto)
          wp_apply (wp_Step tr _ _)
          (try wp_auto)
          wp_apply (wp_Extract res q os (rvStr σ.rev)) $$ [$Hmeta $Hl] as %isl %xerr ⟨%hxerr, %xs, Hxs, Hobjs⟩
          subst hxerr
          (try wp_auto)
          wp_apply (wp_Step tr _ _)
          (try wp_auto)
          ihave #Hσ' := Hσ
          iunfold pastSt at Hσ'
          icases Hσ' with ⟨%Hh, -, %hHh⟩
          have hwf : σ.wf := hHh.2.1
          imod infInv_register_list γa res γf γt γi xs os (listOk_res hwf hlist) $$ Hinv Hobjs
            with ⟨%R0, #HR0, #Hoks, %h2⟩
          iunfold keysOk at Hkeys
          ihave %hgood := Hkeys $$ %σ Hσ
          have hl := listRel_of_list res σ hwf os hlist R0 xs h2
          have hu : rvLe n (some σ.rev.toNat) := by
            have h0 := hrv.2.2
            have h1 := hle.1
            cases n with
            | none => trivial
            | some k => simp only [rvLe] at h0 ⊢; omega
          wp_apply (wp_syncWith r f γf (infObj γi res) isl (DFrac.own 1) xs (rvStr σ.rev))
            $$ [$Hpkg $Hstore $Hfifo $Hxs $Hoks]
          iapply (infInv_pushReplaceAU γa res γf γt γi n σ σ.rev R0 xs hl (Nat.le_refl _) hu (hgood res))
            $$ Hinv Hσ HR0 Hlast
          iintro Hlast - -
          (try wp_auto)
          wp_apply (wp_Step tr _ _)
          (try wp_auto)
          wp_apply (wp_setLastSyncResourceVersion r v false _) $$ [$Hpkg $Hown] as Hown
          (try wp_auto)
          wp_apply (wp_Step tr _ _)
          (try wp_auto)
          wp_apply (wp_LogIfLong tr _)
          (try wp_auto)
          iapply HΦ
          ileft
          isplitr
          · ipureintro; rfl
          iexists σ.rev.toNat
          unfold reflSt reflMisc
          iexists (rvStr σ.rev), false, σ
          iframe
          iframe #
          ipureintro
          exact ⟨⟨σ.rev, rfl, rfl⟩, fun k hk => by cases hk; exact hwf.rev_pos, Nat.le_refl _⟩
    · simp only [↓reduceIte]
      icases Hv with ⟨⟨⟩, -⟩
  · iapply BigAndL.bigAndL_nil.2; itrivial


end proof

end cache
end EtcdGrove
end Perennial
