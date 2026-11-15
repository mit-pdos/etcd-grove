/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__syncPaginated.lean`. Lean-first (no Rocq
counterpart).

The options slice is appended to (`WithLimit`, `WithRange`, later `WithRev`): its elements are held
read-only with its capacity owned (`optsOwn`), so that each `append` (`wp_slice_append_dfrac`) keeps
them and the client's `Get` reads them (`optsAt`). The loop's invariant: before the first page,
`withRev = 0` and the read updates from `lbf`; after a page cut by `More` (recursive only), the
first page's state `σ0` (its revision the start point, `withRev` and `initialRev`), the raw events
queued so far `I` followed by the scope from the next start key (`fromL`) being the initial raw
events (`kInitRaws`). Each page is a client `KV.Get` (`client_range_any`), its key-values the scope's
from the start key (`srvRangeOk_page`, `srvRangeOk_key0`), each queued through `parseKV` and
`queueEvent` (`kProd_queue`, a prefix of the initial part: `kInit_ok`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__syncPaginated
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__queueEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.parseKV
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretListError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithLimit
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.GetPrefixRangeEnd
public import Spec.fmt.ErrorfPlain
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ErrOk
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.SyncPages

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- **An options slice being appended to**: its elements read-only, `optSpec` of `gs`, its
capacity owned. -/
def optsOwn (sl : GoSlice) (gs : List (OpFull → OpFull)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ownSliceCap GoFunc sl (DFrac.own 1) ∗
    ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : OpFull → OpFull), ⌜fs[i]? = some f⌝ -∗ ⌜gs[i]? = some g⌝ -∗
      optSpec f g)

theorem optsOwn_optsAt (sl : GoSlice) (gs : List (OpFull → OpFull)) :
    optsOwn (GF := GF) sl gs ⊢ optsAt sl gs ∗ optsOwn sl gs := by
  unfold optsOwn optsAt
  iintro ⟨%fs, #Hs, Hc, %Hl, #Hf⟩
  isplitr
  · iexists fs
    iframe Hs Hf
    ipureintro; exact Hl
  iexists fs
  iframe Hs Hc Hf
  ipureintro; exact Hl

/-- The read updates at the members, as `client_range_any` takes them (linearizable reads). -/
theorem readAus_members {Obj : Type} (c : StoreCfg GF Obj) (γk : KVNames) (Q : KVState → IProp GF)
    (o : OpFull) (hs : o.base.serializable = false) :
    readAus c γk Q ⊢ □ [∧list] x ∈ c.ms, ⌜Q = fun _ => iprop(True)⌝ ∨
      (⌜o.base.serializable = false⌝ ∗ kvReadAu x.γr.kv Q) := by
  unfold readAus
  iintro ⟨-, #H⟩
  imodintro
  iapply (BigAndL.bigAndL_intro (P := iprop(□ [∗list] x ∈ c.ms, kvReadAu x.γr.kv Q))
    (fun k x hk => ?_)) $$ H
  iintro #H'
  ihave #Hx := BigSepL.bigSepL_lookup hk $$ H'
  iright
  iframe Hx
  ipureintro; exact hs

/-- `append(opts, f)`, `f` with `optSpec f g`, in a fresh one-element slice. -/
theorem wp_optsOwn_append (sl sl2 : GoSlice) (gs : List (OpFull → OpFull)) (f : GoFunc)
    (g : OpFull → OpFull) :
    {{ optsOwn (GF := GF) sl gs ∗ optSpec f g ∗ sl2 ↦* [f] }}
      (App (App (Val #(functions go.append
        [go.GoType.SliceType go_etcd_io.etcd.client.v3.OpOption.ty])) (Val #sl)) (Val #sl2))
    {{ (s' : GoSlice), RET #s'; optsOwn s' (gs ++ [g]) }} := by
  iintro %Φ ⟨Ho, #Hf, Hsl2⟩ HΦ
  iunfold optsOwn at Ho
  icases Ho with ⟨%fs, #Hs, Hcap, %Hl, #Hfs⟩
  wp_apply (wp_slice_append_dfrac (st := go.GoType.SliceType go_etcd_io.etcd.client.v3.OpOption.ty)
    (t := go_etcd_io.etcd.client.v3.OpOption.ty) sl fs DFrac.discard sl2 [f] (DFrac.own 1))
    $$ [Hcap Hsl2] as %s' ⟨#Hs', Hcap', -⟩
  · iframe Hs Hcap Hsl2
    ipureintro; exact DFrac.valid_discard
  iapply HΦ
  iunfold optsOwn
  iexists fs ++ [f]
  iframe Hs' Hcap'
  isplitr
  · ipureintro; simp [Hl]
  iintro !> %i %f' %g' %Hf' %Hg'
  by_cases hi : i < fs.length
  · rw [List.getElem?_append_left hi] at Hf'
    rw [List.getElem?_append_left (by omega)] at Hg'
    iapply Hfs $$ %i %f' %g' %Hf' %Hg'
  · rw [List.getElem?_append_right (by omega)] at Hf'
    rw [List.getElem?_append_right (by omega)] at Hg'
    have hgl : i - gs.length = i - fs.length := by omega
    rw [hgl] at Hg'
    rcases hk : i - fs.length with _ | k <;> rw [hk] at Hf' Hg'
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg'
      subst Hf' Hg'
      iexact Hf
    · simp at Hf'

theorem watchChan.syncPaginated.wp_proof
    (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG))
    (wp_ECode : rpctypes.EtcdError.Code.spec (GF := GF) (hG := hG))
    (wp_SCode : status.Status.Code.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithLimit : WithLimit.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_GetPrefixRangeEnd : GetPrefixRangeEnd.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_ErrorfPlain : fmt.ErrorfPlain.spec (GF := GF) (hG := hG))
    (wp_interpretListError : interpretListError.spec (GF := GF) (hG := hG))
    (wp_parseKV : parseKV.spec (GF := GF) (hG := hG))
    (wp_queueEvent : watchChan.queueEvent.spec (GF := GF) (hG := hG)) :
    watchChan.syncPaginated.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 lbf q
    hQ hH hR hf hle
  wp_start as ⟨#Hst, #Hsw, #Hwc, Hir, #Hra, #Hre, Hps, Hpe⟩
  ihave #Hwc' := Hwc
  iunfold kWcProd at Hwc'
  icases Hwc' with ⟨%wp, %chI, %chR, %lg, %cf, %rse, %γc, #Hfw, #Hsw1, #Hfk, #Hfr, -, -, #Hfctx,
    -, -, -, -, #HfI, #HfL, #Hbl, #Hspsc, -, -, #Hctx, #Hoc, #Hce, %Hp⟩
  obtain ⟨hinS, hkpl, hkp⟩ := Hp
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp', %nf, %crv, %rse', #Hsw2, #Hwcl, -⟩
  ihave %Hwp := typedPointsto_agree_wand _ _ _ _ _ $$ Hsw1 Hsw2
  subst Hwp
  ihave #Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, -, -, -, -, -, -, -, -, -, -, -, -, #Hcl, -, #Hregs, -, #Hlst⟩
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%lf, %lγ, -, -, -, %Hutf, -⟩
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hreg : (registryFact : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold registryFact at Hreg
  icases Hreg with ⟨-, #Hlim⟩
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #HctxOk : ctxOk ctx (kCdw γ cd) $$ []
  · iapply ctxOk_of_isContext
    iframe Hctx Hoc
  (try wp_auto)
  -- the options: none, or `WithLimit(10000)` and `WithRange(GetPrefixRangeEnd(key))`
  wp_apply (wp_slice_literal (V := GoFunc) [])
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  imod ownSlice_persist _ _ _ $$ Hsl0 with #Hsl0
  ihave Ho0 : optsOwn (GF := GF) _ [] $$ [Hcap0]
  · iunfold optsOwn
    iexists []
    iframe Hsl0 Hcap0
    isplitr
    · ipureintro; rfl
    iintro !> %i %f %g %Hf
    simp at Hf
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ wc_ptr ↦ wc ∗ ∃ osl : GoSlice,
      opts_ptr ↦ osl ∗ optsOwn (GF := GF) osl (syncGs kp recur)))) $$ [opts Ho0 wc]
  · cases recur
    · wp_auto
      isplitr
      · ipureintro; rfl
      iframe wc
      iexists _
      iframe opts
      iExactEq Ho0
      rfl
    · wp_auto
      wp_apply wp_WithLimit as %f1 #Hf1
      wp_apply (wp_slice_literal (V := GoFunc) [f1])
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      (try wp_auto)
      wp_apply (wp_optsOwn_append _ _ [] f1 (withLimitM (W64 10000))) $$ [Ho0 Hsl1] as %o1 Ho1
      · iframe Ho0 Hsl1 Hf1
      (try wp_auto)
      wp_apply wp_GetPrefixRangeEnd
      (try wp_auto)
      wp_apply wp_WithRange as %f2 #Hf2
      wp_apply (wp_slice_literal (V := GoFunc) [f2])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply (wp_optsOwn_append _ _ _ f2 (withRangeM (prefixRangeEnd kp))) $$ [Ho1 Hsl2] as %o2 Ho2
      · iframe Ho1 Hsl2 Hf2
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iframe wc
      iexists _
      iframe opts
      iExactEq Ho2
      rfl
  iintro %v ⟨%hv, wc, %osl, opts, Ho⟩
  subst hv
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      metricsOp_ptr ↦ (if recur then go!"list" else go!"get")))) $$ [metricsOp]
  · cases recur
    · (try wp_auto)
      iframe; ipureintro; rfl
    · (try wp_auto)
      iframe; ipureintro; rfl
  iintro %v ⟨%hv, metricsOp⟩
  subst hv
  (try wp_auto)
  ihave HI : (∃ (pk : GoString) (wr : w64) (lk : GoSlice) (gr : Loc) (e : GoInterface) (ir : w64)
      (osl : GoSlice) (I : List KRaw),
      "preparedKey" ∷ preparedKey_ptr ↦ pk ∗ "withRev" ∷ withRev_ptr ↦ wr ∗
      "lastKey" ∷ lastKey_ptr ↦ lk ∗ "getResp" ∷ getResp_ptr ↦ gr ∗ "err" ∷ err_ptr ↦ e ∗
      "opts" ∷ opts_ptr ↦ osl ∗ "metricsOp" ∷ metricsOp_ptr ↦ (if recur then go!"list" else go!"get") ∗
      "Hir" ∷ structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ ir ∗
      "Hps" ∷ kProdSt γ cd I ∗ "Hpe" ∷ dghostVar γ.prodEx (DFrac.own q) false ∗
      "Hph" ∷ ((⌜wr = W64 0 ∧ pk = kp ∧ I = []⌝ ∗ optsOwn (GF := GF) osl (syncGs kp recur) ∗
          readAus c γk (Q lbf)) ∨
        (∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗
          ⌜wr = W64 (σ0.rev : Int) ∧ ir = W64 (σ0.rev : Int) ∧ 0 < σ0.rev ∧ recur = true ∧
            kStartOk m σ0 σ0.rev ∧ kvRevFits σ0.rev ∧ kp <+: pk ∧ pk.length ≤ opKeyMax ∧
            I ++ (fromL (σ0.at σ0.rev) kp true pk).map KRaw.kv = kInitRaws inS σ0 σ0.rev⌝ ∗
          optsOwn (GF := GF) osl (syncGs kp true ++ [withRevM wr]))) : IProp GF)
      $$ [preparedKey withRev lastKey getResp err opts metricsOp Hir Hps Hpe Ho]
  · iexists kp, W64 0, _, _, _, r0, osl, []
    iframe
    ileft
    iframe Ho Hra
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  wp_for HI
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
