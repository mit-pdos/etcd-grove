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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
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

/-- `syncPaginated`'s options before a page: `syncGs` until the first page's revision is known,
then `WithRev` of it. -/
def syncGsOf (kp : GoString) (recur : Bool) (wr : w64) : List (OpFull → OpFull) :=
  if wr = W64 0 then syncGs kp recur else syncGs kp true ++ [withRevM wr]

/-- **One page: the client's `KV.Get`** of `pk` with the options `gs` (a linearizable range,
unsorted), through the store's client (`kvObjAt` of its `*kv`), with the read update `Qr` at the
members: `nil` and the reply `m` (its key-values' slice owned) at a state `σ` the update fired at,
`m` the server's answer at `σ`; or a client error (`kClientErr`). -/
theorem wp_syncGet [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] {Obj : Type}
    (c : StoreCfg GF Obj) (γk : KVNames) (api : Loc) (ctx : GoInterfaceOk)
    (cdw : context.ContextDesc (IProp GF)) (pk : GoString) (osl : GoSlice)
    (gs : List (OpFull → OpFull)) (Qr : KVState → IProp GF)
    (hsz : opSizeOk (opGetModel pk gs)) (hg : ¬ opGetPanics gs ∧ (opGetModel pk gs).t = W64 1)
    (hser : (rangeWireOf (opGetModel pk gs)).base.serializable = false)
    (hss : (opGetModel pk gs).base.sortSet = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        EtcdGrove.kvObjAt api (c.ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ c.ms, client.kvRegsAt x) ∗
        ctxOk ctx cdw ∗ ctxErrClient ctx cdw ∗ optsAt osl gs ∗ readAus c γk Qr }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ctx))) (Val #pk)) (Val #osl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsgO resp m ∗ □ Qr σ ∗
          ⌜txn.srvRangeOk (rangeWireOf (opGetModel pk gs))
              (σ.at (σ.readRev (rangeWireOf (opGetModel pk gs)).base.rev)).kvs m.kvs m.more ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧
            σ.readRev (rangeWireOf (opGetModel pk gs)).base.rev ≤ σ.rev ∧ kvRevFits σ.rev⌝) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ kClientErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkv, #Hregs, #Hctx, #Hce, #Hopts, #Hra⟩ HΦ
  imod (client.srvStart_alloc (GF := GF) c.ms) with #Hst
  ihave #Hopts' := optsAt_res osl gs iprop(True) $$ Hopts
  ihave #Hst' := client.srvStart_both c.ms $$ Hst
  ihave #Hau := readAus_members c γk Qr (rangeWireOf (opGetModel pk gs)) hser $$ Hra
  wp_apply (client.client_range_any api c.ms (W64 0) ctx cdw pk osl gs iprop(True) Qr [] hsz) $$ []
    as %resp %err ⟨-, Hout, -⟩
  · iframe #
    isplitl []
    · rw [hss]; iapply sortNamesIf_false
    ipureintro; exact hg
  iapply HΦ
  icases Hout with (⟨%Herr, %m, Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
  · subst Herr
    ihave Hs := kubernetes.rangeReply_state_at x.E x.γr (W64 0) x.cid x.mid _ [] Qr m hser $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, -, hrevσ, hle, hb, -⟩ := Hσ
    ileft
    isplitr
    · ipureintro; rfl
    iexists m, σ
    iframe Hm HQ
    ipureintro
    exact ⟨hsel, hrevσ, hle, hb⟩
  · iright
    iunfold kvErr at Hke
    icases Hke with ⟨%Hce, #Hse, #Hcl⟩
    isplitr
    · ipureintro; exact Herr
    iunfold kClientErr
    iframe Hse Hcl
    ipureintro; exact ⟨Herr, Hce⟩

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
  icases Hsw' with ⟨%wp', %nf, %crv, %rse', #Hsw2, #Hwcl, -, -, #Hwgr, -⟩
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
      "Ho" ∷ optsOwn (GF := GF) osl (syncGsOf kp recur wr) ∗
      "%Hpk" ∷ ⌜kp <+: pk ∧ pk.length ≤ opKeyMax⌝ ∗
      "#Hph" ∷ ((⌜wr = W64 0 ∧ pk = kp ∧ I = []⌝ ∗ readAus c γk (Q lbf)) ∨
        (∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗
          ⌜wr = W64 (σ0.rev : Int) ∧ ir = W64 (σ0.rev : Int) ∧ 0 < σ0.rev ∧ recur = true ∧
            kStartOk m σ0 σ0.rev ∧ kvRevFits σ0.rev ∧
            I ++ (fromL (σ0.at σ0.rev) kp true pk).map KRaw.kv = kInitRaws inS σ0 σ0.rev⌝)) :
      IProp GF)
      $$ [preparedKey withRev lastKey getResp err opts metricsOp Hir Hps Hpe Ho]
  · iexists kp, W64 0, _, _, _, r0, osl, []
    iframe
    isplitr
    · ipureintro; exact ⟨List.prefix_refl _, hkpl⟩
    ileft
    iframe Hra
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  wp_for HI
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  obtain ⟨hkpk, hpkl⟩ := Hpk
  icases optsOwn_optsAt _ _ $$ Ho with ⟨#HoAt, Ho⟩
  ihave Hlbq : (|==> ∃ lbq : Nat, readAus c γk (Q lbq) ∗
      ⌜(wr = W64 0 → lbq = lbf) ∧ (wr ≠ W64 0 → lbq = uint.nat wr)⌝ : IProp GF) $$ []
  · icases Hph with (⟨%Hw, #Hra'⟩ | ⟨%lb0, %σ0, #HQ0, %Hp⟩)
    · imodintro
      iexists lbf
      iframe Hra'
      ipureintro
      exact ⟨fun _ => rfl, fun h => absurd Hw.1 h⟩
    · ihave Hra' := Hre $$ %lb0 %σ0 HQ0
      imod Hra' with #Hra'
      imodintro
      iexists σ0.rev
      iframe Hra'
      ipureintro
      obtain ⟨hw, -, hpos, -, -, hfit, -⟩ := Hp
      refine ⟨fun h => ?_, fun _ => ?_⟩
      · exfalso; rw [hw] at h; have := hfit.lt; word
      · rw [hw]; have := hfit.lt; word
  imod Hlbq with ⟨%lbq, #HraQ, %Hlbq⟩
  have hsz : opSizeOk (opGetModel pk (syncGsOf kp recur wr)) := by
    have hel : (prefixRangeEnd kp).length ≤ 2 ^ 27 := by
      have := prefixRangeEnd_length_le kp
      simp only [opKeyMax] at hkpl
      omega
    unfold syncGsOf syncGs
    split <;> (try cases recur) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append]
    all_goals first
      | exact opSizeOk_opGetModel (K := 2 ^ 27) (E := 0) (V := 0) (optsKeep_nil _ _ _) hpkl (by decide)
      | exact opSizeOk_opGetModel (K := 2 ^ 27) (E := 2 ^ 27) (V := 0)
          (optsKeep_cons (withLimitM_keep _) (optsKeep_cons (withRangeM_keep hel)
            (optsKeep_nil _ _ _))) hpkl (by decide)
      | exact opSizeOk_opGetModel (K := 2 ^ 27) (E := 2 ^ 27) (V := 0)
          (optsKeep_cons (withLimitM_keep _) (optsKeep_cons (withRangeM_keep hel)
            (optsKeep_cons (withRevM_keep _) (optsKeep_nil _ _ _)))) hpkl (by decide)
  have hg : ¬ opGetPanics (syncGsOf kp recur wr) ∧ (opGetModel pk (syncGsOf kp recur wr)).t = W64 1 := by
    unfold syncGsOf syncGs
    split <;> (try cases recur) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append]
    all_goals first
      | rfl
      | (refine ⟨?_, rfl⟩; unfold opGetPanics opFold OpFull.newOp; simp [withRevM, withLimitM, withRangeM])
  have hser : (rangeWireOf (opGetModel pk (syncGsOf kp recur wr))).base.serializable = false := by
    unfold syncGsOf syncGs
    split <;> (try cases recur) <;> rfl
  have hss : (opGetModel pk (syncGsOf kp recur wr)).base.sortSet = false := by
    unfold syncGsOf syncGs
    split <;> (try cases recur) <;> rfl
  wp_apply (wp_syncGet c γk api ctx (kCdw γ cd) pk osl (syncGsOf kp recur wr) (Q lbq) hsz hg hser hss)
    $$ [] as %resp %gerr Hget
  · iframe #
  (try wp_auto)
  icases Hget with (⟨%Hge, %mm, %σ, Hm, #HQσ, %Hσ⟩ | ⟨%Hge, #Hce'⟩)
  rotate_left
  · -- the client's error: `interpretListError(err, true, preparedKey, wc.key)`
    ihave #Hce2 := Hce'
    iunfold kClientErr at Hce2
    icases Hce2 with ⟨-, #Hse, -⟩
    wp_apply (wp_RecordEtcdRequest _ c.gr gerr t0 (by cases recur <;> decide) Hutf.1 Hutf.2) $$ []
    · iframe #
    cases gerr with
    | nil => exact absurd rfl Hge
    | ok gi =>
    (try wp_auto)
    wp_apply (wp_interpretListError Obj c (GoInterface.ok gi) true pk kp
        (fun _ => by simp [k8s_etcd3.encOkL, hkp, hkpk])) $$ [] as %e2 #He2
    · iframe #
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe Hpe
    iright
    isplitr [Hir]
    · iunfold listErrF at He2
      icases He2 with (#Hc | ⟨%st, #Hst, %Hstp⟩)
      · iapply (kErrOk_client wp_AsLeafTy wp_ECode wp_SCode) $$ Perr Hc
      · iunfold apierrors.apiErrAt at Hst
        icases Hst with ⟨%l, %hl, #Hl, -⟩
        subst hl
        iapply (kErrOk_statusError wp_AsLeafTy l st Hstp.2.2) $$ Perr Hl
    iexists ir
    iexact Hir
  subst Hge
  wp_apply (wp_RecordEtcdRequest _ c.gr GoInterface.nil t0 (by cases recur <;> decide) Hutf.1 Hutf.2)
    $$ []
  · iframe #
    iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
  (try wp_auto)
  iunfold rangeRespMsgO at Hm
  icases Hm with ⟨Hrecv, Hown⟩
  iunfold rangeRespRecv at Hrecv
  icases Hrecv with ⟨%Hnn, %h, #Hh, #Hhf, #Hmore, #Hcount⟩
  iunfold rangeRespKvsOwn at Hown
  icases Hown with ⟨%sl2, %ps, #Hkvf2, Hsl2, #Hkvs⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  obtain ⟨hsel, hrevσ, hle', hfitσ⟩ := Hσ
  ihave %HwfQ := hQ lbq σ $$ HQσ
  obtain ⟨hlbq, -, hwh, hks⟩ := HwfQ
  ihave ⟨%lb0, %σ0, #HQ0, %HP⟩ : (∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗
      ⌜mm.kvs <+: fromL (σ0.at σ0.rev) kp recur pk ∧
       (mm.more = false → mm.kvs = fromL (σ0.at σ0.rev) kp recur pk) ∧
       (mm.more = true → mm.kvs.length = 10000 ∧
         10000 < (fromL (σ0.at σ0.rev) kp recur pk).length ∧ recur = true) ∧
       I ++ (fromL (σ0.at σ0.rev) kp recur pk).map KRaw.kv = kInitRaws inS σ0 σ0.rev ∧
       kStartOk m σ0 σ0.rev ∧ kvRevFits σ0.rev ∧
       ((wr = W64 0 ∧ σ0.rev = σ.rev) ∨
         (wr = W64 (σ0.rev : Int) ∧ ir = W64 (σ0.rev : Int) ∧ recur = true)) ∧
       (∀ v ∈ (σ0.at σ0.rev).kvs, 0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ σ0.rev ∧
         v.key.length < opKeyMax)⌝ : IProp GF) $$ []
  · icases Hph with (⟨%Hw, -⟩ | ⟨%lb0', %σ0, #HQ0, %Hp⟩)
    · obtain ⟨hw0, hpk0, hI0⟩ := Hw
      subst hw0 hpk0 hI0
      have hlb : lbq = lbf := Hlbq.1 rfl
      subst hlb
      iexists lbq, σ
      iframe HQσ
      ipureintro
      have hrr : σ.readRev (opGetModel pk (syncGsOf pk recur (W64 0))).base.rev = σ.rev := by
        have : (opGetModel pk (syncGsOf pk recur (W64 0))).base.rev = W64 0 := by
          cases recur <;> rfl
        rw [this]; unfold KVState.readRev; simp
      rw [hrr] at hsel
      have hst' : kStartOk m σ σ.rev := by
        unfold kStartOk; rw [if_pos hf]; exact ⟨rfl, by omega⟩
      have hwh' : ∀ v ∈ (σ.at σ.rev).kvs, 0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ σ.rev ∧
          v.key.length < opKeyMax := fun v hv =>
        ⟨(hwh σ.rev (Nat.le_refl _) v hv).2.1, (hwh σ.rev (Nat.le_refl _) v hv).2.2,
          (hks σ.rev (Nat.le_refl _)).2 v hv⟩
      cases recur
      · have hw : rangeWireOf (opGetModel pk (syncGsOf pk false (W64 0))) =
            rangeWireOf (opGetModel pk []) := rfl
        rw [hw] at hsel
        obtain ⟨hk, hm⟩ := srvRangeOk_key0 pk _ _ _ hsel
        rw [← fromL_key] at hk
        refine ⟨hk ▸ List.prefix_refl _, fun _ => hk, fun (h : mm.more = true) => (by rw [hm] at h; cases h), ?_, hst',
          hfitσ, Or.inl ⟨rfl, rfl⟩, hwh'⟩
        rw [List.nil_append, hinS, kInitRaws_fromL]
      · have hw : rangeWireOf (opGetModel pk (syncGsOf pk true (W64 0))) =
            pageOp pk pk (W64 0) (W64 10000) := rfl
        rw [hw] at hsel
        obtain ⟨hk, hm⟩ := srvRangeOk_sync pk pk _ _ _ _ (List.prefix_refl _) hsel
        refine ⟨hk ▸ List.take_prefix _ _, fun h => ?_, fun h => ?_, ?_, hst', hfitσ,
          Or.inl ⟨rfl, rfl⟩, hwh'⟩
        · rw [hm] at h; rw [hk]; exact List.take_of_length_le (by simpa using h)
        · rw [hm] at h; have h' := of_decide_eq_true h; rw [hk]
          exact ⟨by simp only [List.length_take]; omega, h', rfl⟩
        · rw [List.nil_append, hinS, kInitRaws_fromL]
    · obtain ⟨hw, hir, hpos, hrec, hst0, hfit0, hI⟩ := Hp
      subst hrec
      have hfit0' := hfit0.lt
      have hwne : wr ≠ W64 0 := by rw [hw]; intro h; apply Nat.ne_of_gt hpos; word
      have hlb : lbq = σ0.rev := by rw [Hlbq.2 hwne, hw]; word
      subst hlb
      ihave %Hh := hH _ _ σ0 σ $$ [HQ0 HQσ]
      · iframe HQ0 HQσ
      ihave %Hw0 := hQ _ _ $$ HQ0
      obtain ⟨-, -, hwh0, hks0⟩ := Hw0
      have hat : σ.at σ0.rev = σ0.at σ0.rev := (kvSameHist_at σ0 σ σ0.rev Hh (Nat.le_refl _) hlbq).symm
      have hrr : σ.readRev (opGetModel pk (syncGsOf kp true wr)).base.rev = σ0.rev := by
        have : (opGetModel pk (syncGsOf kp true wr)).base.rev = wr := by
          unfold syncGsOf; rw [if_neg hwne]; rfl
        rw [this, hw]; unfold KVState.readRev
        split <;> word
      rw [hrr, hat] at hsel
      have hwire : rangeWireOf (opGetModel pk (syncGsOf kp true wr)) = pageOp kp pk wr (W64 10000) := by
        unfold syncGsOf; rw [if_neg hwne]; rfl
      rw [hwire] at hsel
      obtain ⟨hk, hm⟩ := srvRangeOk_sync kp pk _ _ _ _ hkpk hsel
      iexists lb0', σ0
      iframe HQ0
      ipureintro
      refine ⟨hk ▸ List.take_prefix _ _, fun h => ?_, fun h => ?_, hI, hst0, hfit0, Or.inr ⟨hw, hir, rfl⟩,
        fun v hv => ⟨(hwh0 σ0.rev (Nat.le_refl _) v hv).2.1, (hwh0 σ0.rev (Nat.le_refl _) v hv).2.2,
          (hks0 σ0.rev (Nat.le_refl _)).2 v hv⟩⟩
      · rw [hm] at h; rw [hk]; exact List.take_of_length_le (by simpa using h)
      · rw [hm] at h; have h' := of_decide_eq_true h; rw [hk]
        exact ⟨by simp only [List.length_take]; omega, h', rfl⟩
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
