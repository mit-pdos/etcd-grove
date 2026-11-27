/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__syncPaginated.lean`. Lean-first (no Rocq
counterpart).

The options slice is appended to (`WithLimit`, `WithRange`, later `WithRev`): its elements are held
read-only with its capacity owned (`optsOwn`), so that each `append` (`wp_slice_append_dfrac`) keeps
them and the client's `Get` reads them (`optsAt`). The loop's invariant: before the first page,
`withRev = 0` and the read updates from `lbf`; after a page cut by `More` (recursive only), the
first page's state `σ0` (its revision the start point, `withRev` and `initialRev`), the raw events
queued so far `I` followed by the scope from the next start key (`fromL`) being the initial raw
events (`kInitRaws`). Each page is a client `KV.Get` (the client's law `kvGet`), its key-values the scope's
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
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ErrOk
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.SyncPages
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.OptsOwn
public import Proof.go_etcd_io.etcd.client.v3.ClientCallLaws
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

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

/-- The read updates at the client's KVs, as its `KV.Get` takes them. -/
theorem readAus_kvs {Obj : Type} (c : StoreCfg GF Obj) (γk : KVNames) (Q : KVState → IProp GF) :
    readAus c γk Q ⊢ □ [∗list] γv ∈ c.K.kvs, kvReadAu γv Q := by
  unfold readAus
  iintro ⟨-, #H⟩
  iexact H

/-- `syncPaginated`'s options before a page: `syncGs` until the first page's revision is known,
then `WithRev` of it. -/
def syncGsOf (kp : GoString) (recur : Bool) (wr : w64) : List (OpFull → OpFull) :=
  if wr = W64 0 then syncGs kp recur else syncGs kp true ++ [withRevM wr]

/-- **One page: the client's `KV.Get`** of `pk` with the options `gs` (a linearizable range,
unsorted), through the store's client (`K.kvAt` of its `*kv`), with the read update `Qr` at the
members: `nil` and the reply `m` (its key-values' slice owned) at a state `σ` the update fired at,
`m` the server's answer at `σ`; or a client error (`kClientErr`). -/
theorem wp_syncGet [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] {Obj : Type}
    (c : StoreCfg GF Obj) (hK : c.K.Laws) (γk : KVNames) (api : Loc) (ctx : GoInterfaceOk)
    (cdw : context.ContextDesc (IProp GF)) (pk : GoString) (osl : GoSlice)
    (gs : List (OpFull → OpFull)) (Qr : KVState → IProp GF)
    (hsz : opSizeOk (opGetModel pk gs)) (hg : ¬ opGetPanics gs ∧ (opGetModel pk gs).t = W64 1)
    (hser : (rangeWireOf (opGetModel pk gs)).base.serializable = false)
    (hss : (opGetModel pk gs).base.sortSet = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        c.K.kvAt api ∗
        ctxOk ctx cdw ∗ ctxErrClient ctx cdw ∗ optsAt osl gs ∗ readAus c γk Qr }}
      (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
          go!"Get")) (Val #(GoInterface.ok ctx))) (Val #pk)) (Val #osl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsgO resp m ∗ □ Qr σ ∗
          ⌜txn.srvRangeOk (rangeWireOf (opGetModel pk gs))
              (σ.at (σ.readRev (rangeWireOf (opGetModel pk gs)).base.rev)).kvs m.kvs m.more ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧
            σ.readRev (rangeWireOf (opGetModel pk gs)).base.rev ≤ σ.rev ∧ kvRevFits σ.rev⌝) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ kClientErr err)) }} := by
  iintro %Φ ⟨#Pc, Hlt, #Hkv, #Hctx, #Hce, #Hopts, #Hra⟩ HΦ
  ihave #Hau := readAus_kvs c γk Qr $$ Hra
  wp_apply (hK.kvGet api ctx cdw pk osl gs Qr hsz hg hser hss) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
  iapply HΦ
  iframe Hlt
  icases Hout with (Hok | ⟨%Herr, #Hke⟩)
  · ileft; iexact Hok
  · iright
    isplitr
    · ipureintro; exact Herr
    iunfold kClientErr
    iexact Hke

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
  intro _ _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 lbf q
    hQ hH hR hf hle
  wp_start as ⟨Hlt, #Hst, #Hsw, #Hwc, Hir, #Hra, #Hre, Hps, Hpe⟩
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
  icases Hst' with ⟨%Hsp, -, -, -, -, -, -, -, -, -, -, -, -, #Hkcl, -, #Hlst⟩
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%lf, %lγ, -, -, -, %Hutf, -⟩
  iunfold k8sClient at Hkcl
  icases Hkcl with ⟨%hK, #Hh⟩
  icases (hK.kvField c.cl) $$ Hh with ⟨%api, #Hkvf, #Hkv⟩
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
            I ++ (fromL (σ0.at σ0.rev) kp true pk).map KRaw.kv = kInitRaws inS σ0 σ0.rev⌝)) ∗
      "Hlt" ∷ levelTok 0 :
      IProp GF)
      $$ [preparedKey withRev lastKey getResp err opts metricsOp Hir Hps Hpe Ho Hlt]
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
  wp_apply (wp_syncGet c hK γk api ctx (kCdw γ cd) pk osl (syncGsOf kp recur wr) (Q lbq) hsz hg hser hss)
    $$ [$Hlt] as %resp %gerr ⟨Hlt, Hget⟩
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
    iframe Hlt
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
         (wr = W64 (σ0.rev : Int) ∧ ir = W64 (σ0.rev : Int) ∧ recur = true ∧ 0 < σ0.rev)) ∧
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
      refine ⟨hk ▸ List.take_prefix _ _, fun h => ?_, fun h => ?_, hI, hst0, hfit0, Or.inr ⟨hw, hir, rfl, hpos⟩,
        fun v hv => ⟨(hwh0 σ0.rev (Nat.le_refl _) v hv).2.1, (hwh0 σ0.rev (Nat.le_refl _) v hv).2.2,
          (hks0 σ0.rev (Nat.le_refl _)).2 v hv⟩⟩
      · rw [hm] at h; rw [hk]; exact List.take_of_length_le (by simpa using h)
      · rw [hm] at h; have h' := of_decide_eq_true h; rw [hk]
        exact ⟨by simp only [List.length_take]; omega, h', rfl⟩
  obtain ⟨hpre, hnm, hmo, hI, hst0, hfit0, hph, hwh0⟩ := HP
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl2
  (try wp_auto)
  -- `len(getResp.Kvs) == 0 && getResp.More`: an error
  wp_bind (If _ _ (Val #false))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (sl2.len = W64 0 ∧ mm.more = true))⌝ ∗
      getResp_ptr ↦ resp))) $$ [getResp]
  · by_cases h0 : sl2.len = W64 0
    · rw [decide_eq_true h0]
      (try wp_auto)
      iframe
      ipureintro; simp [h0]
    · rw [decide_eq_false h0]
      (try wp_auto)
      iframe
      ipureintro
      rw [show decide (sl2.len = W64 0 ∧ mm.more = true) = false from decide_eq_false (fun h => h0 h.1)]
  iintro %v ⟨%hv, getResp⟩
  subst hv
  by_cases hbad : sl2.len = W64 0 ∧ mm.more = true
  · rw [decide_eq_true hbad]
    (try wp_auto)
    wp_apply (wp_ErrorfPlain _ slice.nil [] (DFrac.own 1) (by refine ⟨_, rfl, ?_⟩; decide)) $$ []
      as %x ⟨-, %msg, -, -, #HE⟩
    · iframe #
      isplitl
      · iapply ownSlice_nil
      fmt_args_intro; itrivial
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iframe Hpe
    iright
    isplitr [Hir]
    · iapply (kErrOk_errorString wp_AsLeafTy x) $$ Perr
      unfold fmt.stringMethodSpec
      iintro !> %Φ' HΦ'
      iapply HE
      inext
      iapply HΦ'
    iexists ir
    iexact Hir
  rw [decide_eq_false hbad]
  (try wp_auto)
  -- queue the page's key-values
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave #Hspsc' := Hspsc
  iunfold isSpsc at Hspsc'
  icases Hspsc' with ⟨#Hchan, -⟩
  ihave HJ : (∃ (j k : w64) (kvl : Loc) (lkv : GoSlice) (ps' : List Loc),
      "i" ∷ i_ptr ↦ j ∗ "Higo" ∷ igo ↦ k ∗ "kv" ∷ kv_ptr ↦ kvl ∗ "lastKey" ∷ lastKey_ptr ↦ lkv ∗
      "Hsl2" ∷ sl2 ↦* ps' ∗
      "Hps" ∷ kProdSt γ cd (I ++ (mm.kvs.take (sint.nat j)).map KRaw.kv) ∗
      "Hpe" ∷ dghostVar γ.prodEx (DFrac.own q) false ∗
      "#Hlk" ∷ (⌜sint.nat j = 0⌝ ∨ ∃ kv : EtcdKv,
        ⌜mm.kvs[sint.nat j - 1]? = some kv⌝ ∗ lkv ↦*□ kv.key) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ mm.kvs.length ∧ ps'.length = ps.length ∧
        (∀ k, sint.nat j ≤ k → ps'[k]? = ps[k]?)⌝ : IProp GF)
      $$ [i Higo kv lastKey Hsl2 Hps Hpe]
  · iexists W64 0, _, _, _, ps
    iframe i Higo kv lastKey Hsl2 Hpe
    isplitl [Hps]
    · iExactEq Hps
      simp [sint.nat]
    isplitr
    · ileft; ipureintro; rfl
    ipureintro
    exact ⟨by decide, by simp, rfl, fun _ _ => rfl⟩
  wp_for HJ
  wp_if_destruct
  · obtain ⟨hj0, hjk, hpsl, hpse⟩ := Hj
    have Hif' : sint.Z j < sint.Z sl2.len := by
      first | exact Hif | (have h := go.intoVal_inj Hif; simpa using h)
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl2.len := ⟨hj0, Hif'⟩
    have hjlt : sint.nat j < mm.kvs.length := by
      rw [← Hlen, Hsll.1]
      simp only [sint.nat, sint.Z] at hj0 Hif' ⊢
      omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    obtain ⟨v, hv⟩ : ∃ v, mm.kvs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hjlt⟩
    obtain ⟨pq, hq⟩ : ∃ q, ps[sint.nat j]? = some q :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hlen]; exact hjlt)⟩
    have hq' : ps'[(sint.Z j).toNat]? = some pq := by rw [← hq]; exact hpse _ (Nat.le_refl _)
    wp_apply wp_load_slice_index sl2 (sint.Z j) ps' _ pq hj0 $$ [$Hsl2] as Hsl2
    · ipureintro; exact hq'
    ihave #Hkv := Hall $$ %(sint.nat j) %pq %v %hq %hv
    iunfold txn.kvIs at Hkv
    icases Hkv with ⟨%keySl, %valSl, #Hk, #Hksl, #Hcr, #Hmr, #Hver, #Hvf, #Hvsl, #Hlease, %Hnn'⟩
    (try wp_auto)
    wp_apply (wp_parseKV pq v σ0) $$ [] as %p ⟨%ev, Hp, #Hev⟩
    · iframe #
      iunfold kvValAt
      iexists keySl, valSl
      iframe #
    ipersist Hp
    ihave #Hea : eventAt σ0 p (KRaw.kv v) $$ []
    · iunfold eventAt
      iexists ev
      iframe Hp Hev
    have hv' : mm.kvs[sint.nat j]'hjlt = v := by
      simpa [List.getElem?_eq_getElem hjlt] using hv
    have hok : kRawStreamOk inS m σ0 σ0.rev
        (I ++ (mm.kvs.take (sint.nat j)).map KRaw.kv ++ [KRaw.kv v]) := by
      apply kInit_ok (fun _ => Nat.le_refl _)
      have := queue_prefix hI hpre (sint.nat j) hjlt
      rw [hv'] at this
      exact this.trans (kInitRaws_prefix inS m σ0 σ0.rev hf)
    ihave ⟨%S, %Qs, Hsc, HQs, Hdrop⟩ := kProd_queue γ cd inS m Q chI p (KRaw.kv v) _ lb0 lb0 σ0.rev
      σ0 σ0 hst0 hok $$ Hspsc Hea HQ0 HQ0 Hps
    (try wp_auto)
    wp_apply (wp_queueEvent wc chI lg ctx (kCdw γ cd) γ.inc.chanName p S Qs) $$ [Hsc] as Hres
    · iframe #
      iexact Hsc
    ihave ⟨Hps, Hpe⟩ : (kProdSt γ cd (I ++ (mm.kvs.take (sint.nat j)).map KRaw.kv ++ [KRaw.kv v]) ∗
        dghostVar γ.prodEx (DFrac.own q) false : IProp GF) $$ [Hres HQs Hdrop Hpe]
    · icases Hres with (HQs' | ⟨#Hpd, HS⟩)
      · iframe Hpe
        iapply HQs $$ HQs'
      · ihave H2 := Hdrop $$ %q HS
        iapply H2
        · iintro !>
          unfold kCdw
          iexact Hpd
        · iexact Hpe
    (try wp_auto)
    have hjps : sint.Z j < (ps'.length : Int) := by
      rw [hpsl, Hsll.1]; simp only [sint.nat, sint.Z] at hj0 Hif' ⊢; omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index sl2 (sint.Z j) ps' (null : Loc)) $$ [$Hsl2] as Hsl2
    · ipureintro; exact ⟨hj0, hjps⟩
    (try wp_auto)
    wp_for_post
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := hjlt; have := Hsll.1; simp only [sint.nat, sint.Z] at hjlt hj0 Hif' ⊢; word
    iframe
    iexists j + W64 1, j, pq, keySl, ps'.set (sint.Z j).toNat null
    simp only [named]
    rw [hj1]
    iframe
    isplitl [Hps]
    · iExactEq Hps
      rw [List.take_succ, List.getElem?_eq_getElem hjlt, hv', List.map_append, List.append_assoc]
      rfl
    isplitr
    · iright
      iexists v
      iframe Hksl
      ipureintro
      simpa using hv
    ipureintro
    refine ⟨by word, by omega, by simp [hpsl], ?_⟩
    intro k hk
    rw [List.getElem?_set_ne (by simp only [sint.nat, sint.Z] at hk hj0 ⊢; omega)]
    exact hpse k (by omega)
  -- the page is queued
  obtain ⟨hj0, hjk, -, -⟩ := Hj
  have Hif' : ¬ sint.Z j < sint.Z sl2.len := by
    first | exact Hif | (intro h; apply Hif; simp [h])
  have hjl : sint.nat j = mm.kvs.length := by
    have h1 := Hsll.1
    rw [Hlen] at h1
    simp only [sint.nat, sint.Z] at h1 hj0 hjk Hif' ⊢
    omega
  (try simp only [show decide (sint.Z j < sint.Z sl2.len) = false from decide_eq_false Hif',
    _root_.decide_true, ↓reduceIte])
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
  -- `initialRev` is the first page's revision
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ getResp_ptr ↦ resp ∗ wc_ptr ↦ wc ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦
        W64 (σ0.rev : Int)))) $$ [Hir getResp wc]
  · rcases hph with ⟨hw, he⟩ | ⟨hw, hir, -, hpos⟩
    · subst hw
      rw [decide_eq_true rfl]
      (try wp_auto)
      rw [hrevσ, he]
      iframe
      ipureintro; rfl
    · have hwne : wr ≠ W64 0 := by
        rw [hw]; intro h
        have := hfit0.lt
        apply Nat.ne_of_gt hpos
        word
      rw [decide_eq_false hwne]
      (try wp_auto)
      rw [hir]
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, getResp, wc, Hir⟩
  subst hv
  (try wp_auto)
  have hmemF : ∀ v ∈ mm.kvs, v ∈ (σ0.at σ0.rev).kvs := fun v hv =>
    (List.mem_filter.1 (hpre.subset hv)).1
  cases hmm : mm.more
  · -- no more: the initial raw events are queued
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iframe Hpe
    ileft
    isplitr
    · ipureintro; rfl
    iexists lb0, σ0
    iframe HQ0 Hir
    isplitr
    · ipureintro; exact ⟨hst0, hfit0⟩
    iExactEq Hps
    rw [hjl, List.take_length, hnm hmm, hI]
  -- more: the next page, from the last key and `"\x00"`, at the first page's revision
  obtain ⟨hlen10, hlt, hrec⟩ := hmo hmm
  subst hrec
  icases Hlk with (%h0 | ⟨%kvl, %hkvl, #Hksl'⟩)
  · exfalso; rw [hjl, hlen10] at h0; cases h0
  rw [hjl, hlen10] at hkvl
  have hkvlm : kvl ∈ mm.kvs := List.mem_of_getElem? hkvl
  have hσpos : 0 < σ0.rev := by
    have := hwh0 kvl (hmemF kvl hkvlm); omega
  have hfit0' := hfit0.lt
  have hσne : W64 (σ0.rev : Int) ≠ W64 0 := by intro h; apply Nat.ne_of_gt hσpos; word
  (try wp_auto)
  wp_apply (wp_bytes_to_string lkv kvl.key) $$ [$Hksl'] as -
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ withRev_ptr ↦ W64 (σ0.rev : Int) ∗
      getResp_ptr ↦ resp ∗
      ∃ osl' : GoSlice, opts_ptr ↦ osl' ∗ optsOwn (GF := GF) osl' (syncGsOf kp true (W64 (σ0.rev : Int))))))
    $$ [withRev opts Ho getResp]
  · rcases hph with ⟨hw, he⟩ | ⟨hw, hir, -, -⟩
    · subst hw
      rw [decide_eq_true rfl]
      (try wp_auto)
      rw [hrevσ, ← he]
      wp_apply wp_WithRev as %f3 #Hf3
      wp_apply (wp_slice_literal (V := GoFunc) [f3])
      isplitr
      · ipureintro; rfl
      iintro %sl3 ⟨Hsl3, -⟩
      (try wp_auto)
      wp_apply (wp_optsOwn_append _ _ _ f3 (withRevM (W64 (σ0.rev : Int)))) $$ [Ho Hsl3] as %o3 Ho3
      · iframe Ho Hsl3 Hf3
      (try wp_auto)
      iframe
      isplitr
      · ipureintro; rfl
      iExactEq Ho3
      unfold syncGsOf
      rw [if_neg hσne, if_pos rfl]
    · have hwne : wr ≠ W64 0 := by rw [hw]; exact hσne
      rw [decide_eq_false hwne]
      (try wp_auto)
      rw [← hw]
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, withRev, getResp, %osl', opts, Ho⟩
  subst hv
  (try wp_auto)
  wp_for_post
  obtain ⟨kv', hlast, hnext⟩ := syncNext (σ0.at σ0.rev) kp pk 10000 (by decide) hlt
  have hkvs : mm.kvs = (fromL (σ0.at σ0.rev) kp true pk).take 10000 := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hkv' : kv' = kvl := by
    rw [← hkvs, List.getLast?_eq_getElem?, hlen10] at hlast
    rw [hlast] at hkvl; cases hkvl; rfl
  subst hkv'
  have hkey := hwh0 kv' (hmemF kv' hkvlm)
  have hpref : kp <+: kv'.key := by
    have := (List.mem_filter.1 (hpre.subset hkvlm)).2
    simp only [kInScope, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  iframe
  iexists kv'.key ++ [W8 0], W64 (σ0.rev : Int), lkv, resp, GoInterface.nil, W64 (σ0.rev : Int), osl',
    I ++ mm.kvs.map KRaw.kv
  iframe
  isplitl [Hps]
  · iExactEq Hps
    rw [hjl, List.take_length]
  isplitr
  · ipureintro
    refine ⟨hpref.trans (List.prefix_append _ _), ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  iright
  iexists lb0, σ0
  iframe HQ0
  ipureintro
  refine ⟨rfl, rfl, hσpos, rfl, hst0, hfit0, ?_⟩
  rw [hnext, List.append_assoc, ← List.map_append, hkvs, List.take_append_drop]
  rw [hinS] at hI ⊢
  exact hI

end proof

end k8s
end EtcdGrove
end Perennial
