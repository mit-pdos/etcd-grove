/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart): `readView.Rev`'s proof
(`readView__Rev.lean`) with the caller's tokens and certificate passed to `store.Read`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Rev.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.store.Rev.spec (GF := GF) (hG := hG) := by
  intro s rv γ m log₀
  wp_start as ⟨#HRV, #Hrv, Hrd, Htoks, #Hc0⟩
  -- the promoted method (unfolded by `wp_start`): the embedded `ReadView`'s, the `readView`'s
  (try wp_auto)
  wp_method_call; unfold readView.Rev.impl; wp_call
  iunfold mvcc.isReadView at Hrv
  icases Hrv with ⟨%kv, Hrv⟩
  iNamed Hrv
  ihave %Hkvok := mvcc.kvOver_ok kv s $$ Hkvo
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  -- `rv.kv.Read(mode, t)`: the store's, with the caller's tokens and certificate
  imod mvcc.crevLb_neg γ.idx with #Hlbn
  wp_apply (mvcc.kvOver_Read hRead kty kvv s γ _ t m log₀ true (-1) iprop(True) none) $$ [$Hkvo $Hs $Hrd $Htoks $Hc0 $Hlbn $Htrc]
    as %mw ⟨%log, %rev, %crev, Htx, Htoks, -, #Hrok, %Hpin, -, -⟩
  · isplitr
    · iintro !>; itrivial
    isplitr
    · ipureintro; exact Ht
    unfold mvcc.logLent; itrivial
  (try wp_auto)
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  -- `tr.Rev()`: the promoted methods down to `storeTxnCommon.Rev`
  rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) rev) $$ [$HrevT]
  (try wp_auto)
  -- the deferred `tr.End()`: `metricsTxnWrite.End`
  ihave Htx : mvcc.isTxnRead mw s γ t log rev crev iprop(True) $$ [Hmw Htrw Hrd Hmu HrevMu Hti Htrc]
  · iunfold mvcc.isTxnRead
    iexists p, trw, tr, ti, rt, ranges
    iframe
    iframe #
  ihave Htx' : mvcc.isTxn mw s γ t (.read log rev) crev iprop(True) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev iprop(True) $$ Htx'
  ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
  · simp only [mvcc.txnEndPre]; itrivial
  wp_apply (hEnd t mw s γ (.read log rev) crev iprop(True)) $$ [$Htx' $Hep] as ⟨Hrd, -, -, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Hrd Htoks
  iexists log
  withPhys_simp
  iframe HcertT Hrok
  ipureintro
  exact ⟨Hpin.1, Hpin.2.1, HneT, HrevT⟩

/-- **`store.Read`'s candidate at a KV over the store** (`kvOver_read_wp`). -/
theorem mvcc.kvOver_ReadC (hRead : mvcc.store.Read.specC (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s : Loc) (γ : mvcc.MvccName) (mode : w32) (trace : Loc) (te : Bool)
    (Q : mvcc.MvccState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.kvOver (interface.mkOk ty v) s ∗
        mvcc.isMvcc s γ ∗ threadTok ∗ ⌜trace ≠ null⌝ ∗ traceutil.ownTrace trace te ∗
        AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ }> @ ⊤ \ ↑mvcc.mvccN, ∅
          <{ mvcc.mvccState γ σ, COMM Q σ }> }}
      (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        ∃ σ : mvcc.MvccState, mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace (.read σ) ∗ Q σ }} := by
  iintro %Φ ⟨#Hpkg, #Hk, Hrest⟩ HΦ
  iapply mvcc.kvOver_read_wp ty v s mode trace
  iframe Hk
  iapply (hRead s γ mode trace te Q) $$ [Hrest] HΦ
  iframe Hpkg Hrest

/-- **The candidate `Rev`** (`specC`): the store's read view's (`readView.Rev`): a read transaction
(`store.Read.specC`, at the caller's update: its log is the state's), its `Rev`, its `End`. On a
store with watchers, the view is the watchable store's (`isMvccI`'s `isWatchableStore`); a store
without watchers' views are not yet in `isMvccI`. -/
theorem mvcc.store.Rev.wp_proofC
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.specC (GF := GF) (hG := hG))
    (hRev : mvcc.metricsTxnWrite.Rev.specC (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.specC (GF := GF) (hG := hG)) :
    mvcc.store.Rev.specC (GF := GF) (hG := hG) := by
  intro s γ Q
  wp_start as ⟨#Hmv, Htt, Hau⟩
  ihave #Hs1 : mvcc.isMvccI s γ $$ []
  · iunfold mvcc.isMvcc at Hmv; iexact Hmv
  iunfold mvcc.isMvccI at Hs1
  icases Hs1 with ⟨-, -, -, -, -, -, -, -, #Hwsi⟩
  cases hw : γ.watched with
  | false => sorry
  | true =>
  simp only [hw, ↓reduceIte] at *
  iunfold mvcc.isWatchableStore at Hwsi
  iNamed Hwsi
  (try wp_auto)
  wp_method_call; unfold readView.Rev.impl; wp_call
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  ihave #Hko : mvcc.kvOver (interface.mkOk (go.GoType.PointerType watchableStore.ty) #γ.wl) s $$ []
  · iunfold mvcc.kvOver; iright; iexists γ.wl; iframe Hst; ipureintro; rfl
  wp_apply (mvcc.kvOver_ReadC hRead _ _ s γ _ t true Q) $$ [$Hko $Hmv $Htt $Htrc $Hau] as %mw ⟨%σ, Htx, HQ⟩
  · ipureintro; exact Ht
  (try wp_auto)
  wp_apply (hRev mw γ t (.read σ)) $$ [$Htx] as Htx
  (try wp_auto)
  wp_apply (hEnd mw γ t (.read σ) iprop(True) func.nil iprop(True)) $$ [$Htx] as ⟨Htt, -, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Htt
  iexists σ
  iframe HQ
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
