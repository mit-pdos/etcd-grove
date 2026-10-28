/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__rev
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
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

theorem mvcc.watchableStore.rev.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.rev.spec (GF := GF) (hG := hG) := by
  intro s st γ oa
  wp_start as ⟨#Hws, Hrd, HoA⟩
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType store.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType readView.ty) (m := go!"Rev")]
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType watchableStore.ty) (m := go!"Read")]
  wp_auto
  imod ownToks_0 (GF := GF) γ.st.revs with Hnone
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamedSuffix Hs' "S"
  imod mvcc.crevLb_neg γ.st.idx with #Hlbn
  wp_apply (hRead st γ.st _ t 0 [[], []] true (-1) iprop(True) oa) $$ [$Hs $Hrd $Hnone $Hc0S $Hlbn $Htrc $HoA]
    as %mw ⟨%log, %rev, %crev, Htx, -, -, -, %Hpre0, HoA, %HoaL⟩
  · isplitr
    · iintro !>; itrivial
    ipureintro; exact Ht
  (try wp_auto)
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) rev) $$ [$HrevT]
  (try wp_auto)
  ihave Htx : mvcc.isTxnRead mw st γ.st t log rev crev iprop(True) $$ [Hmw Htrw Hrd Hmu HrevMu Hti Htrc]
  · iunfold mvcc.isTxnRead
    iexists p, trw, tr, ti, rt, ranges
    iframe
    iframe #
  ihave Htx' : mvcc.isTxn mw st γ.st t (.read log rev) crev iprop(True) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev iprop(True) $$ Htx'
  ihave Hep : mvcc.txnEndPre γ.st (.read log rev) $$ []
  · simp only [mvcc.txnEndPre]; itrivial
  wp_apply (hEnd t mw st γ.st (.read log rev) crev iprop(True)) $$ [$Htx' $Hep] as ⟨Hrd, -, -, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Hrd HoA
  iexists log
  withPhys_simp
  iframe HcertT
  ipureintro
  have hl := Hpre0.1.length_le
  exact ⟨HneT, HrevT, hl, by have := Hpre0.2.1; omega, HoaL⟩

end proof

end EtcdGrove
end Perennial
