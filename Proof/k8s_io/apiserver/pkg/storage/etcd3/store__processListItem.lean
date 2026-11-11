/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__processListItem.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__processListItem
public import Spec.reflect.ValueOf
public import Spec.reflect.Value__Set

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver reflectM

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.processListItem.wp_proof
    (wp_ValueOf : reflect.ValueOf.spec (GF := GF) (hG := hG))
    (wp_Set : reflect.Value.Set.spec (GF := GF) (hG := hG)) :
    store.processListItem.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c L ctx kvp kv pred sel emp nf ag v p s os o hdec
  obtain ⟨b, hd⟩ := hdec
  obtain ⟨d, st, hfs, hdc, -⟩ := ObjCodec.dec_some _ _ _ _ hd
  wp_start as ⟨#Hst, #Hlc, #Hsel, #Hnf, #Hctx, %hv, #Hkv, Hp, Hit⟩
  ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
    #Hcl, #Hone, #Hregs, #Hcon, -⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, -, -, #Htr, -, -, -⟩
  iunfold transformerOk at Htr
  icases Htr with ⟨#HtrFrom, -⟩
  iunfold listContractOk at Hlc
  icases Hlc with ⟨#Hlc', #HDec, -, -⟩
  iunfold listContractOk' at Hlc'
  icases Hlc' with ⟨-, -, -, #HApp⟩
  iunfold selPredOk at Hsel
  icases Hsel with ⟨%hsel, #HMatch, -⟩
  iunfold ctxNeverDone at Hctx
  icases Hctx with ⟨%ci, %hci, #HDone⟩
  subst hci
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%ksl, %vsl, #Hkey, #Hksl, #Hcrev, #Hmod, #Hver, #Hval, #Hvsl, #Hlease, %Hkvp⟩
  (try wp_auto)
  wp_apply (wp_bytes_to_string ksl kv.key DFrac.discard) $$ [$Hksl] as -
  (try wp_auto)
  wp_apply HtrFrom $$ [$Hvsl] as %dsl %st' %terr Htres
  rw [hfs]
  icases Htres with ⟨%Hterr, #Hdsl⟩
  obtain ⟨rfl, rfl⟩ := Hterr
  (try wp_auto)
  wp_bind
  iapply HDone
  inext
  (try wp_auto)
  wp_apply_core chan.wp_select_nonblocking_nil
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · iright
      iapply chan.nilClausePre_recv Unit _ _ rfl
    iapply BigAndL.bigAndL_nil.2
    itrivial
  (try wp_auto)
  wp_bind
  iapply HDec $$ %_ %dsl %d %kv.modRev %nf Hdsl Hnf
  inext
  iintro %x %err Hdres
  rw [hdc]
  icases Hdres with ⟨%he, Hobj⟩
  subst he
  (try wp_auto)
  wp_bind
  iapply HMatch $$ %pred_ptr %_ %x %o %_ pred Hobj
  inext
  iintro pred Hobj
  icases persistent_entails_left (c.S.objAt_ptr x o _) $$ Hobj with ⟨Hobj, %Hx⟩
  obtain ⟨q, hq, rfl⟩ := Hx
  cases hs : sel o
  · (try wp_auto)
    iapply HΦ
    iexists s
    iframe
  · (try wp_auto)
    wp_apply (wp_ValueOf c.S.objTy q) as %vv ⟨-, #HElem⟩
    wp_apply HElem as %e %he
    · ipureintro; exact hq
    wp_apply wp_slice_literal (V := _root_.Perennial.reflect.Value) [e]
    isplitr
    · ipureintro; rfl
    iintro %esl ⟨Hesl, -⟩
    (try wp_auto)
    wp_bind
    iapply HApp $$ %v %p %(DFrac.own 1) %s %os %e %_ %(DFrac.own 1) %q %o %_ [] Hp Hit Hesl Hobj
    · ipureintro; exact ⟨hv, he⟩
    inext
    iintro %w %s' %hw Hp Hit' Hesl Hobj
    (try wp_auto)
    wp_apply (wp_Set v_ptr _ v w (go.GoType.SliceType c.S.objTy) p GoSlice s s') $$ [$v $Hp]
      as ⟨v, Hp⟩
    · ipureintro; exact ⟨hv, Or.inr ⟨c.S.objTy, s', rfl, hw, HEq.rfl⟩⟩
    (try wp_auto)
    iapply HΦ
    iexists s'
    iframe

end proof

end k8s
end EtcdGrove
end Perennial
