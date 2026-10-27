/-
Lean-first (no Rocq counterpart).

The proof of `(*store).stateFromEtcdResponse` (decode errors not expected, `ignoreNotFound`
false): the fresh object (`v.Addr().Interface()` is not a `runtime.Unstructured`, so
`reflect.New(v.Type())`, the zero object by the contract), then "not found" or the key-value's
value through the transformer and the decoder, which succeed since it decodes.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__stateFromEtcdResponse
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyNotFoundError
public import Spec.reflect.New
public import Spec.reflect.Value__Addr
public import Spec.reflect.Value__Type
public import Spec.reflect.Value__Interface

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
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
variable [reflect.Assumptions]

theorem store.stateFromEtcdResponse.wp_proof
    (wp_NewKeyNotFoundError : storage.NewKeyNotFoundError.spec (GF := GF) (hG := hG))
    (wp_New : reflect.New.spec (GF := GF) (hG := hG))
    (wp_Addr : reflect.Value.Addr.spec (GF := GF) (hG := hG))
    (wp_Type : reflect.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Interface : reflect.Value.Interface.spec (GF := GF) (hG := hG)) :
    store.stateFromEtcdResponse.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ctx kvp mkv rev key v p hdec
  wp_start as ⟨#Hst, #Hkv, %Hv⟩
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
    #Hcl, #Hone, #Hregs, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, #Henc, #Hver, #Htr, #Hdec, #Hzero⟩
  ihave #Prf : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  ihave #Psg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Addr v_ptr (DFrac.own 1) v c.S.objTy p $$ [$v] as %w ⟨Hvp, %Hw⟩
  · iframe #
    ipureintro; exact Hv
  wp_apply wp_Interface w c.S.objTy p $$ []
  · iframe #
    ipureintro; exact Hw
  obtain ⟨hObj, hUns⟩ := Hty
  simp only [hUns, Bool.false_eq_true, ↓reduceIte]
  (try wp_auto)
  wp_apply wp_Type v_ptr (DFrac.own 1) v c.S.objTy p $$ [$Hvp] as %rt ⟨Hvp, %Hrt⟩
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  wp_apply wp_New rt c.S.objTy $$ [] as %w' %p' ⟨%Hw', Hnew⟩
  · iframe #
    ipureintro; exact Hrt
  wp_apply wp_Interface w' c.S.objTy p' $$ []
  · iframe #
    ipureintro; exact Hw'.1
  simp only [hObj, ↓reduceIte]
  (try wp_auto)
  cases mkv with
  | none =>
    iunfold kubernetes.kvOut at Hkv
    icases Hkv with %HKV
    wp_if_destruct
    · (try wp_auto)
      iapply wp_fupd
      wp_apply wp_NewKeyNotFoundError key rev as %ep Hep
      ipersist Hep
      imodintro
      iapply HΦ
      simp only [storageErrIs]
      isplitr
      · ipureintro; trivial
      iexists ep
      iframe Hep
      ipureintro; rfl
    · exact absurd HKV Hif
  | some kv =>
    iunfold kubernetes.kvOut at Hkv
    icases Hkv with ⟨%HKV, #Hkvv⟩
    obtain ⟨o, b, hd⟩ := hdec kv rfl
    obtain ⟨d, st, hfs, hdc, -⟩ := ObjCodec.dec_some _ _ _ _ hd
    wp_if_destruct
    · exact absurd rfl HKV
    iunfold txn.kvIs at Hkvv
    icases Hkvv with ⟨%ksl, %vsl, #Hkey, #Hksl, #Hcrev, #Hmod, #Hver, #Hval, #Hvsl, #Hlease⟩
    (try wp_auto)
    iunfold transformerOk at Htr
    icases Htr with ⟨#HtrFrom, -⟩
    wp_apply HtrFrom $$ [$Hvsl] as %dsl %st' %terr Htres
    rw [hfs]
    icases Htres with ⟨%Hterr, #Hdsl⟩
    obtain ⟨rfl, rfl⟩ := Hterr
    (try wp_auto)
    imod (c.S.newObj p') $$ Hnew with Hobj
    iunfold decoderOk at Hdec
    wp_apply Hdec $$ [$Hdsl] [$Hobj] as %derr Hdres
    rw [hdc]
    icases Hdres with ⟨%Hderr, Hobj⟩
    subst Hderr
    (try wp_auto)
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hstp, %Hnn⟩
    have hz : (zero_val k8s_io.apiserver.pkg.storage.ResponseMeta).TTL' = W64 0 := rfl
    isimp only [hz] at Hstp «$v0»
    iapply HΦ
    isplitl []
    · ipureintro; rfl
    iexists ⟨o, kv.modRev, d, true, _⟩
    isplitl
    · iunfold ownState
      iexists (interface.mkOk (go.GoType.PointerType c.S.objTy) #p'), «$v0_ptr», dsl
      iframe Hstp Hobj Hdsl
      isplitr
      · ipureintro; exact Hnn
      iexact «$v0»
    ipureintro
    exact ⟨rfl, hfs, hdc, rfl⟩

end proof

end k8s
end EtcdGrove
end Perennial
