/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3alarm/AlarmStore__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Get

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Assumptions]

/-- `TypeRepr` of `AlarmStore` straight from its `TypeAssumptions` (as `InvServer.lean` does
for the server's structs): otherwise the `StructFieldRef` step finds it through the struct's
`IntoValTyped`, built from its fields', and `be`'s type (`schema.AlarmBackend`, axiomatized) has
`sorry` instances. -/
instance (priority := high) alarmStore_typeRepr : TypeRepr v3alarm.AlarmStore.ty v3alarm.AlarmStore :=
  go.type_repr_underlying (u := v3alarm.AlarmStore.underlying)
instance (priority := high) alarmStore_typeRepr_u :
    TypeRepr v3alarm.AlarmStore.underlying v3alarm.AlarmStore :=
  go.type_repr_underlying (u := v3alarm.AlarmStore.underlying)

/-- What `Get` accumulates in its result `ret`: some owned slice. -/
def alarmRet (ret : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (l : List Loc), ret ↦ sl ∗ sl ↦* l ∗
    ownSliceCap Loc sl (DFrac.own 1))

theorem alarmRet_nil (ret : Loc) : ret ↦ (zero_val GoSlice) ⊢ alarmRet (GF := GF) ret := by
  iintro Hr
  iunfold alarmRet
  iexists slice.nil, []
  iframe Hr
  isplitl []
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil

theorem v3alarm.AlarmStore.Get.wp_proof :
    v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG) := by
  intro a aty
  wp_start as #Ha
  iunfold isAlarmStore at Ha
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Ha] as ⟨Hlocked, HR⟩
  iunfold alarmLockInv at HR
  icases HR with ⟨%tm, %gm, Htypes, Hm, Hin⟩
  ihave Hret := alarmRet_nil ret_ptr $$ ret
  (try wp_auto)
  wp_if_destruct
  · -- every type
    (try wp_func_lits)
    (try wp_auto)
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_keys : List w32) (_i : Int) => iprop(alarmRet ret_ptr ∗
        (∃ x : GoMap, t_ptr ↦ x) ∗ [∗map] _k ↦ t ∈ gm, ∃ im : GMap w64 Loc, t ↦$ im)) $$ Hm
    iintro %keys %_
    isplitl [Hret t Hin]
    · iframe Hret Hin; iexists _; iframe t
    isplitr
    · imodintro
      iintro %i %key %tv ⟨%Hkey, %Htv⟩ ⟨Hret, ⟨%x, Ht⟩, Hin⟩
      (try wp_auto)
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_k : w32) (t : GoMap) =>
          iprop(∃ im : GMap w64 Loc, t ↦$ im)) Htv).1 $$ Hin with ⟨⟨%im, Him⟩, Hback⟩
      (try wp_func_lits)
      (try wp_auto)
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (_keys : List w64) (_i : Int) => iprop(alarmRet ret_ptr ∗
          (∃ x : Loc, m_ptr ↦ x))) $$ Him
      iintro %keys' %_
      isplitl [Hret m]
      · iframe Hret; iexists _; iframe m
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ ⟨Hret, %x, Hmp⟩
        (try wp_auto)
        iunfold alarmRet at Hret
        icases Hret with ⟨%sl, %l, Hret, Hsl, Hcap⟩
        (try wp_auto)
        wp_apply wp_slice_literal (V := Loc) [vv]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        (try wp_auto)
        wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2] as %sl3 ⟨Hsl, Hcap, -⟩
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hret Hsl Hcap]
        · iunfold alarmRet; iexists sl3, _; iframe
        · iexists vv; iframe
      iintro ⟨Hret, Hmp⟩ Him
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iframe Hret
      isplitl [Ht]
      · iexists _; iframe Ht
      iapply Hback
      iexists im; iframe Him
    iintro ⟨Hret, -, Hin⟩ Hm
    (try wp_auto)
    iunfold alarmRet at Hret
    icases Hret with ⟨%sl, %l, Hret, Hsl, Hcap⟩
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Ha $Hlocked Htypes Hm Hin]
    · inext
      iunfold alarmLockInv
      iexists tm, gm
      iframe
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- one type: its set, if any
    (try wp_auto)
    wp_apply (wp_map_lookup1 (K := w32) (V := GoMap) _ _ tm gm aty) $$ [$Hm] as Hm
    (try wp_func_lits)
    (try wp_auto)
    cases hlk : gm !! aty with
    | none =>
      simp only [Option.getD_none]
      rw [show (zero_val GoMap : GoMap) = map.nil from rfl]
      (try wp_auto)
      iunfold alarmRet at Hret
      icases Hret with ⟨%sl, %l, Hret, Hsl, Hcap⟩
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Ha $Hlocked Htypes Hm Hin]
      · inext
        iunfold alarmLockInv
        iexists tm, gm
        iframe
      (try wp_auto)
      iapply HΦ
      itrivial
    | some tv =>
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_k : w32) (t : GoMap) =>
          iprop(∃ im : GMap w64 Loc, t ↦$ im)) hlk).1 $$ Hin with ⟨⟨%im, Him⟩, Hback⟩
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (_keys : List w64) (_i : Int) => iprop(alarmRet ret_ptr ∗
          (∃ x : Loc, m_ptr ↦ x))) $$ Him
      iintro %keys' %_
      isplitl [Hret m]
      · iframe Hret; iexists _; iframe m
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ ⟨Hret, %x, Hmp⟩
        (try wp_auto)
        iunfold alarmRet at Hret
        icases Hret with ⟨%sl, %l, Hret, Hsl, Hcap⟩
        (try wp_auto)
        wp_apply wp_slice_literal (V := Loc) [vv]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        (try wp_auto)
        wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2] as %sl3 ⟨Hsl, Hcap, -⟩
        (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        isplitl [Hret Hsl Hcap]
        · iunfold alarmRet; iexists sl3, _; iframe
        · iexists vv; iframe
      iintro ⟨Hret, Hmp⟩ Him
      (try wp_auto)
      iunfold alarmRet at Hret
      icases Hret with ⟨%sl, %l, Hret, Hsl, Hcap⟩
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Ha $Hlocked Htypes Hm Hback Him]
      · inext
        iunfold alarmLockInv
        iexists tm, gm
        iframe
        iapply Hback
        iexists im; iframe Him
      (try wp_auto)
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
