/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/AlarmType__String.lean`, over the trusted model of
protoc-gen-go's `AlarmType.String` (`TrustedCode/go_etcd_io/etcd/api/v3/etcdserverpb.lean`,
etcd-grove#39, 2026-11-23): the lookup in `AlarmType_name`, which `etcdserverpb`'s package fact holds
read-only (`etcdserverpb.alarmTypeNames`), else `strconv.Itoa`; the call through the pointer reads
`*p` (goose's `ptr_String_unfold`). (Until 2026-11-23 a trust-boundary axiom.)
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType__String
public import Spec.strconv.Itoa

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- The table's names are ASCII. -/
private theorem alarmTypeNames_ascii (a : w32) (s : GoString)
    (h : go_etcd_io.etcd.cache.v3.etcdserverpb.alarmTypeNames !! a = some s) : asciiStr s := by
  unfold go_etcd_io.etcd.cache.v3.etcdserverpb.alarmTypeNames at h
  simp only [GMap.lookup_insert_eq_iff, GMap.lookup_empty] at h
  repeat' split at h
  all_goals cases h
  all_goals (unfold asciiStr; decide)

/-- A decimal number's characters are ASCII (a sign and digits). -/
private theorem fmtInt10_ascii (n : w64) : asciiStr (fmtInt n (W64 10)) := by
  have hu : ∀ m : w64, asciiStr (fmtUint m (W64 10)) := by
    intro m b hb
    unfold fmtUint at hb
    rw [dif_pos (by decide)] at hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
    have hlt : d < 10 := by simpa using baseDigits_lt _ _ _ d hd
    unfold digitChar; rw [if_pos hlt]; simp [W8]; omega
  unfold fmtInt
  split
  · intro b hb
    rcases List.mem_cons.1 hb with rfl | h
    · decide
    · exact hu _ b h
  · exact hu n

theorem etcdserverpb.AlarmType.String.wp_proof
    (hItoa : strconv.Itoa.spec (GF := GF) (hG := hG)) :
    etcdserverpb.AlarmType.String.spec (GF := GF) (hG := hG) := by
  intro p a dq
  wp_start as Hp
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave Hfact : (go_etcd_io.etcd.cache.v3.etcdserverpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hfact with ⟨-, -, ⟨%m, #Hg, #Hm⟩, -⟩
  -- the trusted model names the translation's type and table by their names
  have hty : (go_etcd_io.etcd.api.v3.etcdserverpb.model.AlarmType : go.GoType) =
      go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType.ty := by with_unfolding_all rfl
  have hnm : (go_etcd_io.etcd.api.v3.etcdserverpb.model.AlarmType_name : GoString) =
      go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType_name := by with_unfolding_all rfl
  wp_auto
  -- the value method's resolution (`go.int32` is not an interface: a local instance, as in
  -- `kvdurable/getEntry.lean`)
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_auto
  wp_method_call
  wp_call
  unfold go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType.String.impl
  simp only [hty, hnm]
  wp_auto
  -- the table kept opaque (`wp_auto`'s `simp` would compute its lookups)
  have hA := alarmTypeNames_ascii a
  generalize go_etcd_io.etcd.cache.v3.etcdserverpb.alarmTypeNames = M at hA ⊢
  cases hk : M !! a with
  | some s =>
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string m M a DFrac.discard)
      $$ Hm as -
    rw [hk]
    simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
    wp_auto
    iapply HΦ; iframe Hp; ipureintro; exact hA s hk
  | none =>
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string m M a DFrac.discard)
      $$ Hm as -
    rw [hk]
    simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    wp_auto
    wp_apply hItoa $$ Hsc as %str %Hstr
    rw [Hstr]
    iapply HΦ; iframe Hp; ipureintro; exact fmtInt10_ascii _

end proof

end EtcdGrove
end Perennial
