/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/urlPicker__unreachable.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.urlPicker__unreachable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

omit [FfiSyntax] in
/-- `(i + 1) % n` (Go's signed `%`) stays an index for `0 ≤ i < n`. -/
theorem srem_succ_bounds (a n : w64) (ha : 0 ≤ sint.Z a) (ha' : sint.Z a < sint.Z n) :
    0 ≤ sint.Z (BitVec.srem (a + W64 1) n) ∧ sint.Z (BitVec.srem (a + W64 1) n) < sint.Z n := by
  have h1 : sint.Z (a + W64 1) = sint.Z a + 1 := by word
  have e : sint.Z (BitVec.srem (a + W64 1) n) = (sint.Z a + 1) % sint.Z n := by
    show (BitVec.srem (a + W64 1) n).toInt = _
    rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg (by change 0 ≤ sint.Z (a + W64 1); omega)]
    change sint.Z (a + W64 1) % sint.Z n = _
    rw [h1]
  rw [e]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

theorem rafthttp.urlPicker.unreachable.wp_proof :
    rafthttp.urlPicker.unreachable.spec (GF := GF) (hG := hG) := by
  intro pk P u
  wp_start as #Hpk
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold pickerOk at Hpk
  wp_apply sync.Mutex.wp_Lock _ (pickerInv pk P) $$ [$Hpk] as ⟨Hlocked, Hinv⟩
  iunfold pickerInv at Hinv
  icases Hinv with ⟨%sl, %us, %i, Hurls, #Hus, Hi, %Hok⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hus
  obtain ⟨u', Hu⟩ : ∃ u', us[sint.nat i]? = some u' := ⟨_, List.getElem?_eq_getElem (by word)⟩
  rw [if_pos (by word)]
  icases ownSlice_elem_acc (sint.Z i) u' sl DFrac.discard us Hok.1 Hu $$ Hus with ⟨#Hue, -⟩
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  have Hlen0 : ¬ sint.Z sl.len = 0 := by word
  all_goals try (rw [if_neg Hlen0]; wp_auto)
  all_goals
    wp_apply sync.Mutex.wp_Unlock $$ [$Hpk $Hlocked Hurls Hi]
    · inext
      iunfold pickerInv
      iexists sl, us, _
      iframe
      iframe #
      ipureintro
      refine ⟨?_, ?_, Hok.2.2⟩
      all_goals first | exact Hok.1 | exact Hok.2.1 |
        (have := srem_succ_bounds i sl.len Hok.1 (by word); first | exact this.1 | word)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
