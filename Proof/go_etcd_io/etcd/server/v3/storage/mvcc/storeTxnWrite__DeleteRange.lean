/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__deleteRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.DeleteRange.wp_proof
    (hdel : mvcc.storeTxnWrite.deleteRange.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend key endk k e
  wp_start as ⟨Htw, #Hkey, #Hend, %Hb⟩
  (try wp_auto)
  wp_apply (hdel tw s γ ilog pend key endk k e) $$ [$Htw $Hkey $Hend] as Htw
  · ipureintro; exact Hb
  (try wp_auto)
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  (try wp_auto)
  generalize hks : mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e = ks at *
  have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
    rw [← mvcc.W64_add_one]; simp
  ihave %Hlen := ownSlice_len chs (DFrac.own 1) ps $$ Hchs
  have hpend : pend ++ List.map Change.del ks = [] ↔ chs.len = 0 := by
    obtain ⟨h1, h2⟩ := Hlen
    constructor
    · intro h
      have hz : ps.length = 0 := by rw [Hps, h]; rfl
      rw [← mvcc.W64_sint_nat chs.len h2, ← h1, hz]; rfl
    · intro h
      rw [h] at h1
      exact List.length_eq_zero_iff.1 (by rw [← Hps, h1]; rfl)
  have hkslt : ks.length < 2 ^ 64 := by omega
  wp_if_destruct
  · -- `n == 0`: nothing deleted
    have hks0 : ks.length = 0 := by
      have h := congrArg BitVec.toNat Hif
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkslt] at h
      simpa using h
    have hks : ks = [] := List.length_eq_zero_iff.1 hks0
    subst hks
    simp only [List.map_nil, List.append_nil] at *
    (try wp_auto)
    wp_if_destruct
    · -- `len(tw.changes) > 0`: the pending revision
      trace_state
      (try wp_auto)
      trace_state
      sorry
    · trace_state
      (try wp_auto)
      trace_state
      sorry
  · -- `n != 0`: the pending revision
    have hks : ks ≠ [] := fun h => by subst h; exact Hif rfl
    (try wp_auto)
    trace_state
    wp_pures
    trace_state
    sorry

end proof

end EtcdGrove
end Perennial
