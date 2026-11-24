/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__genID.lean`
(claim #34, stage 2, 2026-11-25). Lean-first.

`MemberIDs()` (the sorted ids, `n` of them), `b := make([]byte, 8*n)`, the range over the ids writes
each id's big-endian bytes at `b[8*i:]` (the loop's invariant: the first `i` ids' bytes, then zeros,
`genBytes`), `sha1.Sum(b)` (Perennial's proved spec, its environment premise), and `c.cid` is the
big-endian word of the hash's first eight bytes (`hash[:8]`, a slice of the local array).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__genID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberIDs
public import Spec.encoding.binary.bigEndian__PutUint64
public import Spec.encoding.binary.bigEndian__Uint64
public import Perennial.Spec.crypto.sha1.Sum

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

attribute [-instance] pure_wp_slice_for_range

/-- The bytes `b` holds after `k` of the range's iterations: the first `k` ids' big-endian bytes,
then zeros. -/
def membership.genBytes (ids : List w64) (k : Nat) : List w8 :=
  (ids.take k).flatMap u64Be ++ List.replicate (8 * (ids.length - k)) (zero_val w8)

theorem membership.flatMap_u64Be_length (l : List w64) : (l.flatMap u64Be).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, u64Be_length, ih]; omega

theorem membership.genBytes_take (ids : List w64) (k : Nat) (hk : k ≤ ids.length) :
    (membership.genBytes ids k).take (8 * k) = (ids.take k).flatMap u64Be := by
  unfold membership.genBytes
  have h : ((ids.take k).flatMap u64Be).length = 8 * k := by
    rw [membership.flatMap_u64Be_length, List.length_take]; omega
  rw [List.take_append_of_le_length (Nat.le_of_eq h.symm), List.take_of_length_le (Nat.le_of_eq h)]

theorem membership.genBytes_drop (ids : List w64) (k : Nat) (hk : k < ids.length) :
    (membership.genBytes ids k).drop (8 * k) =
      List.replicate 8 (zero_val w8) ++ List.replicate (8 * (ids.length - (k + 1))) (zero_val w8) := by
  unfold membership.genBytes
  have h : ((ids.take k).flatMap u64Be).length = 8 * k := by
    rw [membership.flatMap_u64Be_length, List.length_take]; omega
  rw [List.drop_append_of_le_length (Nat.le_of_eq h.symm), List.drop_of_length_le (Nat.le_of_eq h),
    List.nil_append, List.replicate_append_replicate]
  congr 1; omega

theorem membership.genBytes_succ (ids : List w64) (k : Nat) (x : w64) (hx : ids[k]? = some x) :
    membership.genBytes ids (k + 1) =
      (ids.take k).flatMap u64Be ++ (u64Be x ++ List.replicate (8 * (ids.length - (k + 1))) (zero_val w8)) := by
  unfold membership.genBytes
  rw [List.take_add_one, hx]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem membership.genBytes_all (ids : List w64) :
    membership.genBytes ids ids.length = ids.flatMap u64Be := by
  unfold membership.genBytes
  simp

theorem membership.genBytes_zero (ids : List w64) :
    membership.genBytes ids 0 = List.replicate (8 * ids.length) (zero_val w8) := by
  unfold membership.genBytes
  simp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `a[0:8]` of a 20-byte array (the array's other bytes dropped). -/
theorem membership.array20_prefix8 (p : Loc) (bs : List w8) :
    (p ↦ (array.mk 20 bs : GoArray w8 20) : IProp GF) ⊢
      slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) p) (W64 8 - W64 0) (W64 20 - W64 0) ↦*
        bs.take 8 := by
  iintro Ha
  icases (array_split (W64 8) p (DFrac.own 1) 20 (array.mk 20 bs) ⟨by decide, by decide⟩).1 $$ Ha
    with ⟨H1, -⟩
  have h0 : sint.Z (W64 0) = 0 := rfl
  have e1 : (W64 8 - W64 0 : w64) = W64 8 := by decide
  have e2 : (W64 20 - W64 0 : w64) = W64 20 := by decide
  have e3 : sint.nat (W64 8) = 8 := by decide
  rw [h0, go.arrayIndexRef_0, e1, e2, e3]
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  simp only
  iframe H1
  ipureintro; decide

theorem membership.RaftCluster.genID.wp_proof
    (hMemberIDs : membership.RaftCluster.MemberIDs.spec (GF := GF) (hG := hG))
    (hPut : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (hUint : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG))
    (hSum : crypto.sha1.Sum.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.genID.spec (GF := GF) (hG := hG) := by
  intro c q ms mem cid0 hfips hids hsz
  wp_start as ⟨Hmu, Hmem, Hcid⟩
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hsha : isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hMemberIDs c q ms mem hids (by omega)) $$ [$Hmu $Hmem]
    as %sl ⟨Hmu, Hmem, %ids, Hids, %Hsorted⟩
  obtain ⟨hsrt, hlen⟩ := Hsorted
  ihave %Hil := ownSlice_len _ _ _ $$ Hids
  have hn : ids.length ≤ 2 ^ 58 := by omega
  (try wp_auto)
  have hmul : sint.Z (W64 8 * sl.len) = 8 * ids.length := by
    have h1 := Hil.1; have h2 := Hil.2; word
  wp_apply (wp_slice_make2 (V := w8) (W64 8 * sl.len)) as %bsl ⟨Hb, Hbcap⟩
  · ipureintro; omega
  have hrep : sint.nat (W64 8 * sl.len) = 8 * ids.length := by
    show (sint.Z (W64 8 * sl.len)).toNat = _
    rw [hmul]; omega
  ihave Hb : (bsl ↦* membership.genBytes ids 0 : IProp GF) $$ [Hb]
  · rw [membership.genBytes_zero, ← hrep]; iexact Hb
  (try wp_auto)
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hb
  have hgl : (membership.genBytes ids 0).length = 8 * ids.length := by
    rw [membership.genBytes_zero, List.length_replicate]
  wp_func_lits
  wp_apply (membership.wp_slice_for_range_ro (V := w64) _ sl ids (DFrac.own 1) _
    (fun k => iprop(b_ptr ↦ bsl ∗ bsl ↦* membership.genBytes ids k ∗
      (∃ x : w64, id_ptr ↦ x) ∗ (∃ y : w64, i_ptr ↦ y)))) $$ Hids [b Hb id i]
  · iframe b Hb
    isplitl [id]
    · iexists _; iexact id
    · iexists _; iexact i
  · imodintro
    iintro %k %x %hx ⟨b, Hb, ⟨%x0, id⟩, ⟨%y0, i⟩⟩ Hids
    have hk : k < ids.length := (List.getElem?_eq_some_iff.1 hx).1
    have hk58 : k < 2 ^ 58 := by omega
    (try wp_auto)
    have hlo : sint.Z (W64 8 * W64 (k : Int)) = 8 * k := by word
    have Hrb : 0 ≤ sint.Z (W64 8 * W64 (k : Int)) ∧ sint.Z (W64 8 * W64 (k : Int)) ≤ sint.Z bsl.len ∧
        sint.Z bsl.len ≤ sint.Z bsl.cap := by
      have h1 := Hbl.1; have h2 := Hbl.2
      refine ⟨by omega, ?_, Hbwf.2⟩
      rw [hgl] at h1; word
    simp only [Hrb, _root_.and_self, ↓reduceIte]
    (try wp_auto)
    have hlo' : sint.nat (W64 8 * W64 (k : Int)) = 8 * k := by
      show (sint.Z (W64 8 * W64 (k : Int))).toNat = _
      rw [hlo]; omega
    icases (ownSlice_split_all (W64 8 * W64 (k : Int)) bsl _ _ ⟨Hrb.1, Hrb.2.1⟩).1 $$ Hb
      with ⟨Hb1, Hb2⟩
    rw [hlo', membership.genBytes_take ids k (by omega), membership.genBytes_drop ids k hk]
    wp_apply (hPut (slice.slice bsl w8 (W64 8 * W64 (k : Int)) bsl.len)
      (List.replicate 8 (zero_val w8)) (List.replicate (8 * (ids.length - (k + 1))) (zero_val w8)) x
      (by simp)) $$ [$Hb2] as Hb2
    ihave Hb := (ownSlice_split_all (W64 8 * W64 (k : Int)) bsl (DFrac.own 1)
      (membership.genBytes ids (k + 1)) ⟨Hrb.1, Hrb.2.1⟩).2 $$ [Hb1 Hb2]
    · have h1 : ((ids.take k).flatMap u64Be).length = 8 * k := by
        rw [membership.flatMap_u64Be_length, List.length_take]; omega
      rw [hlo', membership.genBytes_succ ids k x hx, List.take_append_of_le_length (Nat.le_of_eq h1.symm),
        List.take_of_length_le (Nat.le_of_eq h1), List.drop_append_of_le_length (Nat.le_of_eq h1.symm),
        List.drop_of_length_le (Nat.le_of_eq h1), List.nil_append]
      iframe Hb1 Hb2
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iframe b Hb Hids
    isplitl [id]
    · iexists _; iexact id
    · iexists _; iexact i
  iintro ⟨b, Hb, -, -⟩ Hids
  rw [membership.genBytes_all]
  (try wp_auto)
  wp_apply (hSum bsl (DFrac.own 1) (ids.flatMap u64Be) hfips) $$ [$Hb] as Hb
  (try wp_auto)
  have hcond : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ (20 : Int) := by
    decide
  try simp only [hcond, _root_.and_self, ↓reduceIte]
  (try wp_auto)
  ihave %Hhl := array_len _ _ _ _ $$ hash
  ihave Hh := membership.array20_prefix8 hash_ptr (crypto.sha1.sha1 (ids.flatMap u64Be)) $$ hash
  have hl8 : ((crypto.sha1.sha1 (ids.flatMap u64Be)).take 8).length = 8 := by
    rw [List.length_take]; omega
  wp_apply (hUint _ ((crypto.sha1.sha1 (ids.flatMap u64Be)).take 8) [] (DFrac.own 1) hl8)
    $$ [Hh] as Hh
  · rw [List.append_nil]; iexact Hh
  (try wp_auto)
  iapply HΦ
  iframe Hmu Hmem
  iexists ids
  unfold membership.clusterIdOf
  iframe Hcid
  ipureintro; exact hsrt

end proof

end EtcdGrove
end Perennial
