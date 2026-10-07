/-
Port of `election_proof/proof_extend.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.extend

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The in-place `append` branch is dead by the `cap` premise; what is left is
`make(need, need)`, a `copy` of `dst` into the front and a `copy` of `vals` into the
tail sub-slice `buf[len(dst):]`.

Two things to watch. (1) `need = len(dst) + len(vals)` is a `w64` addition: `Hneed'`
pins `sint.nat (dst.len + vals.len) = |ds| + |vs|` from the `Hfits` premise, and
rewriting with it up front keeps every later `take`/`drop`/`replicate` index a plain
`Nat` so `omega` can see them. (2) `buf[len(dst):]` is a `slice.slice`, and
`wp_slice_copy`'s slice cannot be inferred until the goal has actually been stepped to
the call, hence the `wp_auto` before the second `copy` (the bounds `if` must be
discharged first, or `wp_auto` stops at it).

The tail is split off with `ownSlice_split_all` and put back with `ownSlice_combine`
plus `ownSlice_trivial_slice_2`. -/
theorem extend.wp_proof : extend.spec (GF := GF) (hG := hG) := by
  intro dst vals ds vs dq1 dq2 Hcap Hfits
  wp_start as ⟨Hdst, Hvals⟩
  wp_auto
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hdst
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hvals
  have Hneed : sint.Z (dst.len + vals.len) = (ds.length : Int) + (vs.length : Int) := by
    word
  have Hneed' : sint.nat (dst.len + vals.len) = ds.length + vs.length := by word
  wp_if_destruct
  · exfalso; omega
  wp_apply wp_slice_make3 (V := raftpb.Entry) (dst.len + vals.len) (dst.len + vals.len)
    (by omega) as %buf ⟨Hbuf, Hbuf_cap, %Hbufcap⟩
  rw [Hneed']
  wp_apply wp_slice_copy $$ [$Hbuf $Hdst] as %n1 ⟨%Hn1, Hbuf, Hdst⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate,
    show ds.length + vs.length - ds.length = vs.length by omega]
  ihave %Hlenb := ownSlice_len _ _ _ $$ Hbuf
  simp only [List.length_append, List.length_replicate] at Hlenb
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
  icases (ownSlice_split_all dst.len buf _ _ (by word)).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
  rw [List.take_left' (by word), List.drop_left' (by word)]
  wp_auto
  wp_apply wp_slice_copy (V := raftpb.Entry) $$ [$Hbuf2 $Hvals] as %n2 ⟨%Hn2, Hbuf2, Hvals⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate,
    Nat.sub_self, List.replicate_zero, List.append_nil]
  ihave Hbuf := ownSlice_combine dst.len buf (DFrac.own 1) ds vs (W64 0) buf.len
    ⟨by word, by word, by word, by word⟩ $$ Hbuf1 Hbuf2
  ihave Hbuf := ownSlice_trivial_slice_2 _ _ _ $$ Hbuf
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
