/-
Port of `election_proof/proof_extend.v`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.extend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
  intro dst vals ds vs dq1 dq2 Hcap
  wp_start as ⟨Hdst, Hvals⟩
  iunfold entsPts at Hdst Hvals
  icases Hdst with ⟨%ls1, Hdst, #Hb1⟩
  icases Hvals with ⟨%ls2, Hvals, #Hb2⟩
  ihave %Hbl1 := entsBig_length $$ Hb1
  ihave %Hbl2 := entsBig_length $$ Hb2
  rw [← Hbl1, ← Hbl2] at Hcap
  wp_auto
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hdst
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hvals
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hdst
  have Hl1 : (ls1.length : Int) = sint.Z dst.len := by word
  have Hl2 : (ls2.length : Int) = sint.Z vals.len := by word
  rcases Classical.em ((ls1.length : Int) + (ls2.length : Int) < 2 ^ 63) with Hfits | Hbig
  case inr =>
    -- `need` wraps negative: `need <= cap(dst)`, and `append(dst, vals...)` runs, whose
    -- model assumes the lengths do not overflow (see the spec)
    have Hwrap : sint.Z (dst.len + vals.len) < 0 := by word
    wp_if_destruct
    · wp_func_call
      wp_call
      wp_apply wp_sumAssumeNoOverflowSigned with %Hov
      exfalso; omega
    · exfalso; omega
  have Hneed : sint.Z (dst.len + vals.len) = (ls1.length : Int) + (ls2.length : Int) := by
    word
  have Hneed' : sint.nat (dst.len + vals.len) = ls1.length + ls2.length := by word
  wp_if_destruct
  · exfalso; omega
  wp_apply wp_slice_make3 (V := Loc) (dst.len + vals.len) (dst.len + vals.len)
    (by omega) as %buf ⟨Hbuf, Hbuf_cap, %Hbufcap⟩
  rw [Hneed']
  wp_apply wp_slice_copy $$ [$Hbuf $Hdst] as %n1 ⟨%Hn1, Hbuf, Hdst⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate,
    show ls1.length + ls2.length - ls1.length = ls2.length by omega]
  ihave %Hlenb := ownSlice_len _ _ _ $$ Hbuf
  simp only [List.length_append, List.length_replicate] at Hlenb
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
  icases (ownSlice_split_all dst.len buf _ _ (by word)).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
  rw [List.take_left' (by word), List.drop_left' (by word)]
  wp_auto
  wp_apply wp_slice_copy (V := Loc) $$ [$Hbuf2 $Hvals] as %n2 ⟨%Hn2, Hbuf2, Hvals⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate,
    Nat.sub_self, List.replicate_zero, List.append_nil]
  ihave Hbuf := ownSlice_combine dst.len buf (DFrac.own 1) ls1 ls2 (W64 0) buf.len
    ⟨by word, by word, by word, by word⟩ $$ Hbuf1 Hbuf2
  ihave Hbuf := ownSlice_trivial_slice_2 _ _ _ $$ Hbuf
  iapply HΦ
  iframe Hbuf_cap
  isplitl [Hbuf]
  · iunfold entsPts
    iexists ls1 ++ ls2
    iframe Hbuf
    iapply entsBig_app $$ [Hb1 Hb2]
    iframe Hb1 Hb2
  isplitl [Hdst]
  · iunfold entsPts; iexists ls1; iframe Hdst Hb1
  · iunfold entsPts; iexists ls2; iframe Hvals Hb2

end proof

end EtcdGrove
end Perennial
