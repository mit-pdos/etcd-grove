/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/decodeReadCtx.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.decodeReadCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.decode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem decodeReadCtx.wp_proof (wp_decode : decode.spec (GF := GF) (hG := hG)) :
    decodeReadCtx.spec (GF := GF) (hG := hG) := by
  intro b d dq
  wp_start as Hb
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_if_destruct
  · have Hd : decodeReadCtxB d = none := by
      unfold decodeReadCtxB; rw [ite_eq_right (by obtain ⟨h1, h2⟩ := Hlen; word)]
    unfold decodeReadCtxRet; rw [Hd]
    iapply HΦ
    iexact Hb
  have H8 : 8 ≤ d.length := by obtain ⟨h1, h2⟩ := Hlen; word
  rw [ite_eq_left (by refine ⟨by decide, by word, Hwf.2⟩)]
  icases (ownSlice_split_all (W64 8) b dq d ⟨by decide, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  wp_apply wp_decode _ (d.drop (sint.nat (W64 8))) dq $$ [$Hb2] as Hb2
  ihave Hb2 : slice.slice b w8 (W64 8) b.len ↦*{dq} d.drop (sint.nat (W64 8)) $$ [Hb2]
  · rw [show sint.nat (W64 8) = 8 from rfl]; iexact Hb2
  ihave Hb := (ownSlice_split_all (W64 8) b dq d ⟨by decide, by word⟩).2 $$ [$Hb1 $Hb2]
  try simp only [show sint.nat (W64 8) = 8 from rfl]
  unfold decodeRet
  cases Hdo : decodeOp (d.drop 8) with
  | none =>
    have Hd : decodeReadCtxB d = none := by
      unfold decodeReadCtxB; rw [ite_eq_left H8, Hdo]
    unfold decodeReadCtxRet; rw [Hd]
    wp_auto
    iapply HΦ
    iexact Hb
  | some x =>
    obtain ⟨i, k, key, v⟩ := x
    wp_auto
    by_cases hk : k = opReadB
    · have Hd : decodeReadCtxB d = some (leToU64 (d.take 8), i, key) := by
        unfold decodeReadCtxB; rw [ite_eq_left H8, Hdo]; simp [hk]
      unfold decodeReadCtxRet; rw [Hd]
      rw [decide_eq_true (show k = W8 3 from hk)]
      wp_auto
      ihave Hb := (show (b ↦*{dq} d : IProp GF) ⊣⊢ b ↦*{dq} (d.take 8 ++ d.drop 8) by
        rw [List.take_append_drop 8 d]; exact .rfl).1 $$ Hb
      wp_apply encoding.binary.wp_LittleEndian_Uint64 b (d.take 8) dq (d.drop 8)
        (by simp; omega) $$ [$Hb] as Hb
      rw [List.take_append_drop 8 d]
      try wp_auto
      iapply HΦ
      iexact Hb
    · have Hd : decodeReadCtxB d = none := by
        unfold decodeReadCtxB; rw [ite_eq_left H8, Hdo]; simp [hk]
      unfold decodeReadCtxRet; rw [Hd]
      rw [decide_eq_false (show ¬ k = W8 3 from hk)]
      wp_auto
      iapply HΦ
      iexact Hb

end proof

end kvreconf
end EtcdGrove
end Perennial
