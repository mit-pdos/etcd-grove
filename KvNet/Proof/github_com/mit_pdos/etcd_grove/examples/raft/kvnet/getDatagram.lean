/-
The proof of `KvNet/Spec/.../kvnet/getDatagram.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getDatagram

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- `LittleEndian.Uint64(b[off:])`: `u64At`. -/
private theorem wp_u64_at (b : GoSlice) (q : DFrac) (bs : List w8) (off : w64)
    (h0 : 0 ≤ sint.Z off) (hlen : bs.length = sint.nat b.len) (hb : 0 ≤ sint.Z b.len)
    (hoff : sint.nat off + 8 ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{q} bs }}
      (App (Val ((globalAddr encoding.binary.LittleEndian) @!!
        go.GoType.PointerType encoding.binary.littleEndian.ty @!! go!"Uint64"))
        (Val #(slice.slice b w8 off b.len)))
    {{ RET #(u64At bs (sint.nat off)); b ↦*{q} bs }} := by
  wp_start_folded as ⟨#Hpkg, Hb⟩
  have Hrng : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.len := by
    refine ⟨h0, ?_, le_refl _⟩; word
  icases (ownSlice_slice off b.len b q bs Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  have Hsub : subslice (sint.nat off) (sint.nat b.len) bs =
      (bs.drop (sint.nat off)).take 8 ++ bs.drop (sint.nat off + 8) := by
    have hd : (bs.drop (sint.nat off)).drop 8 = bs.drop (sint.nat off + 8) := by
      simp only [List.drop_drop, Nat.add_comm]
    rw [← hlen]
    simp only [subslice, List.take_length]
    rw [← hd, List.take_append_drop]
  have E2 : (slice.slice b w8 off b.len ↦*{q} subslice (sint.nat off) (sint.nat b.len) bs : IProp GF) ⊣⊢
      slice.slice b w8 off b.len ↦*{q} ((bs.drop (sint.nat off)).take 8 ++ bs.drop (sint.nat off + 8)) := by
    rw [Hsub]; exact .rfl
  ihave Hb2 := E2.1 $$ Hb2
  have hl8 : ((bs.drop (sint.nat off)).take 8).length = 8 := by simp; omega
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ _ q _ hl8 $$ [$Hpkg $Hb2] as Hb2
  ihave Hb2 := E2.2 $$ Hb2
  ihave Hb := (ownSlice_slice off b.len b q bs Hrng).2 $$ [$Hb1 $Hb2 $Hb3]
  iapply HΦ
  iexact Hb

/-- `LittleEndian.Uint32(b[off:])`: `u32At`. -/
private theorem wp_u32_at (b : GoSlice) (q : DFrac) (bs : List w8) (off : w64)
    (h0 : 0 ≤ sint.Z off) (hlen : bs.length = sint.nat b.len) (hb : 0 ≤ sint.Z b.len)
    (hoff : sint.nat off + 4 ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{q} bs }}
      (App (Val ((globalAddr encoding.binary.LittleEndian) @!!
        go.GoType.PointerType encoding.binary.littleEndian.ty @!! go!"Uint32"))
        (Val #(slice.slice b w8 off b.len)))
    {{ RET #(u32At bs (sint.nat off)); b ↦*{q} bs }} := by
  wp_start_folded as ⟨#Hpkg, Hb⟩
  have Hrng : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.len := by
    refine ⟨h0, ?_, le_refl _⟩; word
  icases (ownSlice_slice off b.len b q bs Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  have Hsub : subslice (sint.nat off) (sint.nat b.len) bs =
      (bs.drop (sint.nat off)).take 4 ++ bs.drop (sint.nat off + 4) := by
    have hd : (bs.drop (sint.nat off)).drop 4 = bs.drop (sint.nat off + 4) := by
      simp only [List.drop_drop, Nat.add_comm]
    rw [← hlen]
    simp only [subslice, List.take_length]
    rw [← hd, List.take_append_drop]
  have E2 : (slice.slice b w8 off b.len ↦*{q} subslice (sint.nat off) (sint.nat b.len) bs : IProp GF) ⊣⊢
      slice.slice b w8 off b.len ↦*{q} ((bs.drop (sint.nat off)).take 4 ++ bs.drop (sint.nat off + 4)) := by
    rw [Hsub]; exact .rfl
  ihave Hb2 := E2.1 $$ Hb2
  have hl4 : ((bs.drop (sint.nat off)).take 4).length = 4 := by simp; omega
  wp_apply encoding.binary.wp_LittleEndian_Uint32 _ _ q _ hl4 $$ [$Hpkg $Hb2] as Hb2
  ihave Hb2 := E2.2 $$ Hb2
  ihave Hb := (ownSlice_slice off b.len b q bs Hrng).2 $$ [$Hb1 $Hb2 $Hb3]
  iapply HΦ
  iexact Hb

theorem getDatagram.wp_proof :
    getDatagram.spec (GF := GF) (hG := hG) := by
  intro b q bs
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  try wp_auto
  done

end proof

end raft_kvnet
end EtcdGrove
end Perennial
