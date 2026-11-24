/-
The proof of `readFrame` (`KvNet/Spec/.../kvnet/readFrame.lean`): `readFull` of the 8-byte
header into a local array, its little-endian value `l`, the bound, a fresh slice of `l` bytes and
`readFull` into it, the second read's predicate the caller's after the header's bytes.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFrame
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFull

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem readFrame.wp_proof (wp_readFull : readFull.spec (GF := GF) (hG := hG)) :
    readFrame.spec (GF := GF) (hG := hG) := by
  intro c cn s a P eof ed
  wp_start as ⟨#Hc, #Heof, #Hed, HP, #Hacc⟩
  wp_auto
  ihave #Hbin : (isPkgInit (PROP := IProp GF) pkg_id.encoding.binary) $$ []
  · iPkgInit
  ihave Hn := slice_array (GF := GF) n_ptr _ _ (by decide) $$ n
  rw [show (zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) from rfl,
    show W64 (8 : Int) = W64 8 from rfl] at *
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl]
  wp_apply wp_readFull c cn s a (slice.mk n_ptr (W64 8) (W64 8)) (List.replicate 8 (W8 0)) P eof ed
    $$ [Hn HP] as %ok1 ⟨%g1, %h1, HP, Hn, %Hr1⟩
  · iframe Hc Hn Heof Hed HP Hacc
  cases ok1
  · -- the header not read
    wp_auto
    iapply HΦ
    iexists g1
    iframe HP
    ileft; ipureintro; rfl
  obtain ⟨hl1, -, hg1⟩ := Hr1
  have hg1 := hg1 rfl
  subst hg1
  have hl8 : g1.length = 8 := by rw [hl1]; rfl
  wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl]
  ihave Hn : slice.mk n_ptr (W64 8) (W64 8) ↦* (g1 ++ []) $$ [Hn]
  · rw [List.append_nil]; iexact Hn
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ g1 (DFrac.own 1) [] hl8 $$ [$Hn] as Hn
  rcases Classical.em (uint.Z (W64 67108864) < uint.Z (leToU64 g1)) with hb | hb
  · -- a length past `maxFrame`
    rw [decide_eq_true hb]
    wp_auto
    iapply HΦ
    iexists g1
    iframe HP
    ileft; ipureintro; rfl
  rw [decide_eq_false hb]
  wp_auto
  have hLz : uint.Z (leToU64 g1) ≤ 67108864 := by
    have : uint.Z (W64 67108864) = 67108864 := rfl
    omega
  have hLs : sint.Z (leToU64 g1) = uint.Z (leToU64 g1) := by word
  wp_apply wp_slice_make2 (V := w8) (leToU64 g1) as %b ⟨Hb, Hbcap⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply wp_readFull c cn s a b (List.replicate (sint.nat (leToU64 g1)) (zero_val w8)) (fun got => P (g1 ++ got)) eof ed
    $$ [Hb HP] as %ok2 ⟨%g2, %h2, HP, Hb, %Hr2⟩
  · iframe Hc Hb Heof Hed
    rw [List.append_nil]
    iframe HP
    imodintro
    iintro %got %m HP
    imod Hacc $$ %(g1 ++ got) %m HP with ⟨%st, %d, HE, HD, Hcl⟩
    imodintro
    iexists st, d
    iframe HE HD
    iintro %r %d' %Hrd HE HD
    rw [← List.append_assoc]
    iapply Hcl $$ %r %d' %Hrd HE HD
  cases ok2
  · -- the body not read
    wp_auto
    iapply HΦ
    iexists (g1 ++ g2)
    iframe HP
    ileft; ipureintro; rfl
  obtain ⟨hl2, -, hg2⟩ := Hr2
  have hg2 := hg2 rfl
  subst hg2
  wp_auto
  iapply HΦ
  iexists (g1 ++ g2)
  iframe HP
  iright
  iexists g2
  iframe Hb
  ipureintro
  have hg2l : g2.length = (uint.Z (leToU64 g1)).toNat := by
    rw [hl2, List.length_replicate]; show (sint.Z (leToU64 g1)).toNat = _; rw [hLs]
  refine ⟨rfl, ?_, by omega⟩
  unfold putB
  have : W64 g2.length = (leToU64 g1) := by rw [hg2l]; word
  rw [this, leToU64_le g1 hl8]

end proof

end raft_kvnet
end EtcdGrove
end Perennial
