/-
The proof of `KvNet/Spec/.../kvnet/fragments.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.fragments
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putFragment
public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- The chunk `fragments` slices out is `chunkAt`'s. -/
private theorem chunk_sub (bs : List w8) (i e : Nat) (he : e = min ((i + 1) * chunkSizeN) bs.length) :
    subslice (i * chunkSizeN) e bs = chunkAt bs i := by
  subst he
  unfold subslice chunkAt chunkSizeN
  rw [List.drop_take]
  by_cases h : (i + 1) * 479 ≤ bs.length
  · rw [Nat.min_eq_left h, show (i + 1) * 479 - i * 479 = 479 by omega]
  · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by simp; omega),
      List.take_of_length_le (by simp; omega)]

/-- The `k`-th fragment of a body cut into `n` chunks. -/
private theorem fragsOf_get (src dst boot seq : w64) (bs : List w8) (k : Nat)
    (hn : ¬(nChunks bs = 0 ∨ maxFragmentsN < nChunks bs)) (hk : k < nChunks bs) :
    (fragsOf src dst boot seq bs)[k]? = some (fragBytes src dst boot seq (W32 (k : Int))
      (W32 ((nChunks bs : Nat) : Int)) (chunkAt bs k)) := by
  unfold fragsOf
  rw [if_neg hn, List.getElem?_map, List.getElem?_range hk]
  rfl

private theorem fragsOf_len (src dst boot seq : w64) (bs : List w8)
    (hn : ¬(nChunks bs = 0 ∨ maxFragmentsN < nChunks bs)) :
    (fragsOf src dst boot seq bs).length = nChunks bs := by
  unfold fragsOf
  rw [if_neg hn, List.length_map, List.length_range]

theorem fragments.wp_proof
    (wp_putFragment : putFragment.spec (GF := GF) (hG := hG)) :
    fragments.spec (GF := GF) (hG := hG) := by
  intro src dst boot seq body q bs Hbl
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  ihave %Hmax := bytes.ownSlice_bytes_len_le _ _ _ $$ Hb
  unfold maxAddr at Hmax
  have HL : bs.length ≤ 2 ^ 47 := by have := Hlen.1; word
  have HLz : uint.Z body.len = bs.length := by have := Hlen.1; word
  try wp_auto
  done

end proof

end raft_kvnet
end EtcdGrove
end Perennial
