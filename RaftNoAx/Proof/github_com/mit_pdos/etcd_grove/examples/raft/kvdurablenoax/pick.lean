-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/pick.lean` (etc/copy-part.py; rerun it, do not edit).
/-
kvreconf's proof (the same Go text), ported. Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/pick.lean`. Lean-first (no Rocq counterpart).
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.pick
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.below

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]

theorem pick.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    pick.spec (GF := GF) (hG := hG) := by
  intro sl ids dq Hne
  wp_start as Hsl
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply wp_below as %r %Hr'
  obtain ⟨Hr0, Hr⟩ := Hr'
  have Hpos : ids.length ≠ 0 := by simpa using Hne
  have Hn : sl.len ≠ W64 0 := by intro h; apply Hpos; word
  have Hrl := Hr Hn
  have Hi : r.toNat < ids.length := by word
  rw [ite_eq_left (show 0 ≤ sint.Z r ∧ sint.Z r < sint.Z sl.len by word)]
  wp_apply wp_load_slice_index sl (sint.Z r) ids dq (ids[r.toNat]'Hi) (by word) $$ [$Hsl] as Hsl
  · ipureintro
    rw [show (sint.Z r).toNat = r.toNat by word]
    simp [List.getElem?_eq_getElem Hi]
  try wp_auto
  iapply HΦ
  iframe Hsl
  ipureintro; exact List.getElem_mem Hi

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
