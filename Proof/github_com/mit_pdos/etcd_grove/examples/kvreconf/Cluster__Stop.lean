/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__Stop.lean`. Lean-first
(no Rocq counterpart).

`c.all()` with the stopper's token gives every replica's stop token (`repStop`); the range over the
slice stops each.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__Stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__all
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__stop
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.LifeLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.Stop.wp_proof (wp_all : Cluster.all.spec (GF := GF) (hG := hG))
    (wp_stop : Replica.stop.spec (GF := GF) (hG := hG)) :
    Cluster.Stop.spec (GF := GF) (hG := hG) := by
  intro γr vs c
  wp_start as ⟨#Hc, Hst⟩
  wp_auto
  wp_apply wp_all γr vs c true $$ [$Hc Hst] as %sl ⟨%rs, Hsl, %Hne, -, Htk⟩
  · simp only [↓reduceIte]; iexact Hst
  try simp only [↓reduceIte]
  icases Htk with ⟨-, Htk⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  try wp_auto
  ihave IH : iprop(∃ (j : w64) (rv : Loc),
      "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ rv ∗
      "Htk" ∷ ([∗list] r ∈ rs.drop (sint.nat j), repStop γr vs r) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝) $$ [i r Htk]
  · iexists W64 0, _
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hjl : sint.nat j < rs.length := by rw [Hlen.1]; word
    obtain ⟨r0, Hr0⟩ : ∃ r0, rs[sint.nat j]? = some r0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index sl (sint.Z j) rs _ r0 Hj.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hr0
    try wp_auto
    rw [life_drop_cons _ _ _ Hr0]
    icases Htk with ⟨Hr, Htk⟩
    wp_apply wp_stop γr vs r0 $$ [$Hr]
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, r0
    have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [Hj1]
    iframe
    ipureintro; constructor <;> word
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
