/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__Stop.lean`. Lean-first
(no Rocq counterpart). kvreconf's, ported.

`c.all()` with the crasher's token gives every incarnation's stop share (`repStop`,
`Cluster.all.specStop`); the range over the slice stops each.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__all
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__stop
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.LifeLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.Stop.wp_proof (wp_all : Cluster.all.specStop (GF := GF) (hG := hG))
    (wp_stop : Replica.stop.spec (GF := GF) (hG := hG)) :
    Cluster.Stop.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c
  wp_start as ⟨Hc, Hcr⟩
  wp_auto
  wp_apply wp_all γ vs dir c $$ [$Hc $Hcr] as %sl ⟨%rs, Hsl, Htk⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  try wp_auto
  ihave IH : iprop(∃ (j : w64) (rv : Loc),
      "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ rv ∗
      "Htk" ∷ ([∗list] r ∈ rs.drop (sint.nat j), ∃ id, repStop γ vs dir id r) ∗
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
    rw [kvreconf.life_drop_cons _ _ _ Hr0]
    icases Htk with ⟨⟨%id, Hr⟩, Htk⟩
    iunfold repStop at Hr
    icases Hr with ⟨Hr, -⟩
    wp_apply wp_stop γ vs dir id r0 $$ [$Hr] as -
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

end kvdurable
end EtcdGrove
end Perennial
