/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__random.lean`. Lean-first
(no Rocq counterpart).

`c.all()` (not empty), then the replica at `below(len)`, in bounds.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__all

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

theorem Cluster.random.wp_proof (wp_all : Cluster.all.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG)) :
    Cluster.random.spec (GF := GF) (hG := hG) := by
  intro γr vs c
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  wp_auto
  wp_apply wp_all γr vs c false $$ [$Hc] as %sl ⟨%rs, Hsl, %Hne, #Hreps, -⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply wp_below _ $$ [$Hpkg] as %k %Hk
  have Hpos : 0 < rs.length := List.length_pos_iff.mpr Hne
  have Hk' : uint.Z k < rs.length := by
    have := Hk.2 (by intro h; have := congrArg uint.Z h; simp at this; word)
    word
  have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
    obtain ⟨h1, h2⟩ := Hlen; constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  have Hkn : sint.nat k < rs.length := by obtain ⟨h1, h2⟩ := Hlen; word
  obtain ⟨r0, Hr0⟩ : ∃ r0, rs[sint.nat k]? = some r0 := ⟨_, List.getElem?_eq_getElem Hkn⟩
  wp_apply wp_load_slice_index _ (sint.Z k) _ _ r0 Hbnd.1 $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; exact Hr0
  try wp_auto
  iapply HΦ
  iapply BigSepL.bigSepL_lookup (Φ := fun _ r => iprop(∃ id, isRep (GF := GF) γr vs id r)) Hr0
    $$ Hreps

end proof

end kvreconf
end EtcdGrove
end Perennial
