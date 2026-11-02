/-
kvreconf's proof (the same Go text), ported. Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__randomMember.lean`.
Lean-first (no Rocq counterpart).

A random replica's configuration (`conf`, read-only), its voters and learners appended into a fresh
slice; a random replica again (`random`) if that is empty or one time in four, else `replica` of a
random member (`known = false`: a member need not have been started), `random` if it is `nil`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__randomMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__random
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__replica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__conf
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners

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

theorem Cluster.randomMember.wp_proof (wp_random : Cluster.random.spec (GF := GF) (hG := hG))
    (wp_replica : Cluster.replica.spec (GF := GF) (hG := hG))
    (wp_conf : Replica.conf.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_GetVoters : raftpb.ConfState.GetVoters.spec (GF := GF) (hG := hG))
    (wp_GetLearners : raftpb.ConfState.GetLearners.spec (GF := GF) (hG := hG)) :
    Cluster.randomMember.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_random γ vs dir c $$ [$Hc] as %r0 ⟨%id0, #Hr0, -⟩
  wp_apply wp_conf γ vs dir id0 r0 $$ [$Hr0] as %csp %idx ⟨%cs, #Hcs⟩
  try wp_auto
  wp_apply wp_GetVoters csp DFrac.discard cs $$ [$Hpb $Hcs] as %sv ⟨#Hsv, -⟩
  ihave Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := w64) (GF := GF)
  wp_apply wp_slice_append slice.nil [] sv cs.Voters' DFrac.discard $$ [$Hnil $Hncap $Hsv] as %m1 ⟨Hm1, Hm1cap, -⟩
  wp_apply wp_GetLearners csp DFrac.discard cs $$ [$Hpb $Hcs] as %sl ⟨#Hsl, -⟩
  wp_apply wp_slice_append m1 _ sl cs.Learners' DFrac.discard $$ [$Hm1 $Hm1cap $Hsl] as %m2 ⟨Hm2, -, -⟩
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hm2
  -- a random replica, as the answer
  wp_if_destruct
  · try wp_auto
    wp_apply wp_random γ vs dir c $$ [$Hc] as %r1 ⟨%i1, #Hr1, -⟩
    try wp_auto
    iapply HΦ
    iexists i1; iexact Hr1
  · wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
    wp_if_destruct
    · try wp_auto
      wp_apply wp_below _ $$ [$Hpkg] as %k %Hk
      have Hk' : uint.Z k < uint.Z m2.len := Hk.2 Hif
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z m2.len := by
        obtain ⟨h1, h2⟩ := Hlen; constructor <;> word
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      have Hkn : sint.nat k < ([] ++ cs.Voters' ++ cs.Learners').length := by
        obtain ⟨h1, h2⟩ := Hlen; word
      obtain ⟨i0, Hi0⟩ : ∃ i0, ([] ++ cs.Voters' ++ cs.Learners')[sint.nat k]? = some i0 :=
        ⟨_, List.getElem?_eq_getElem Hkn⟩
      wp_apply wp_load_slice_index _ (sint.Z k) _ _ i0 Hbnd.1 $$ [Hm2] as Hm2
      · iframe Hm2; ipureintro; exact Hi0
      try wp_auto
      wp_apply wp_replica γ vs dir c i0 false $$ [$Hc] as %r1 Hr1
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      try wp_auto
      icases Hr1 with (%Hnull | Hr1)
      · obtain ⟨Hn, -⟩ := Hnull
        try wp_auto
        wp_apply wp_random γ vs dir c $$ [$Hc] as %r2 ⟨%i2, #Hr2, -⟩
        try wp_auto
        iapply HΦ
        iexists i2; iexact Hr2
      · wp_if_destruct
        · try wp_auto
          wp_apply wp_random γ vs dir c $$ [$Hc] as %r2 ⟨%i2, #Hr2, -⟩
          try wp_auto
          iapply HΦ
          iexists i2; iexact Hr2
        · try wp_auto
          iapply HΦ
          iexists i0; iexact Hr1
    · try wp_auto
      wp_apply wp_random γ vs dir c $$ [$Hc] as %r1 ⟨%i1, #Hr1, -⟩
      try wp_auto
      iapply HΦ
      iexists i1; iexact Hr1

end proof

end kvdurable
end EtcdGrove
end Perennial
