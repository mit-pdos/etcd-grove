/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__snapshot.lean`.
Lean-first (no Rocq counterpart; kvreconf-snapshot-thread, 2026-10-30).

The request's snapshot part gives `CreateSnapshot` all it takes (`snapReqOk`); either answer raises
what is known of the stored snapshot to the request's index (`memSnapLb`), and the `panic` on any
other error is unreachable. The compaction part is `maybeCompact`'s: `FirstIndex` is past the
request's compaction point `c`; the target `x = first + below(hi - first + 1)` is in `[first, hi]`,
`hi` the least of the request's bound and the known stored index, so its entry is frozen
(`frozenTo_at`), the node applied it (`nodeAppliedLb_mono`, the storage's `J.B`) and the stored
snapshot reaches it (`memSnapLb_mono`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

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

theorem Replica.snapshot.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG)) :
    Replica.snapshot.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ q known
  wp_start as ⟨#Hrr, Hreq, #Hkn⟩
  iunfold snapReqOk at Hreq
  icases Hreq with ⟨Hsnap, Hcomp⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  ihave #HmsInv' := HmsInv
  iunfold memStorInvP at HmsInv'
  icases HmsInv' with ⟨#Hlock, -, -⟩
  try wp_auto
  iunfold errorsNewVar at ErrSnapOODNew
  icases ErrSnapOODNew with ⟨%xe, #Heood, -⟩
  ihave #Hc1 := isStats_field sts go!"SnapshotsTaken" (by decide) $$ Hstats
  ihave #Hc2 := isStats_field sts go!"SnapshotsTakenJoint" (by decide) $$ Hstats
  ihave #Hc3 := isStats_field sts go!"Compactions" (by decide) $$ Hstats
  -- the snapshot part: afterwards, `known` is a lower bound of the stored index
  wp_join iprop(∃ k1 : w64, known_ptr ↦ k1 ∗ req_ptr ↦ q ∗ r_ptr ↦ r ∗
      memSnapLb ρ.γs (uint.nat k1))
    with [known req r Hsnap] as ⟨%k1, known, req, r, #Hkn1⟩
  · iexists known; iframe known req r; iexact Hkn
  · icases Hsnap with (%Hnil | ⟨%e, %cc, %bs, #He, #HSV, #HDL, #Hcs, Hdata⟩)
    · exfalso; exact Hif Hnil
    try wp_auto
    wp_apply Storage.wp_CreateSnapshot wp_CreateSnapshot st ρ.ms ρ.γs (kvrJ γr.cluster id) q.index' e
        q.cs' DFrac.discard cc q.data' bs _
      $$ [$HstRec $Hraft $HmsInv $He $HSV $HDL $HsnLb $Hcs $Hdata $Heood] as %snap %err ⟨-, #Hlb, Hres⟩
    icases Hres with (⟨%Herr, -⟩ | ⟨⟨%Hsn, %Herr⟩, -⟩)
    · subst Herr
      try wp_auto
      wp_apply wp_add sts _ $$ [$Hpkg $Hc1]
      try wp_auto
      ihave #HcsO : csOpt q.cs' DFrac.discard cc $$ []
      · unfold csOpt; iright; iexact Hcs
      wp_apply wp_GetVotersOutgoing q.cs' DFrac.discard cc $$ [$Hpb $HcsO] as %vo ⟨-, -⟩
      try wp_auto
      try wp_if_destruct
      all_goals
        try wp_apply wp_add sts _ $$ [$Hpkg $Hc2]
        try wp_auto
        wp_if_destruct
        · wp_join_done; iexists q.index'; iframe; iexact Hlb
        · wp_join_done; iexists known; iframe; iexact Hkn
    · subst Herr
      try wp_auto
      wp_if_destruct
      · wp_join_done; iexists q.index'; iframe; iexact Hlb
      · wp_join_done; iexists known; iframe; iexact Hkn
  -- the compaction part
  wp_if_destruct
  · iapply HΦ; iexact Hkn1
  icases Hcomp with (%H0 | ⟨%cp, %D, #Hcp, #Hfz, %HD, #Hal⟩)
  · exfalso; simp_all
  wp_apply Storage.wp_FirstIndex wp_FirstIndex st ρ.ms ρ.γs cp $$ [$HstRec $Hraft $Hlock $Hcp]
    as %fi ⟨%Hfi, -⟩
  try wp_auto
  wp_if_destruct
  all_goals
    try wp_auto
    wp_if_destruct
    rotate_left
    · iapply HΦ; iexact Hkn1
    wp_apply wp_below $$ [$Hpkg] as %rb %Hrb
    try wp_auto
    wp_apply Storage.wp_Compact wp_Compact st ρ.ms ρ.γs (kvrJ γr.cluster id) _ errCompacted
      $$ [$HstRec $Hraft $HmsInv $ErrCompacted] as %err ⟨-, -⟩
    · isplitl []
      · ileft
        icases frozenTo_at ρ.γs cp D (uint.nat (fi + rb)) (by word) (by word) $$ Hfz with ⟨%e, #He, -⟩
        iexists e; iexact He
      isplitl []
      · unfold kvrJ; ileft
        iapply nodeAppliedLb_mono γr.cluster id (uint.nat q.compact') _ (by word) $$ Hal
      iapply (memSnapLb_mono ρ.γs (uint.nat k1) (uint.nat (fi + rb)) (by word))
      iexact Hkn1
    try wp_auto
    cases err
    · try wp_auto
      iapply HΦ; iexact Hkn1
    · try wp_auto
      wp_apply wp_add sts _ $$ [$Hpkg $Hc3]
      try wp_auto
      iapply HΦ; iexact Hkn1

end proof

end kvreconf
end EtcdGrove
end Perennial
