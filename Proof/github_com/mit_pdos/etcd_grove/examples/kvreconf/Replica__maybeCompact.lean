/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__maybeCompact.lean`.
Lean-first (no Rocq counterpart).

`FirstIndex` is past the known compaction point `c`; `r.index` is read under the lock (the
applier's half: `len ap`); the target `x = first + below(hi - first + 1)` is in `[first, hi]`, so
at most the stored snapshot's index and `len ap`: its entry is frozen (`frozenTo_at`), the node
applied it (`nodeAppliedLb_mono`, the storage's `J.B`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__maybeCompact
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.below
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

theorem Replica.maybeCompact.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG)) :
    Replica.maybeCompact.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ ap csp m mA A cp sv0 snapIndex Hsi
  wp_start as ⟨#Hrr, Hown, Hsx, #Hcp, #Hfz, #Hal⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold repOwn at Hown
  iNamed Hown
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  ihave #HmsInv' := HmsInv
  iunfold memStorInvP at HmsInv'
  icases HmsInv' with ⟨#Hlock, -, -⟩
  try wp_auto
  wp_apply Storage.wp_FirstIndex wp_FirstIndex st ρ.ms ρ.γs cp $$ [$HstRec $Hraft $Hlock $Hcp]
    as %fi ⟨%Hfi, -⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HR]
  · inext; iexact HR
  try wp_auto
  ihave Hown : repOwn γr r ap (W64 ap.length) csp m mA A $$ [HmK HK HmA HA Hcs Hidx]
  · unfold repOwn; iexists mK, K, c; iframe; iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  -- the target is in `[first, hi]`, `hi` the least of `snapIndex` and `len ap`
  have Hlen' : uint.Z (W64 (ap.length : Int)) = (ap.length : Int) := by word
  wp_if_destruct
  all_goals
    try wp_auto
    wp_if_destruct
    · iapply HΦ; iframe
    wp_apply wp_below $$ [$Hpkg] as %rb %Hrb
    try wp_auto
    wp_apply Storage.wp_Compact wp_Compact st ρ.ms ρ.γs (kvrJ γr.cluster id) _ sv0 errCompacted
      (by rw [Hsi]; word) $$ [$HstRec $Hraft $HmsInv $Hsx $ErrCompacted]
      as %err ⟨-, -, Hsx⟩
    · isplitl []
      · ileft
        icases frozenTo_at ρ.γs cp ap (uint.nat (fi + rb)) (by word) (by word) $$ Hfz with ⟨%e, #He, -⟩
        iexists e; iexact He
      · unfold kvrJ; ileft
        iapply nodeAppliedLb_mono γr.cluster id ap.length _ (by word) $$ Hal
    try wp_auto
    ihave #Hc1 := isStats_field sts go!"Compactions" (by decide) $$ Hstats
    cases err
    · try wp_auto
      iapply HΦ; iframe
    · try wp_auto
      wp_apply wp_add sts _ $$ [$Hpkg $Hc1]
      try wp_auto
      iapply HΦ; iframe

end proof

end kvreconf
end EtcdGrove
end Perennial
