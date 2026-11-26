/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/memoryOf.lean`: a fresh
`MemoryStorage` (`NewMemoryStorage`), no snapshot (B1's disk has none), the disk's hard state
(`SetHardState`) and its entries (`Append`, from index 1).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.memoryOf
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem memoryOf.wp_proof (wp_New : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG)) :
    memoryOf.spec (GF := GF) (hG := hG) := by
  intro d w hix hlen
  wp_start as Hd
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold diskOwn at Hd
  icases Hd with ⟨%hsl, %esl, Hhs, #Hhsr, Hsnap, Hents, #Hes, Hcap⟩
  wp_auto
  wp_apply wp_New false $$ [$Hraft] as %ms %γs ⟨%Hsz, #Hlock, #Hl0, Hend, -, Hmeta, -⟩
  try wp_auto
  wp_apply wp_SetHardState ms γs _ hsl (HardStateM.mk w.term w.vote w.commit) $$ [$Hraft $Hmeta] as Hmeta
  · iunfold hsOpt; iright; iexact Hhsr
  try wp_auto
  ihave #HesZ : entsPtsZ γs.sz esl DFrac.discard w.log $$ []
  · rw [Hsz]; iapply entsPts_entsPtsZ; iexact Hes
  have hix' : ∀ (i : Nat) (e : EntryM), w.log[i]? = some e → uint.nat e.Index' = 1 + i := hix
  by_cases hl : w.log = []
  · wp_apply wp_Append ms γs 1 [] w.log esl DFrac.discard hix' hlen $$ [$Hraft $Hlock $HesZ] as ⟨-, -⟩
    · rw [if_pos hl]; iempintro
    try wp_auto
    iapply HΦ
    iunfold diskOwn
    iframe
    rw [hl, List.length_nil, Nat.add_zero]
    iframe Hhsr Hes Hlock Hend
    isplitl
    · iapply memLog_nil
    ipureintro; exact Hsz
  · wp_apply wp_Append ms γs 1 [] w.log esl DFrac.discard hix' hlen $$ [$Hraft $Hlock Hend $HesZ]
      as ⟨-, Hlog⟩
    · rw [if_neg hl]
      iframe Hend
      iapply memLog_nil
    try wp_auto
    ihave Hlog : iprop(memLog γs 1 (DFrac.own 1) w.log ∗ memEnd γs (1 + w.log.length)) $$ [Hlog]
    · iapply (show ((if w.log = [] then emp else
          iprop(memLog γs 1 (DFrac.own 1) w.log ∗ memEnd γs (1 + w.log.length))) : IProp GF) ⊢
          iprop(memLog γs 1 (DFrac.own 1) w.log ∗ memEnd γs (1 + w.log.length)) by rw [if_neg hl])
      iexact Hlog
    iapply HΦ
    iunfold diskOwn
    iframe
    icases Hlog with ⟨Hlog, Hend⟩
    iframe Hhsr Hes Hlock Hlog Hend
    ipureintro; exact Hsz

end proof

end AntHarness
end EtcdGrove
end Perennial
