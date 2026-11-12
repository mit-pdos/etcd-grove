/-
`EnsureConfState` on a snapshot's nested conf state (`csOptA`, D7, stage R4 of the raft v3.7
retarget): the conf state frozen read-only for good with its `AutoLeave` set. Used where raft
keeps a snapshot's conf state pointer while the snapshot stays its owner's
(`MemoryStorage.InitialState`, `raft.restore`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `EnsureConfState` on a snapshot's non-`nil` nested conf state held at `1` (`csOptA`): `pc`
itself, the conf state with its `AutoLeave` set, frozen read-only for good (an owned one after
`EnsureConfState` wrote its `AutoLeave`, a frozen one as it was). The snapshot then holds it as
`csOptA`'s third case. -/
theorem wp_EnsureConfState_freeze
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (pc : Loc) (c : ConfStateM) (Hpc : pc ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csOptA pc (DFrac.own 1) c }}
      (App (Val #(functions raftpb.EnsureConfState [])) (Val #pc))
    {{ RET #pc; csPts pc DFrac.discard c true }} := by
  iintro %Φ ⟨#Hinit, Hc⟩ HΦ
  iunfold csOptA at Hc
  icases Hc with (⟨%Hp, -⟩ | Hc | #Hc)
  · exact absurd Hp Hpc
  · iapply wp_fupd
    wp_apply wp_EnsureConfState.1 pc (DFrac.own 1) c false $$ [Hc] as Hcs
    · iframe; ipureintro; intro h; exact absurd rfl h
    imod csPts_persist _ _ _ _ $$ Hcs with #Hcs
    imodintro
    iapply HΦ; iexact Hcs
  · wp_apply wp_EnsureConfState.1 pc DFrac.discard c true $$ [] as #Hcs
    · iframe Hc; ipureintro; intro _; rfl
    iapply HΦ; iexact Hcs

/-- (D22 S-b, D22j, 2026-10-19) `EnsureConfState` on a snapshot's nested conf state held at `1`,
`nil` or not (`restore`'s `!found` exit: a `nil` `ConfState` names no node): a conf state with the
same record (`nil`'s is the zero one) and its `AutoLeave` set, frozen read-only for good (`pc`
itself when non-`nil`, `wp_EnsureConfState_freeze`; a fresh one for `nil`), and the snapshot's
nested conf state back as `csOptA` (for non-`nil`, its third case). -/
theorem wp_EnsureConfState_opt
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (pc : Loc) (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csOptA pc (DFrac.own 1) c }}
      (App (Val #(functions raftpb.EnsureConfState [])) (Val #pc))
    {{ (q : Loc), RET #q; csPts q DFrac.discard c true ∗ csOptA pc (DFrac.own 1) c ∗
        ⌜pc ≠ null → q = pc⌝ }} := by
  iintro %Φ ⟨#Hinit, Hc⟩ HΦ
  icases csOptA_nn _ _ _ $$ Hc with ⟨Hc, %Hpc⟩
  rcases Hpc with ⟨Hp, Hc0⟩ | Hpc
  · subst Hp Hc0
    iapply wp_fupd
    wp_apply wp_EnsureConfState.2 as %q Hcs
    imod csPts_persist _ _ _ _ $$ Hcs with #Hcs
    imodintro
    iapply HΦ
    iframe Hcs Hc
    ipureintro; intro h; exact absurd rfl h
  · wp_apply wp_EnsureConfState_freeze wp_EnsureConfState pc c Hpc $$ [Hc] as #Hcs
    · iexact Hc
    iapply HΦ
    iframe Hcs
    isplitr
    · iunfold csOptA; iright; iright; iexact Hcs
    ipureintro; intro _; rfl

end lemmas

end EtcdGrove
end Perennial
