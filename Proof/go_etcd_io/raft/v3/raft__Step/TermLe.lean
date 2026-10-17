/- raft#47 (2026-10-16): the two term facts `Step` gives the code raft#47 adds checks for.

- `ownRaftGhost_lastTerm_le`: the log's last term is at most the node's (`LastTermLe`,
  `Spec/go_etcd_io/raft/v3/raft__appendEntry.lean`), from the ghost state's `TermsLe` (no term in a
  node's full log is above its own). `appendEntry` now panics otherwise; `stepLeader`'s `MsgProp`
  and `stepCandidate`'s `MsgVoteResp` (through `becomeLeader`) take it.
- `isMessage_snap_term_le`: a snapshot message's snapshot term is at most the message's term: the
  sender's log has the snapshot's last entry (`isMessage`'s `snap` case), and no term of a leader's
  full log is above its own (`lpfull`). `restore` now steps down on a snapshot of a later term;
  `handleSnapshot` takes the bound, which `Step` has from here once the node's term is the
  message's.

Proof structure; only files in this directory import it.
-/
module

public import Proof.go_etcd_io.raft.v3.StepGhostMode
public import Spec.go_etcd_io.raft.v3.raft__appendEntry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]
variable {md : Bool}

/-- No term in a node's log is above its own, in particular not the last one's. -/
theorem ownRaftGhost_lastTerm_le (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
      ⌜uint.Z (plogLast s.base s.log).term' ≤ uint.Z s.term⌝ := by
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %γa, %acks, %fp, %γc, %camps, %γl, %vlogs, %γw, %wins, H⟩
  iNamed H
  ipureintro
  obtain ⟨Hfp, Hwf, Htle⟩ := Hfull
  have Hl := plogTermAt_last _ _ Hwf
  have Hr := (plogTermAt_some_range _ _ _ _ Hl).1
  rw [← full_term_at _ _ _ _ Hfp Hr] at Hl
  exact (Htle _ _ Hl).1

private theorem isMessage_snap_inv' (γ : RaftNames) (m : Msg) :
    m.ty = .snap →
    ⊢ isMessage (GF := GF) γ m -∗
      isLeader γ m.src m.term ∗
      isSnapMeta γ m.logterm m.index ∗
      (∃ bL l fp, leadPrefix γ m.src m.term bL l ∗
         ⌜plogTermAt bL l m.index = some m.logterm⌝ ∗
         lpfull γ m.src m.term bL l fp ∗
         commitIn γ (fp ++ l) m.index m.term ∗
         isCommitted γ ((fp ++ l).take (uint.Z m.index).toNat)) ∗
      ⌜m.src ≠ W64 0⌝ := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

/-- A snapshot message's snapshot is of a term at most the message's. -/
theorem isMessage_snap_term_le (γ : RaftNames) (m : Msg) (Hty : m.ty = .snap) :
    ⊢ isMessage (GF := GF) γ m -∗ ⌜uint.Z m.logterm ≤ uint.Z m.term⌝ := by
  iintro #Hm
  icases isMessage_snap_inv' γ m Hty $$ Hm with
    ⟨-, -, ⟨%bL, %l', %fpL, -, %Hidx', #Hpf', -, -⟩, -⟩
  iunfold lpfull at Hpf'
  icases Hpf' with ⟨%F0, -, -, %Hp⟩
  obtain ⟨Hfull, -, -, Ht⟩ := Hp
  have HbL := (plogTermAt_some_range _ _ _ _ Hidx').1
  rw [← full_term_at bL fpL l' m.index Hfull HbL] at Hidx'
  ipureintro; exact Ht _ _ Hidx'

end ghost

section step
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- A `MsgSnap`'s snapshot is of a term at most the message's (`absSnap`'s `logterm` is the
snapshot's term). -/
theorem isMessage_absSnap_term_le (γ : RaftNames) (m : MessageM) (sv : SnapshotM)
    (scfg : CSLists) :
    ⊢ isMessage (GF := GF) γ (absSnap m sv scfg) -∗
      ⌜uint.Z sv.Metadata'.Term' ≤ uint.Z m.Term'⌝ :=
  isMessage_snap_term_le γ (absSnap m sv scfg) rfl

end step

end EtcdGrove
end Perennial
