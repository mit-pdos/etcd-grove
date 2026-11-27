/-
Lean-first (no Rocq counterpart). #33 parity B1 (design §6.4, lead-approved receiver-side route):
**an acknowledgement raft certifies is at a term its node's durable state has reached.**

`isAcked γ id t i` (past index `0`) holds the fragment `(t, i) ↪[γa]□ ()` of node `id`'s
acknowledgement map (`reAcks !! id`); the node's durable ghost (`ownDurGhost γ id S`) holds a share of
that map's authority at its durable maps `E` (`durShares`), and `durPers` bounds every key of `E.acks`
by the durable term `S.term`. So the node that receives a `MsgTimeoutNow` (whose `isRaftMsg` carries
its destination's `isAcked` at the message's term) reads the message's term as at most its own durable
term, from its own ghost state. And `isLeader_wins`: a leader's winners map is named (`reWins`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.GhostState
public import Proof.go_etcd_io.raft.v3.ApiVocab

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section acked
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **An acknowledgement past index `0` is at most its node's durable term** (`isAcked`'s map
fragment against `ownDurGhost`'s share of the map's authority, `durPers`' bound on its keys). The
durable ghost is given back. -/
theorem isAcked_term_le (γ : RaftNames) (id t i : w64) (S : RaftState) :
    ⊢ ownDurGhost (GF := GF) γ id S -∗ isAcked γ id t i -∗
      ⌜uint.Z i ≠ 0 → uint.Z t ≤ uint.Z S.term⌝ ∗ ownDurGhost γ id S := by
  iintro Hd Ha
  unfold isAcked
  icases Ha with (%H0 | ⟨⟨%γa, %Hγa, #Hf⟩, -⟩)
  · iframe Hd
    ipureintro
    intro h; exact absurd H0 h
  · unfold ownDurGhost
    icases Hd with ⟨%E, Hsh, #Hp, Hsl, Hi1⟩
    unfold durShares
    icases Hsh with ⟨%γv, %γa', %γc, %γl, %γe, %Hn, Hv, Hac, Hc, Hl, He⟩
    have hγ : γa' = γa := by
      have h := Hn.2.1; rw [Hγa] at h; exact (Option.some.inj h).symm
    subst hγ
    icases ghost_map_lookup $$ Hac Hf with %Hlk
    have Hk : (E.acks !! (t, i)).isSome := by
      have Hlk' : E.acks !! (t, i) = some () := Hlk
      rw [Hlk']; rfl
    ihave #Hp2 := Hp
    iunfold durPers at Hp2
    icases Hp2 with ⟨%kd, %fp, %Hpu, -⟩
    isplitr
    · ipureintro
      intro _; exact Hpu.2.1 (t, i) Hk
    · iexists E
      iframe Hsl Hi1
      isplitl [Hv Hac Hc Hl He]
      · iexists γv, γa', γc, γl, γe
        iframe Hv Hac Hc Hl He
        ipureintro; exact Hn
      · iexact Hp

/-- **A leader of a term has its winners map** (`isLeader`'s `isWinCore`, `γ.reWins !! id = some _`):
with the cluster's allocation fact (`reWins` named for its ids), a forwarded `MsgTransferLeader`'s
destination, the leader `isRaftMsg` certifies, is one of the cluster's nodes. -/
theorem isLeader_wins (γ : RaftNames) (id t : w64) :
    ⊢ isLeader (GF := GF) γ id t -∗ ⌜(γ.reWins !! id).isSome⌝ := by
  iintro H
  unfold isLeader isWin isWinCore
  icases H with ⟨%q, %c, ⟨%γw, %F0, %k, %M, %Hw, -⟩, -⟩
  ipureintro
  rw [Hw.1]; rfl

/-- **A transfer message's destination is named**, from what a `Ready` says of each message it hands
out (`isRaftMsg`): a `MsgTimeoutNow`'s destination acknowledged an index past `0` (`isAcked`, its
acknowledgement map `reAcks`), a stamped `MsgTransferLeader`'s destination led the message's term
(`isLeader`, its winners map `reWins`). -/
theorem isRaftMsg_xdst (γ : RaftNames) (id : w64) (st : MsgSt) :
    ⊢ isRaftMsg (GF := GF) γ id st -∗
      ⌜(st.msg.Type' = MsgTimeoutNow → (γ.reAcks !! st.msg.To').isSome) ∧
        (st.msg.Type' = MsgTransferLeader → st.msg.Term' ≠ W64 0 →
          (γ.reWins !! st.msg.To').isSome)⌝ := by
  iintro #H
  unfold isRaftMsg
  icases H with ⟨-, -, -, -, #Hl, -, -, #Ht⟩
  isplit
  · iintro %hty
    ispecialize Ht $$ %hty
    icases Ht with ⟨%i, %hi, Ha⟩
    unfold isAcked
    icases Ha with (%H0 | ⟨⟨%γa, %Hγa, -⟩, -⟩)
    · exact absurd H0 hi
    · ipureintro; rw [Hγa]; rfl
  · iintro %hty %hz
    have hlz : st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0 := ⟨hty, hz⟩
    ispecialize Hl $$ %hlz
    iapply isLeader_wins $$ Hl

end acked

end EtcdGrove
end Perennial
