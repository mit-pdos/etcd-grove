/-
Lean-first (no Rocq counterpart). #33 parity B1 (design §6.4, lead-approved receiver-side route):
**an acknowledgement raft certifies is at a term its node's durable state has reached.**

`isAcked γ id t i` (past index `0`) holds the fragment `(t, i) ↪[γa]□ ()` of node `id`'s
acknowledgement map (`reAcks !! id`); the node's durable ghost (`ownDurGhost γ id S`) holds a share of
that map's authority at its durable maps `E` (`durShares`), and `durPers` bounds every key of `E.acks`
by the durable term `S.term`. So the node that receives a `MsgTimeoutNow` (whose `isRaftMsg` carries
its destination's `isAcked` at the message's term) reads the message's term as at most its own durable
term, from its own ghost state.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

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

end acked

end EtcdGrove
end Perennial
