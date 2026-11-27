/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Invariant.lean (241f27e).
-/
/-
`proto` — the inductive invariant `PInv` of the protocol model (`Model.lean`), and the facts the
code uses (`Laws`). See `notes/redesign.md` for the argument.

Leader completeness is the "lacks" argument (Ongaro's thesis, §3.6.3, made inductive with
history): an acknowledgement `acked j Tc m` survives in `j`'s log unless a leader of a later term
`≤ term j` lacks it (`AckH`); a vote records the voter's log, which by `AckH` at the vote has the
acknowledged prefix unless a leader of a term in between lacks it (`VoteAck`); then by induction
on terms no leader after a committed prefix lacks it (`LC`), via the up-to-date check.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Model

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-- The genesis and the servers (stage 4: the genesis is a valid configuration over the servers). -/
def IGen (σ : PState) : Prop :=
  σ.g.term = 1 ∧ σ.g.kind = kConfig ∧ σ.srvs.Nodup ∧ cfgValid σ.srvs (σ.cv σ.g.data) ∧
  σ.llog 1 = [σ.g] ∧ σ.len0 1 = 1 ∧ σ.leader 0 = none ∧ σ.leader 1 = none ∧ σ.llog 0 = []

/-- The shape of each leader log: the election-time part has terms `< T`, the rest is the
leader's own entries (term `T`; stage 4: configurations allowed); it starts with the genesis; the
leader was elected by a quorum of the latest configuration of its election-time log; (stage 4)
the commitment's configuration `ccfg T` is admissible for the whole leader log (`cfgAdmAt`: the
latest, or its parent while the latest is the leader's own). A term with no leader (other than 1)
has the empty leader log. -/
def ILeaders (σ : PState) : Prop :=
  (∀ T ℓ, σ.leader T = some ℓ →
    ℓ ∈ σ.srvs ∧ 2 ≤ T ∧ 1 ≤ σ.len0 T ∧ σ.len0 T ≤ (σ.llog T).length ∧
    ent (σ.llog T) 1 = some σ.g ∧
    (∀ k, 1 ≤ k → k ≤ σ.len0 T → termAt (σ.llog T) k < T) ∧
    (∀ k e, σ.len0 T < k → ent (σ.llog T) k = some e → e.term = T) ∧
    σ.cand ℓ T = some (σ.len0 T, lastTerm ((σ.llog T).take (σ.len0 T))) ∧
    (∃ Q, isQuorumOf (cfgOf σ ((σ.llog T).take (σ.len0 T))) Q ∧
      ∀ j ∈ Q, ∃ L, σ.votes j T = some (ℓ, L, true)) ∧
    cfgAdmAt σ T (σ.llog T).length (σ.ccfg T)) ∧
  (∀ T, T ≠ 1 → σ.leader T = none → σ.llog T = [])

/-- (stage 4) Every configuration entry of a leader log (hence, by log matching, of every history
log) is valid over the servers. -/
def ICfgOk (σ : PState) : Prop :=
  ∀ T k e, ent (σ.llog T) k = some e → e.kind = kConfig → cfgValid σ.srvs (σ.cv e.data)

/-- Every log the protocol knows of: the servers', the leaders', the votes', the committed one
(stage 4: a server's log is empty or starts with the genesis; configurations are valid, `ICfgOk`). -/
def ILogs (σ : PState) : Prop :=
  (∀ i ∈ σ.srvs, LMok σ (σ.log i) ∧ (σ.log i = [] ∨ ent (σ.log i) 1 = some σ.g)) ∧
  (∀ T, LMok σ (σ.llog T)) ∧
  (∀ j T c L b, σ.votes j T = some (c, L, b) → LMok σ L) ∧
  LMok σ σ.C ∧
  ICfgOk σ

/-- (stage 4) **Configuration changes are adjacent and follow a commit** (`ICfgR`): every
configuration entry at `p > len0 T` of a leader log `llog T` (one the leader of `T` appended) is
adjacent to the latest configuration before it, and has its *R-commit*: a recorded commit of `T`
past `T`'s election part, covering that previous configuration's index, recorded when `llog T` had
`q < p` entries with an admissible configuration (`leaderAppendCfgPre`). -/
def ICfgR (σ : PState) : Prop :=
  ∀ T p e, σ.leader T ≠ none → σ.len0 T < p → ent (σ.llog T) p = some e → e.kind = kConfig →
    adjV (cfgOf σ ((σ.llog T).take (p - 1))) (σ.cv e.data) ∧
    ∃ k pc q, σ.commits T k pc ∧ σ.len0 T < k ∧ lastCfgIdx ((σ.llog T).take (p - 1)) ≤ k ∧
      k ≤ q ∧ q < p ∧ cfgAdmAt σ T q pc

/-- The leader of a server's current term is that server only with the leader log as its log. -/
def ICurrent (σ : PState) : Prop :=
  ∀ i ∈ σ.srvs, σ.leader (σ.term i) = some i → σ.log i = σ.llog (σ.term i)

/-- Votes: one per term (the map), cast in a term the voter had reached, for a candidate whose
recorded last entry was at least as up to date as the voter's log; a late vote had a leader. The
stable store's last vote is the vote of `vterm`. -/
def IVotes (σ : PState) : Prop :=
  (∀ j T c L b, σ.votes j T = some (c, L, b) →
    j ∈ σ.srvs ∧ 1 ≤ T ∧ T ≤ (σ.srv j).vterm ∧
    (∃ li lt, σ.cand c T = some (li, lt) ∧ upToDate li lt L) ∧
    (b = false → σ.leader T ≠ none)) ∧
  (∀ j ∈ σ.srvs, (σ.srv j).vterm ≤ σ.term j ∧
    (0 < (σ.srv j).vterm → ∃ L b, σ.votes j (σ.srv j).vterm = some ((σ.srv j).vcand, L, b))) ∧
  (∀ c T x, σ.cand c T = some x → c ∈ σ.srvs ∧ 1 ≤ T ∧ T ≤ σ.term c ∧ (T = 1 → x.1 = 0) ∧ x.2 < T)

/-- Acknowledgements survive (`AckH`): `j` keeps an acknowledged prefix unless a leader of a later
term `≤ term j` lacks it. -/
def IAcks (σ : PState) : Prop :=
  ∀ j T m, σ.acked j T m →
    j ∈ σ.srvs ∧ σ.leader T ≠ none ∧ m ≤ (σ.llog T).length ∧ T ≤ σ.term j ∧
    ∀ k, k ≤ m →
      agree (σ.log j) (σ.llog T) k ∨
      ∃ T'', T < T'' ∧ T'' ≤ σ.term j ∧ σ.leader T'' ≠ none ∧ lacks σ T'' k T

/-- Votes after acknowledgements (`VoteAck`): the log recorded with a vote of `T'` has every prefix
the voter acknowledged in an earlier term `T`, unless a leader of a term in between (or of `T'`
itself, for a late vote) lacks it. -/
def IVoteAck (σ : PState) : Prop :=
  ∀ j T' c L b T m k, σ.votes j T' = some (c, L, b) → σ.acked j T m → k ≤ m → T < T' →
    agree L (σ.llog T) k ∨
    ∃ T'', T < T'' ∧ (T'' < T' ∨ (T'' = T' ∧ b = false)) ∧ σ.leader T'' ≠ none ∧ lacks σ T'' k T

/-- Leader completeness: no leader of a later term lacks a prefix committed by an admissible
configuration (stage 4). -/
def ILC (σ : PState) : Prop :=
  ∀ T k p, committed σ T k p → cfgAdm σ T k p →
    ∀ T', T < T' → σ.leader T' ≠ none → ¬ lacks σ T' k T

/-- Recorded commits are committed by an admissible configuration and in `C`; `C` is a recorded
commit. -/
def ICommits (σ : PState) : Prop :=
  (∀ T k p, σ.commits T k p → committed σ T k p ∧ cfgAdm σ T k p ∧ agree σ.C (σ.llog T) k) ∧
  (σ.C = [] ∨ ∃ T p, σ.commits T σ.C.length p)

/-- Durable prefixes and commit indexes. -/
def IDur (σ : PState) : Prop :=
  ∀ i ∈ σ.srvs,
    ((σ.srv i).dur.1 = 0 ∨
      ((σ.srv i).dur.2 ≤ σ.term i ∧ (∃ k' p, (σ.srv i).dur.1 ≤ k' ∧ σ.commits (σ.srv i).dur.2 k' p) ∧
        agree (σ.log i) (σ.llog (σ.srv i).dur.2) (σ.srv i).dur.1)) ∧
    (σ.srv i).cidx ≤ (σ.srv i).dur.1

/-- Bounds: terms and log lengths below the receipts paid. -/
def IBounds (σ : PState) : Prop :=
  (∀ i ∈ σ.srvs, σ.term i ≤ σ.maxT ∧ (σ.log i).length ≤ σ.maxI) ∧
  (∀ T, (σ.llog T).length ≤ σ.maxI) ∧
  (∀ T, σ.maxT < T → σ.leader T = none) ∧
  1 ≤ σ.maxT ∧ 1 ≤ σ.maxI

/-- Auxiliary: a server's term bounds the terms of its log's entries (stage 4: it is at least 1
only once its log is not empty; a non-member starts at term 0 with the empty log). -/
def IAux (σ : PState) : Prop :=
  ∀ i ∈ σ.srvs, (σ.log i ≠ [] → 1 ≤ σ.term i) ∧
    ∀ k, 1 ≤ k → k ≤ (σ.log i).length → termAt (σ.log i) k ≤ σ.term i

/-- Publications (stage 2): a publication of `T` is by a leader of `T` and covered by a recorded
commit of `T`; every voter's durable prefix is covered by a publication of a term it has reached
(it learned its prefix from its own publication as leader, or from a leader's
`LeaderCommitIndex`, which that leader published). -/
def IPub (σ : PState) : Prop :=
  (∀ T k, σ.pubs T k → σ.leader T ≠ none ∧ ∃ k' p, k ≤ k' ∧ σ.commits T k' p) ∧
  (∀ i ∈ σ.srvs, (σ.srv i).dur.1 = 0 ∨
    ∃ T k, T ≤ σ.term i ∧ (σ.srv i).dur.1 ≤ k ∧ σ.pubs T k)

/-- The inductive invariant (stage 4: `ICfgR` last). -/
def PInv (σ : PState) : Prop :=
  IGen σ ∧ ILeaders σ ∧ ILogs σ ∧ ICurrent σ ∧ IVotes σ ∧ IAcks σ ∧ IVoteAck σ ∧ ILC σ ∧
  ICommits σ ∧ IDur σ ∧ IBounds σ ∧ IAux σ ∧ IPub σ ∧ ICfgR σ

end proto
end github_com.hashicorp.raft
end Perennial
