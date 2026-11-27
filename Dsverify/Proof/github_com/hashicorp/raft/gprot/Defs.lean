/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Defs.lean (241f27e).
-/
/-
`gprot` (redesign R1) — the ghost layer of the protocol model `proto`.

`Inv γ` is an Iris invariant holding the current protocol state `σ : proto.PState` with
`PInv σ`, the authorities of the monotone history (ghost maps with persistent elements, the
committed log as a `mono_list`), and, per server, one half of each piece of per-server state:
- `srvOwn γ i s`: the server's own state `s : SState` — the other half is held by the server's
  main goroutine (the only goroutine that changes it);
- `termCouple γ i t`, `logCouple γ i L`, `cidxCouple γ i c`: the other halves of the mirrors of the
  `currentTerm` atomic, the log store's contents and the `commitIndex` atomic — held by the
  invariants that own those physical cells (allocated when the server is built), so a reader of
  the cell learns the protocol state at the instant it reads.
Time receipts pay for the bounds (`maxT + maxI`).

Clients use only the names below and the laws (`Laws.lean`); every definition is sealed.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Kinds
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Read
public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.GooseLang.Receipts
public import Perennial.GooseLang.Lifting
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Ghost

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

/-! ## Countability of the model's data (ghost state stores encodings) -/

instance entry_countable : Pos.Countable Entry :=
  Pos.Countable.ofInjective
    (fun e => Pos.Countable.encode (e.term, e.kind, e.data))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)

instance sstate_countable : Pos.Countable SState :=
  Pos.Countable.ofInjective
    (fun s => Pos.Countable.encode (s.term, s.log, s.vterm, s.vcand, s.dur, s.cidx))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; rfl)

instance snap_countable : Pos.Countable Snap :=
  Pos.Countable.ofInjective
    (fun s => Pos.Countable.encode (s.idx, s.terms, s.durs, s.llens))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1; subst h2; subst h3; subst h4; rfl)

/-! ## Ghost names -/

/-- The ghost names of the protocol, and the pure parameters of the run: the servers (stage 4: the
six, members of a configuration or not), the decoding of a configuration's voters, and the genesis
entry. -/
structure GNames where
  srvs : List SID
  /-- (stage 4) the voters of an encoded configuration (`proto.PState.cv`). -/
  cv : List w8 → List SID
  g : Entry
  leader : GName
  llog : GName
  len0 : GName
  cand : GName
  votes : GName
  acks : GName
  commits : GName
  C : GName
  srvSet : GName
  term : SID → GName
  dur : SID → GName
  srv : SID → GName
  slog : SID → GName
  cidx : SID → GName
  /-- clients' operation tokens: `ghost_map (List w8) Unit`, authority held by the client (hr3),
  the tokens of the commands appended to a leader log held by the invariant. -/
  ops : GName
  /-- (stage 2) the publications `(T, k)`: a ghost map with persistent elements (`pubIs`). -/
  pubs : GName
  /-- (stage 2) per candidate and term, the bound on its publications: `ghost_map (SID × Nat) Nat`,
  authority in the invariant, the element of `(c, T)` held by `c`'s main goroutine from its
  election of `T` (`pubOwn`). -/
  pubMax : GName
  /-- (stage 2) the snapshots taken so far: a `mono_list Snap` (authority in the invariant;
  `histLb`). -/
  hist : GName
  /-- (stage 4) the configuration each candidate's commitment counts, per `(c, T)`: `ghost_map
  (SID × Nat) Nat`, authority in the invariant, the two halves of the element of `(c, T)` held by
  `c` from its election of `T` (`ccfgOwn`; one in the leader's commitment lock, one in its main
  goroutine); when `c` leads `T` the value is `σ.ccfg T`. -/
  ccfg : GName

def gprotN : Namespace := nroot.@"gprot"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-! ## The invariant -/

/-- The history components as finitely supported partial functions (mirrored by ghost maps). -/
def llogF (σ : PState) (p : Nat × Nat) : Option Entry := ent (σ.llog p.1) p.2
def len0F (σ : PState) (T : Nat) : Option Nat :=
  if σ.leader T ≠ none ∨ T = 1 then some (σ.len0 T) else none
def candF (σ : PState) (p : SID × Nat) : Option (Nat × Nat) := σ.cand p.1 p.2
def votesF (σ : PState) (p : SID × Nat) : Option (SID × RLog × Bool) := σ.votes p.1 p.2
open Classical in
def acksF (σ : PState) (p : SID × Nat × Nat) : Option Unit :=
  if σ.acked p.1 p.2.1 p.2.2 then some () else none
open Classical in
def commitsF (σ : PState) (p : Nat × Nat × Nat) : Option Unit :=
  if σ.commits p.1 p.2.1 p.2.2 then some () else none
def srvsF (σ : PState) (i : SID) : Option Unit := if i ∈ σ.srvs then some () else none
open Classical in
def pubsF (σ : PState) (p : Nat × Nat) : Option Unit :=
  if σ.pubs p.1 p.2 then some () else none

/-- (stage 2) The bound on each candidate's publications in each term, owned by the candidate: a
pair `(c, T)` has an entry iff `c` started an election of `T`; every publication of `T` is at most
the bound of `T`'s leader. -/
def PubMaxG (γ : GNames) (σ : PState) : IProp GF :=
  iprop(∃ PM : GMap (SID × Nat) Nat, ghostMapAuth γ.pubMax 1 PM ∗
    ⌜(∀ c T, (PM.lookup (c, T)).isSome ↔ σ.cand c T ≠ none) ∧
      ∀ T k, σ.pubs T k → ∃ ℓ m, σ.leader T = some ℓ ∧ PM.lookup (ℓ, T) = some m ∧ k ≤ m⌝)

/-- (stage 2) The snapshots: a list of snapshots numbered `0, 1, ..` in order, each known to the
current state (`SnapOK`), each no later than the next. -/
def SnapG (γ : GNames) (σ : PState) : IProp GF :=
  iprop(∃ L : List Snap, monoListAuthOwn γ.hist 1 L ∗
    ⌜(∀ n s, L[n]? = some s → s.idx = n ∧ SnapOK σ s) ∧ L.Pairwise snapLe⌝)

/-- (stage 4) The commitments' configurations: a pair `(c, T)` has an entry iff `c` started an
election of `T`; if `c` leads `T`, its entry is `ccfg T`. -/
def CcfgG (γ : GNames) (σ : PState) : IProp GF :=
  iprop(∃ CM : GMap (SID × Nat) Nat, ghostMapAuth γ.ccfg 1 CM ∗
    ⌜(∀ c T, (CM.lookup (c, T)).isSome ↔ σ.cand c T ≠ none) ∧
      ∀ c T p, CM.lookup (c, T) = some p → σ.leader T = some c → σ.ccfg T = p⌝)

/-- The clients' operation tokens held by the invariant (`O`: data of each appended command, with
its operation's call-snapshot length), and how they relate to `σ`: every command of a leader log
has its token in `O`; commands with the same data sit at one index; and the command of a token
`d ↦ n` is committed, if ever, at an index above `n`. -/
def OpsOK (σ : PState) (O : GMap (List w8) Nat) : Prop :=
  (∀ T k e, ent (σ.llog T) k = some e → e.kind = kCommand → O.lookup e.data ≠ none) ∧
  (∀ T1 k1 e1 T2 k2 e2, ent (σ.llog T1) k1 = some e1 → ent (σ.llog T2) k2 = some e2 →
    e1.kind = kCommand → e2.kind = kCommand → e1.data = e2.data → k1 = k2) ∧
  (∀ d n y, O.lookup d = some n →
    (∃ T e, ent (σ.llog T) y = some e ∧ e.kind = kCommand ∧ e.data = d) →
    n < y ∨ ∃ e', ent σ.C y = some e' ∧ ¬ (e'.kind = kCommand ∧ e'.data = d))

/-- The operation tokens in the invariant. -/
def OpsG (γ : GNames) (σ : PState) : IProp GF :=
  iprop(∃ O : GMap (List w8) Nat, ⌜OpsOK σ O⌝ ∗ [∗map] d ↦ n ∈ O, d ↪[γ.ops] n)

/-- The history's ghost state at `σ`. -/
def HistG (γ : GNames) (σ : PState) : IProp GF := iprop(
  GMapOf γ.leader σ.leader ∗ GMapOf γ.llog (llogF σ) ∗ GMapOf γ.len0 (len0F σ) ∗
  GMapOf γ.cand (candF σ) ∗ GMapOf γ.votes (votesF σ) ∗ GMapOf γ.acks (acksF σ) ∗
  GMapOf γ.commits (commitsF σ) ∗ GMapOf γ.srvSet (srvsF σ) ∗ OpsG γ σ ∗
  monoListAuthOwn γ.C 1 σ.C ∗ GMapOf γ.pubs (pubsF σ) ∗ PubMaxG γ σ ∗ SnapG γ σ)

/-- The invariant's half of server `i`'s state `s`. -/
def srvG (γ : GNames) (i : SID) (s : SState) : IProp GF := iprop(
  monoNatAuthOwn (γ.term i) (1 : Qp).half s.term ∗
  monoNatAuthOwn (γ.dur i) (1 : Qp).half s.dur.1 ∗
  ghostVar (γ.srv i) (1 : Qp).half s ∗
  ghostVar (γ.slog i) (1 : Qp).half s.log ∗
  ghostVar (γ.cidx i) (1 : Qp).half s.cidx)

/-- The pure part: `PInv`, the fixed parameters (stage 4: the servers, the configuration
decoding, the genesis), the kinds. -/
def GInv (γ : GNames) (σ : PState) : Prop :=
  PInv σ ∧ σ.srvs = γ.srvs ∧ σ.g = γ.g ∧ σ.cv = γ.cv ∧ IKinds σ ∧ (∀ j ∈ γ.srvs, j ≠ [])

/-- The invariant at state `σ`. -/
def InvBody (γ : GNames) (σ : PState) : IProp GF := iprop(
  ⌜GInv γ σ⌝ ∗ HistG γ σ ∗ ([∗list] i ∈ γ.srvs, srvG γ i (σ.srv i)) ∗
  receipt (σ.maxT + σ.maxI) ∗ CcfgG γ σ)

/-- The body: some state `σ` with `PInv σ`, the history's ghost maps mirroring it, the
invariant's half of each server's pieces, receipts for the bounds, and (stage 4) the authority of
the commitments' configurations. -/
def InvInner (γ : GNames) : IProp GF := iprop(∃ σ : PState, InvBody γ σ)

def InvDef (γ : GNames) : IProp GF := inv gprotN (InvInner γ)

/-- The protocol invariant. -/
@[irreducible] def Inv (γ : GNames) : IProp GF := InvDef γ
theorem Inv_unseal : @Inv = @InvDef := by funext; with_unfolding_all rfl

/-! ## Per-server exclusive halves -/

/-- Server `i`'s own protocol state (held by its main goroutine); carries the witness that `i`
is one of the servers (so the invariant's per-server half can be found). -/
@[irreducible] def srvOwn (γ : GNames) (i : SID) (s : SState) : IProp GF :=
  iprop(ghostVar (γ.srv i) (1 : Qp).half s ∗ i ↪[γ.srvSet]□ ())

/-- The `currentTerm` atomic's half (held by the cell's invariant). -/
@[irreducible] def termCouple (γ : GNames) (i : SID) (t : Nat) : IProp GF :=
  monoNatAuthOwn (γ.term i) (1 : Qp).half t

/-- The log store's half (held by the store's coupling invariant); carries the server witness. -/
@[irreducible] def logCouple (γ : GNames) (i : SID) (L : RLog) : IProp GF :=
  iprop(ghostVar (γ.slog i) (1 : Qp).half L ∗ i ↪[γ.srvSet]□ ())

/-- A fraction `q` of the view of server `i`'s durable-prefix length `d` (the main goroutine
holds one half, the invariant the other; exclusive per fraction, not persistent). -/
@[irreducible] def durView (γ : GNames) (i : SID) (q : Qp) (d : Nat) : IProp GF :=
  monoNatAuthOwn (γ.dur i) q d

/-- The `commitIndex` atomic's half (held by the cell's invariant). -/
@[irreducible] def cidxCouple (γ : GNames) (i : SID) (c : Nat) : IProp GF :=
  ghostVar (γ.cidx i) (1 : Qp).half c

/-! ## Persistent facts about the history -/

/-- `i` is one of the servers (stage 4; was `isVoter`, one of the fixed voters). -/
@[irreducible] def isSrv (γ : GNames) (i : SID) : IProp GF := i ↪[γ.srvSet]□ ()

/-- `ℓ` is the leader of term `T`. -/
@[irreducible] def leaderIs (γ : GNames) (T : Nat) (ℓ : SID) : IProp GF := T ↪[γ.leader]□ ℓ

/-- The leader log of `T` has `e` at index `k ≥ 1` (forever: it only grows). -/
@[irreducible] def llogIdx (γ : GNames) (T k : Nat) (e : Entry) : IProp GF :=
  iprop(⌜1 ≤ k⌝ ∗ (T, k) ↪[γ.llog]□ e)

/-- The leader of `T` had `n` entries at its election. -/
@[irreducible] def len0Is (γ : GNames) (T n : Nat) : IProp GF := T ↪[γ.len0]□ n

/-- Candidate `c`'s election of `T` started with last entry `(li, lt)`: a valid `RequestVote`. -/
@[irreducible] def candIs (γ : GNames) (c : SID) (T li lt : Nat) : IProp GF :=
  (c, T) ↪[γ.cand]□ (li, lt)

/-- `j` granted its vote of term `T` to `c`. -/
@[irreducible] def voteIs (γ : GNames) (j : SID) (T : Nat) (c : SID) : IProp GF :=
  iprop(∃ (L : RLog) (b : Bool), (j, T) ↪[γ.votes]□ (c, L, b))

/-- `j`, in term `T`, acknowledged `llog T [1..m]`. -/
@[irreducible] def ackIs (γ : GNames) (j : SID) (T m : Nat) : IProp GF :=
  (j, T, m) ↪[γ.acks]□ ()

/-- The leader of `T` recorded the commit of `llog T [1..k]` (stage 4: by a quorum of the
configuration entry at index `p` of `llog T`). -/
@[irreducible] def commitIs (γ : GNames) (T k p : Nat) : IProp GF := (T, k, p) ↪[γ.commits]□ ()

/-- (stage 4) **The configuration the commitment of `c`'s term `T` counts** (half of it; exclusive
per half): `c`'s main goroutine holds one half from its election of `T` (`electTerm_upd`), the
leader's commitment lock the other; when `c` leads `T`, `p = ccfg T` (the index in `llog T` of the
configuration the commitment counts). Both halves change it (`installCfg_upd`,
`commitment.setConfiguration`); one half gives a commit's configuration (`commit_upd`). -/
@[irreducible] def ccfgOwn (γ : GNames) (c : SID) (T p : Nat) : IProp GF :=
  (c, T) ↪[γ.ccfg]{#(1 : Qp).half} p

/-- (stage 4) The leader log of `T` extends `L` (each entry of `L` an `llogIdx` fact; persistent):
what a leader knows of its own log (`llogPre_leader`), so the configurations of its prefixes
(`cfgOfC γ.cv (L.take m)`) can be named in persistent facts (the read bound). -/
@[irreducible] def llogPre (γ : GNames) (T : Nat) (L : RLog) : IProp GF :=
  [∗list] k ↦ e ∈ L, llogIdx γ T (k + 1) e

/-- The committed log has `e` at index `k ≥ 1`. -/
@[irreducible] def CIdx (γ : GNames) (k : Nat) (e : Entry) : IProp GF :=
  iprop(⌜1 ≤ k⌝ ∗ monoListIdxOwn γ.C (k - 1) e)

/-- (stage 4, review T1-1) **Index `k` of the log `L` is committed by a commit of a term `≤ T`**
(persistent): `k = 0`, or a recorded commit `(T', k', p')` with `T' ≤ T` and `k ≤ k'` whose leader
log has `L`'s entry at `k`. What `mainOwnAt` keeps of the committed configuration's index
`configurations.committedIndex` (with `T` the server's term and `L` its log): with leader
completeness (`ILC`) the leader log of `T` extends `L [1..k]` (`cmtIdx_llog`: an `AppendEntries` of
term `T` truncates only above `k`), and `L`'s entry at `k` is in the committed log (`cmtIdx_CIdx`). -/
@[irreducible] def cmtIdx (γ : GNames) (T : Nat) (L : RLog) (k : Nat) : IProp GF :=
  iprop(⌜k = 0⌝ ∨ ∃ (T' k' p' : Nat) (e : Entry), ⌜T' ≤ T ∧ k ≤ k' ∧ ent L k = some e⌝ ∗
    commitIs γ T' k' p' ∗ llogIdx γ T' k e)

/-- The committed log extends `L`. -/
@[irreducible] def CLb (γ : GNames) (L : RLog) : IProp GF := monoListLbOwn γ.C L

/-- A client's authority over the data it has used for commands, each with the length of the
snapshot of the committed log its operation took (extension E1, see `Ops.lean`). -/
@[irreducible] def opsAuth (γ : GNames) (M : GMap (List w8) Nat) : IProp GF := ghostMapAuth γ.ops 1 M

/-- The token of command data `d` whose operation's call snapshot had length `n` (exclusive). -/
@[irreducible] def opTok (γ : GNames) (d : List w8) (n : Nat) : IProp GF :=
  iprop(d ↪[γ.ops] n ∗ ∃ L : RLog, CLb γ L ∗ ⌜L.length = n⌝)

/-- Server `i`'s term is at least `t`. -/
@[irreducible] def termLb (γ : GNames) (i : SID) (t : Nat) : IProp GF :=
  monoNatLbOwn (γ.term i) t

/-- Server `i`'s durable prefix is at least `k` long. -/
@[irreducible] def durLb (γ : GNames) (i : SID) (k : Nat) : IProp GF :=
  monoNatLbOwn (γ.dur i) k

/-- Term `t` is an existing one (some server reached it): a term from a message may be adopted. -/
@[irreducible] def termOk (γ : GNames) (t : Nat) : IProp GF :=
  iprop((∃ j t', isSrv γ j ∗ termLb γ j t' ∗ ⌜t ≤ t'⌝) ∨
    (∃ c li lt, candIs γ c t li lt) ∨ (∃ ℓ, leaderIs γ t ℓ))

/-- (stage 2) The leader of `T` published `k` as its commit index (`setCommitIndex` in leaderLoop's
`commitCh` case). -/
@[irreducible] def pubIs (γ : GNames) (T k : Nat) : IProp GF := (T, k) ↪[γ.pubs]□ ()

/-- (stage 2) **A candidate's publications** (exclusive, held by the main goroutine of `i` from
its election of `T`, `electTerm_upd`): if `i` leads `T`, every publication of `T` is at most `k`
(only `T`'s leader publishes in `T`, `learnCommitLeader`, which raises `k`). -/
@[irreducible] def pubOwn (γ : GNames) (i : SID) (T k : Nat) : IProp GF :=
  (i, T) ↪[γ.pubMax] k

/-- (stage 2) **A snapshot** `s` of the protocol state was taken (persistent): the servers' terms,
durable prefixes and leader-log lengths at some instant, numbered in the order snapshots are taken
(`proto.Snap`, keyed by the servers). Snapshots are ordered (`histLb_order`); the laws `histLb_now`, `srvOwn_now`,
`termCouple_now` take one of the current state. -/
@[irreducible] def histLb (γ : GNames) (s : Snap) : IProp GF :=
  iprop(∃ L : List Snap, monoListLbOwn γ.hist L ∗
    ⌜L.getLast? = some s ∧ (∀ (n : Nat) (x : Snap), L[n]? = some x → x.idx = n) ∧ L.Pairwise snapLe ∧
      γ.srvs.Nodup ∧ ∀ x ∈ L, x.terms.map (·.1) = γ.srvs ∧ x.durs.map (·.1) = γ.srvs⌝)

/-- `lci` may be sent as `LeaderCommitIndex` in term `T` (the commit part of `AEok`): `0`, or
covered by a recorded commit of a term `≤ T` whose leader log agrees with `llog T` up to `lci`,
and (stage 2) by a publication of a term `≤ T`. -/
@[irreducible] def lciOk (γ : GNames) (T lci : Nat) : IProp GF :=
  iprop(⌜lci = 0⌝ ∨
    (∃ (T' k' p' : Nat) (es : List Entry), ⌜T' ≤ T ∧ lci ≤ k' ∧ lci = es.length⌝ ∗ commitIs γ T' k' p' ∗
      ([∗list] j ↦ e ∈ es, llogIdx γ T (j + 1) e ∗ llogIdx γ T' (j + 1) e)) ∗
    (∃ T'' k'', ⌜T'' ≤ T ∧ lci ≤ k''⌝ ∗ pubIs γ T'' k''))

/-- A valid AppendEntries request of term `T` (`proto.AEok`): from the leader of `T`, its previous
entry and entries a slice of `llog T`, its commit index covered. -/
@[irreducible] def aeValid (γ : GNames) (T prev pt : Nat) (ents : List Entry) (lci : Nat) :
    IProp GF :=
  iprop((∃ ℓ, leaderIs γ T ℓ) ∗
    (⌜prev = 0 ∧ pt = 0⌝ ∨ ∃ e, ⌜1 ≤ prev ∧ e.term = pt⌝ ∗ llogIdx γ T prev e) ∗
    ([∗list] j ↦ e ∈ ents, llogIdx γ T (prev + 1 + j) e) ∗
    lciOk γ T lci)

/-! ### Persistence -/

instance Inv_persistent (γ : GNames) : Persistent (Inv (GF := GF) γ) := by
  rw [Inv_unseal]; unfold InvDef; infer_instance

instance isSrv_persistent γ i : Persistent (isSrv (GF := GF) γ i) := by
  unfold isSrv; infer_instance
instance leaderIs_persistent γ T ℓ : Persistent (leaderIs (GF := GF) γ T ℓ) := by
  unfold leaderIs; infer_instance
instance llogIdx_persistent γ T k e : Persistent (llogIdx (GF := GF) γ T k e) := by
  unfold llogIdx; infer_instance
instance len0Is_persistent γ T n : Persistent (len0Is (GF := GF) γ T n) := by
  unfold len0Is; infer_instance
instance candIs_persistent γ c T li lt : Persistent (candIs (GF := GF) γ c T li lt) := by
  unfold candIs; infer_instance
instance voteIs_persistent γ j T c : Persistent (voteIs (GF := GF) γ j T c) := by
  unfold voteIs; infer_instance
instance ackIs_persistent γ j T m : Persistent (ackIs (GF := GF) γ j T m) := by
  unfold ackIs; infer_instance
instance commitIs_persistent γ T k p : Persistent (commitIs (GF := GF) γ T k p) := by
  unfold commitIs; infer_instance
instance llogPre_persistent γ T L : Persistent (llogPre (GF := GF) γ T L) := by
  unfold llogPre; infer_instance
instance cmtIdx_persistent γ T L k : Persistent (cmtIdx (GF := GF) γ T L k) := by
  unfold cmtIdx; infer_instance
instance CIdx_persistent γ k e : Persistent (CIdx (GF := GF) γ k e) := by
  unfold CIdx; infer_instance
instance CLb_persistent γ L : Persistent (CLb (GF := GF) γ L) := by
  unfold CLb; infer_instance
instance termLb_persistent γ i t : Persistent (termLb (GF := GF) γ i t) := by
  unfold termLb; infer_instance
instance durLb_persistent γ i k : Persistent (durLb (GF := GF) γ i k) := by
  unfold durLb; infer_instance
instance termOk_persistent γ t : Persistent (termOk (GF := GF) γ t) := by
  unfold termOk; infer_instance
instance pubIs_persistent γ T k : Persistent (pubIs (GF := GF) γ T k) := by
  unfold pubIs; infer_instance
instance histLb_persistent γ s : Persistent (histLb (GF := GF) γ s) := by
  unfold histLb; infer_instance
instance lciOk_persistent γ T lci : Persistent (lciOk (GF := GF) γ T lci) := by
  unfold lciOk; infer_instance
instance aeValid_persistent γ T prev pt ents lci :
    Persistent (aeValid (GF := GF) γ T prev pt ents lci) := by
  unfold aeValid; infer_instance

end defs

end gprot
end github_com.hashicorp.raft

end Perennial
