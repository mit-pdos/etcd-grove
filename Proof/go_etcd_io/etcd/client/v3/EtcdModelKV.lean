/-
**The clients' model of etcd, over etcd's KV state** (D48, 2026-10-26). Lean-first (no Rocq
counterpart).

The clients (the cache, the recipes, `client/v3/concurrency`, `client/v3/leasing`) state their
results over `EtcdModel GF` (`cache/v3/EtcdModel.lean`). Until D48 the server instantiated it with
its own facts (`v3rpc.etcdModelOfServer`: sealed logs of the store); the clients' contracts were
proved at the server's members. Here it is instead an adapter on top of the client's specs of the
KV and watch methods (`kv.Get.spec`, ..., `watcher.Watch.spec`), whose atomic updates are over
etcd's KV state `etcdKV γ σ` (D44, D47): a client keeps the state's half in an invariant
(`kmInv`), with the list of its changes, an append-only list (`monoListAuthOwn γ.ch`: every change
of the KV is an update of a client, which fires in the invariant), and the revisions' tokens
(`ghostMapAuth γ.tok`, one per revision a write of the client made).

* `kmLog γ W`: `W` is a prefix of the log of a state the client saw (a lower bound of the
  changes, `monoListLbOwn γ.ch`), well formed and small (`kvLogOk`, D48, what the specs give of
  the state a reply reads). Two such logs are in prefix order (`kmLog_two`), which is all the laws
  need, as `v3rpc.srvLog`'s were.
* `etcdState rev pfx s` (`kmEtcdState`), `EtcdStep r0 r1 pfx evs` (`kmStep`): as the server's
  (`srvEtcdState`, `srvStep`), over `kmLog`.
* `etcdReachedAt r`, `etcdReadAt r` (`kmReachedAt`): the client saw a state of revision `r` or
  more (a lower bound of `r` changes). A linearizable read fired after it reads a later state
  (`km_read_au`'s `kmSeenQ`).
* `etcdRevToken r` (`kmRevTok`): the token the invariant minted when a client's write made
  revision `r` (`km_write_au`'s `kmWriteQ`; fired at most once, so a client that sends a write at
  most once, `isKv api γ false`).

Every law is a theorem, the server's proofs over `kmLog` (`txn/HistoryLaws.lean`,
`txn/ClientLaws.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLogOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode mvcc txn

/-! ## Pure lemmas -/

theorem km_longer_log {L1 L2 : Log} (h : L1 <+: L2 ∨ L2 <+: L1) :
    ∃ L, L1 <+: L ∧ L2 <+: L ∧ (L = L1 ∨ L = L2) := by
  rcases h with h | h
  · exact ⟨L2, h, List.prefix_refl _, Or.inr rfl⟩
  · exact ⟨L1, List.prefix_refl _, h, Or.inl rfl⟩

theorem km_toNat_cast {z : Int} (h : 0 ≤ z) : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg h

/-- Prefixes of two lists in prefix order are in prefix order. -/
theorem prefix_cmp_of {α : Type _} {a b c d : List α} (ha : a <+: c) (hb : b <+: d)
    (h : c <+: d ∨ d <+: c) : a <+: b ∨ b <+: a := by
  rcases h with h | h
  · have ha' := ha.trans h
    rcases Nat.le_total a.length b.length with hl | hl
    · exact Or.inl (List.prefix_of_prefix_length_le ha' hb hl)
    · exact Or.inr (List.prefix_of_prefix_length_le hb ha' hl)
  · have hb' := hb.trans h
    rcases Nat.le_total a.length b.length with hl | hl
    · exact Or.inl (List.prefix_of_prefix_length_le ha hb' hl)
    · exact Or.inr (List.prefix_of_prefix_length_le hb' ha hl)

/-- An operation's step commits some changes (unit T3: a lease's grant or revocation also changes
the table, so the step agrees with a commit on the changes and the revision). -/
theorem kvOpStep_commit (op : KVOp) (σ : KVState) : ∃ cs,
    (kvOpStep op σ).changes = (σ.commit cs).changes ∧ (kvOpStep op σ).rev = (σ.commit cs).rev := by
  have h : ∃ cs, (kvOpStep op σ).changes = (σ.commit cs).changes ∧
      (kvOpStep op σ).compacted = (σ.commit cs).compacted := by
    have hn : (σ.commit []) = σ := KVState.commit_nil σ
    cases op with
    | put o =>
      simp only [kvOpStep]
      split
      · exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
      split
      · exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
      · exact ⟨_, rfl, rfl⟩
    | range o => exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
    | deleteRange o => exact ⟨_, rfl, rfl⟩
    | txn t =>
      simp only [kvOpStep]
      split
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
    | leaseGrant id ttl =>
      simp only [kvOpStep]
      split
      · exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
      · exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
    | leaseRevoke id =>
      simp only [kvOpStep]
      split
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨[], by rw [hn]; exact ⟨rfl, rfl⟩⟩
  obtain ⟨cs, h1, h2⟩ := h
  exact ⟨cs, h1, by unfold KVState.rev; rw [h1, h2]⟩

/-- A commit extends the changes, and the revision by one if it changed the state. -/
theorem commit_changes (σ : KVState) (cs : List Change) :
    σ.changes <+: (σ.commit cs).changes ∧
      ((σ.commit cs).rev = σ.rev ∨ (σ.commit cs).rev = σ.rev + 1) := by
  by_cases h : cs = []
  · subst h; rw [KVState.commit_nil]; exact ⟨List.prefix_refl _, Or.inl rfl⟩
  · refine ⟨?_, Or.inr (KVState.commit_rev σ cs h)⟩
    simp only [KVState.commit, h, ↓reduceIte]
    exact List.prefix_append _ _

/-- A state's changes in prefix order: its log, too. -/
theorem log_prefix_of {l1 l2 : List (List Change)} (h : l1 <+: l2) :
    ([] :: l1 : Log) <+: [] :: l2 := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, rfl⟩

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The ghost state -/

/-- The adapter's ghost names: the KV's (its state variable), the list of its changes, the
revisions' tokens; and an application's property of the changes that the invariant keeps (`W`:
every change of the KV is some client's update firing in the invariant, so a client's own fact
about them, D45, e.g. that each revision is one of a plan's writes; `fun _ => True` for none). -/
structure KMNames where
  kv : KVNames
  ch : GName
  tok : GName
  W : List (List Change) → Prop

/-- **A log the client saw** (persistent; see the file header): a prefix of the log of a state
whose changes the client knows a lower bound of, well formed and small. -/
def kmLog (γ : KMNames) (W : Log) : IProp GF :=
  iprop(∃ l : List (List Change), monoListLbOwn γ.ch l ∗
    ⌜W <+: [] :: l ∧ LogWf' W ∧ W.length < 2 ^ 63 ∧ LogSmall W⌝)

instance kmLog_persistent (γ : KMNames) (W : Log) : Persistent (kmLog (GF := GF) γ W) := by
  unfold kmLog; infer_instance

instance kmLog_timeless (γ : KMNames) (W : Log) : Timeless (kmLog (GF := GF) γ W) := by
  unfold kmLog; infer_instance

theorem kmLog_two (γ : KMNames) (L1 L2 : Log) :
    kmLog (GF := GF) γ L1 ∗ kmLog γ L2 ⊢
      ⌜∃ L, L1 <+: L ∧ L2 <+: L ∧ LogWf' L ∧ L.length < 2 ^ 63 ∧ LogSmall L ∧
        (L = L1 ∨ L = L2)⌝ := by
  unfold kmLog
  iintro ⟨⟨%l1, #H1, %h1⟩, ⟨%l2, #H2, %h2⟩⟩
  ihave %Hp := mono_list_lb_valid γ.ch l1 l2 $$ H1 H2
  ipureintro
  have hc : ([] :: l1 : Log) <+: [] :: l2 ∨ ([] :: l2 : Log) <+: [] :: l1 :=
    Hp.imp log_prefix_of log_prefix_of
  obtain ⟨L, p1, p2, hL⟩ := km_longer_log (prefix_cmp_of h1.1 h2.1 hc)
  refine ⟨L, p1, p2, ?_⟩
  rcases hL with rfl | rfl
  · exact ⟨h1.2.1, h1.2.2.1, h1.2.2.2, Or.inl rfl⟩
  · exact ⟨h2.2.1, h2.2.2.1, h2.2.2.2, Or.inr rfl⟩

/-! ## The predicates -/

/-- **etcd's state at `rev` under `pfx`, as the client saw it**: a log it saw has revision `rev`,
and `s` is its state at `rev` restricted to `pfx`. -/
def kmEtcdState (γ : KMNames) (rev : w64) (pfx : GoString) (s : List EtcdKv) : IProp GF :=
  iprop(∃ log : Log, kmLog γ log ∗
    ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧
      s = underPfx pfx (stateAt log (sint.Z rev).toNat)⌝)

/-- **etcd has reached `r`, as the client saw it**: a state of revision `r` or more (a lower bound
of `r` changes). -/
def kmReachedAt (γ : KMNames) (r : w64) : IProp GF :=
  iprop(∃ l : List (List Change), monoListLbOwn γ.ch l ∗ ⌜sint.Z r ≤ l.length⌝)

instance kmReachedAt_persistent (γ : KMNames) (r : w64) :
    Persistent (kmReachedAt (GF := GF) γ r) := by
  unfold kmReachedAt; infer_instance

instance kmReachedAt_timeless (γ : KMNames) (r : w64) :
    Timeless (kmReachedAt (GF := GF) γ r) := by
  unfold kmReachedAt; infer_instance

/-- **A step of etcd's history, as the client saw it**: a log it saw has revision `r1` (above
`r0 ≥ 0`), no event under `pfx` at a revision strictly between `r0` and `r1`, and `evs` are the
events under `pfx` at `r1`. -/
def kmStep (γ : KMNames) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) : IProp GF :=
  iprop(∃ log : Log, kmLog γ log ∗
    ⌜0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < log.length ∧
      (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → revEvs log pfx x = []) ∧
      revEvs log pfx (sint.Z r1).toNat = evs⌝)

instance kmStep_persistent (γ : KMNames) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) :
    Persistent (kmStep (GF := GF) γ r0 r1 pfx evs) := by
  unfold kmStep; infer_instance

instance kmStep_timeless (γ : KMNames) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) :
    Timeless (kmStep (GF := GF) γ r0 r1 pfx evs) := by
  unfold kmStep; infer_instance

/-- **The token of revision `r`**: minted when a client's write made it (`km_write_au`). -/
def kmRevTok (γ : KMNames) (r : w64) : IProp GF :=
  ghostMapElem (K := Nat) (V := Unit) γ.tok (sint.Z r).toNat (DFrac.own 1) ()

/-! ## The laws -/

theorem kmEtcdState_agree (γ : KMNames) (rev : w64) (pfx : GoString) (s s' : List EtcdKv) :
    kmEtcdState (GF := GF) γ rev pfx s ∗ kmEtcdState γ rev pfx s' ⊢ ⌜s = s'⌝ := by
  unfold kmEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]

theorem kmEtcdState_revs (γ : KMNames) (r : w64) (pfx : GoString) (s : List EtcdKv) :
    kmEtcdState (GF := GF) γ r pfx s ⊢
      ⌜∀ v ∈ s, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
        sint.Z v.modRev ≤ sint.Z r ∧ 0 < sint.Z v.version⌝ := by
  unfold kmEtcdState kmLog
  iintro ⟨%L, ⟨%l, -, %Hw⟩, %h⟩
  ipureintro
  obtain ⟨-, hwf, hlen, hs⟩ := Hw
  obtain ⟨h0, hl, rfl⟩ := h
  intro v hv
  have := stateAt_client_revs L hwf hlen hs (sint.Z r).toNat (by omega) v (mem_underPfx.1 hv).1
  rw [km_toNat_cast h0] at this
  exact this

theorem kmEtcdState_create_persist (γ : KMNames) (r a : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    kmEtcdState (GF := GF) γ r pfx s ∗ kmEtcdState γ a pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.createRev ≤ sint.Z a → sint.Z a ≤ sint.Z r →
        ∃ v' ∈ s', v'.key = v.key ∧ v'.createRev = v.createRev⌝ := by
  unfold kmEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := (sint.Z r).toNat) (by omega),
    ← stateAt_of_prefix p2 (r := (sint.Z a).toNat) (by omega)]
  have hr : (sint.Z r).toNat < L.length := by have := p1.length_le; omega
  intro v hv hc ha
  exact stateAtPfx_create_persist L hlen _ _ hr pfx v hv (by rw [km_toNat_cast h2a]; exact hc)
    (by omega)

theorem kmEtcdState_modrev_det (γ : KMNames) (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    kmEtcdState (GF := GF) γ a pfx s ∗ kmEtcdState γ b pfx s' ⊢
      ⌜∀ v ∈ s, ∀ v' ∈ s', v.key = v'.key → v.modRev = v'.modRev → v = v'⌝ := by
  unfold kmEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  exact stateAtPfx_modrev_det L hlen _ _ (by have := p1.length_le; omega)
    (by have := p2.length_le; omega) pfx

theorem kmEtcdState_modrev_persist (γ : KMNames) (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    kmEtcdState (GF := GF) γ a pfx s ∗ kmEtcdState γ b pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝ := by
  unfold kmEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  intro v hv hm hba
  exact stateAtPfx_modrev_persist L hlen _ _ (by have := p1.length_le; omega) pfx v hv
    (by rw [km_toNat_cast h2a]; exact hm) (by omega)

theorem kmRevTok_excl (γ : KMNames) (r : w64) :
    kmRevTok (GF := GF) γ r ∗ kmRevTok γ r ⊢ False := by
  unfold kmRevTok
  iintro ⟨H1, H2⟩
  ihave %Hbad := ghostMapElem_valid_2 (K := Nat) (V := Unit) _ γ.tok _ _ _ _ $$ H1 H2
  exfalso
  have h := DFrac.valid_own_op Hbad.1
  exact absurd h (by decide)

theorem kmStep_transfer (γ : KMNames) (r0 a r1 : w64) (pfx : GoString) (s : List EtcdKv)
    (evs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    kmStep (GF := GF) γ r0 r1 pfx evs ∗ kmEtcdState γ a pfx s ⊢
      kmEtcdState γ r1 pfx (applyEvsState s evs) := by
  unfold kmStep kmEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h10, h1a, h1b, h1q, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  iexists L1
  iframe H1
  ipureintro
  refine ⟨by omega, h1b, ?_⟩
  have e2 : stateAt L2 (sint.Z a).toNat = stateAt L1 (sint.Z a).toNat := by
    rw [← stateAt_of_prefix p1 (r := (sint.Z a).toNat) (by omega),
      ← stateAt_of_prefix p2 (r := (sint.Z a).toNat) (by omega)]
  rw [e2]
  exact (step_transfer L1 pfx (sint.Z a).toNat (sint.Z r1).toNat (by omega) (by omega)
    (fun x hx1 hx2 => h1q x (by omega) (by omega))).symm

theorem kmStep_compose (γ : KMNames) (a b c : w64) (pfx : GoString) (evs : List EtcdEv) :
    kmStep (GF := GF) γ a b pfx [] ∗ kmStep γ b c pfx evs ⊢ kmStep γ a c pfx evs := by
  unfold kmStep
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  obtain ⟨L, p1, p2, -, -, -, hL⟩ := Hl
  obtain ⟨h10, h1a, h1b, h1q, h1e⟩ := h1
  obtain ⟨h20, h2a, h2b, h2q, h2e⟩ := h2
  iexists L
  isplitr
  · rcases hL with rfl | rfl
    · iexact H1
    · iexact H2
  have hl2 : L2.length ≤ L.length := p2.length_le
  ipureintro
  refine ⟨h10, by omega, by omega, ?_, ?_⟩
  · intro x hx1 hx2
    by_cases hxb : (x : Int) < sint.Z b
    · rw [revEvs_prefix p1 (x := x) (by omega)]; exact h1q x hx1 hxb
    · by_cases hxe : (x : Int) = sint.Z b
      · rw [revEvs_prefix p1 (x := x) (by omega)]
        have : (sint.Z b).toNat = x := by omega
        rw [← this]; exact h1e
      · have hxl : x < L2.length := by
          have h2b' : sint.Z c < (L2.length : Int) := h2b
          have hx2' : (x : Int) < sint.Z c := hx2
          omega
        have hbx : sint.Z b < (x : Int) := by omega
        rw [revEvs_prefix p2 hxl]; exact h2q x hbx hx2
  · rw [revEvs_prefix p2 (x := (sint.Z c).toNat) (by omega)]; exact h2e

theorem kmStep_delete_present (γ : KMNames) (r0 a r1 : w64) (pfx : GoString)
    (s : List EtcdKv) (cs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    kmStep (GF := GF) γ r0 r1 pfx cs ∗ kmEtcdState γ a pfx s ⊢
      ⌜∀ (i : Nat) (c : EtcdEv), cs[i]? = some c → c.typ = W32 1 →
        ∃ v ∈ applyEvsState s (cs.take i), v.key = c.kv.key⌝ := by
  unfold kmStep kmEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := kmLog_two γ L1 L2 $$ [$H1 $H2]
  iunfold kmLog at H1
  icases H1 with ⟨%l1, -, %Hw⟩
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h10, h1a, h1b, h1q, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  have e2 : stateAt L2 (sint.Z a).toNat = stateAt L1 (sint.Z a).toNat := by
    rw [← stateAt_of_prefix p1 (r := (sint.Z a).toNat) (by omega),
      ← stateAt_of_prefix p2 (r := (sint.Z a).toNat) (by omega)]
  rw [e2]
  exact step_delete_present L1 Hw.2.1 pfx (sint.Z a).toNat (sint.Z r1).toNat (by omega) (by omega)
    (fun x hx1 hx2 => h1q x (by omega) (by omega))

/-! ## The instance -/

/-- **The clients' model of etcd over its KV state** (see the file header): every field the
adapter's, every law a theorem. -/
@[instance_reducible]
def etcdModelOfKV (γ : KMNames) : EtcdModel GF where
  etcdState := kmEtcdState γ
  etcdState_agree := kmEtcdState_agree γ
  etcdState_revs := kmEtcdState_revs γ
  etcdState_create_persist := kmEtcdState_create_persist γ
  etcdState_modrev_det := kmEtcdState_modrev_det γ
  etcdState_modrev_persist := kmEtcdState_modrev_persist γ
  etcdReachedAt := kmReachedAt γ
  etcdReachedAt_timeless := kmReachedAt_timeless γ
  etcdReadAt := kmReachedAt γ
  etcdReadAt_persistent := kmReachedAt_persistent γ
  etcdReadAt_timeless := kmReachedAt_timeless γ
  etcdRevToken := kmRevTok γ
  etcdRevToken_excl := kmRevTok_excl γ
  EtcdStep := kmStep γ
  EtcdStep_persistent := kmStep_persistent γ
  EtcdStep_timeless := kmStep_timeless γ
  etcdStep_transfer := kmStep_transfer γ
  etcdStep_compose := kmStep_compose γ
  etcdStep_delete_present := kmStep_delete_present γ

theorem etcdModelOfKV_etcdState (γ : KMNames) :
    (etcdModelOfKV (GF := GF) γ).etcdState = kmEtcdState γ := rfl
theorem etcdModelOfKV_etcdReachedAt (γ : KMNames) :
    (etcdModelOfKV (GF := GF) γ).etcdReachedAt = kmReachedAt γ := rfl
theorem etcdModelOfKV_etcdReadAt (γ : KMNames) :
    (etcdModelOfKV (GF := GF) γ).etcdReadAt = kmReachedAt γ := rfl
theorem etcdModelOfKV_etcdRevToken (γ : KMNames) :
    (etcdModelOfKV (GF := GF) γ).etcdRevToken = kmRevTok γ := rfl
theorem etcdModelOfKV_EtcdStep (γ : KMNames) :
    (etcdModelOfKV (GF := GF) γ).EtcdStep = kmStep γ := rfl

/-! ## The invariant and the updates -/

/-- The adapter's namespace. -/
def kmN : Namespace := nroot .@ "client_kv_model"

theorem kmN_mask : (↑kmN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- **The adapter's invariant** (see the file header): the KV state's half, the list of its
changes, the revisions' tokens minted (each at most the state's revision), and the application's
property of the changes (`γ.W`). -/
def kmInv (γ : KMNames) : IProp GF :=
  inv kmN iprop(∃ (σ : KVState) (m : GMap Nat Unit), etcdKV γ.kv σ ∗
    monoListAuthOwn γ.ch 1 σ.changes ∗ ghostMapAuth γ.tok 1 m ∗
    ⌜(∀ n, m.lookup n ≠ none → n ≤ σ.rev) ∧ γ.W σ.changes⌝)

instance kmInv_persistent (γ : KMNames) : Persistent (kmInv (GF := GF) γ) := by
  unfold kmInv; infer_instance

/-- **The adapter's start** from the KV state's half, with an application's property of its
changes (`W`, true of the start's): its invariant, and the start's changes seen. -/
theorem kmInv_alloc (γk : KVNames) (σ0 : KVState) (W : List (List Change) → Prop)
    (hW : W σ0.changes) :
    etcdKV (GF := GF) γk σ0 ⊢ |={⊤}=> ∃ γ : KMNames, ⌜γ.kv = γk ∧ γ.W = W⌝ ∗ kmInv γ ∗
      monoListLbOwn γ.ch σ0.changes := by
  iintro Hσ
  imod (mono_list_own_alloc (GF := GF) σ0.changes) with ⟨%γc, Hc, #Hlb⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit)) with ⟨%γt, Ht⟩
  imod (inv_alloc kmN ⊤ iprop(∃ (σ : KVState) (m : GMap Nat Unit), etcdKV (GF := GF) γk σ ∗
      monoListAuthOwn γc 1 σ.changes ∗ ghostMapAuth γt 1 m ∗
      ⌜(∀ n, m.lookup n ≠ none → n ≤ σ.rev) ∧ W σ.changes⌝)) $$ [Hσ Hc Ht] with #Hinv
  · inext
    iexists σ0, ∅
    iframe
    ipureintro
    exact ⟨fun n hn => by simp at hn, hW⟩
  imodintro
  iexists ⟨γk, γc, γt, W⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iframe Hlb
  unfold kmInv
  iexact Hinv

/-- **What a read learns**: the state read is one the client saw (its changes' lower bound), at or
after the changes `l0` it saw before. -/
def kmSeenQ (γ : KMNames) (l0 : List (List Change)) (σ : KVState) : IProp GF :=
  iprop(monoListLbOwn γ.ch σ.changes ∗ ⌜l0 <+: σ.changes⌝)

instance kmSeenQ_persistent (γ : KMNames) (l0 : List (List Change)) (σ : KVState) :
    Persistent (kmSeenQ (GF := GF) γ l0 σ) := by
  unfold kmSeenQ; infer_instance

/-- **A read update at the adapter** (persistent): fired at the KV's state, it learns that the
client saw it, after `l0`. -/
theorem km_read_au (γ : KMNames) (l0 : List (List Change)) :
    kmInv (GF := GF) γ ∗ monoListLbOwn γ.ch l0 ⊢ kvReadAu γ.kv (kmSeenQ γ l0) := by
  have Hm := kmN_mask
  iintro ⟨#Hinv, #Hl0⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold kmInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %m, Hσ, Hc, Ht, %Hm⟩
  ihave %Hp := mono_list_auth_lb_valid γ.ch 1 σ.changes l0 $$ Hc Hl0
  ihave #Hlb := monoListLbOwn_get γ.ch 1 σ.changes $$ Hc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑kmN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc Ht] with -
    · inext; iexists σ, m; iframe; ipureintro; exact Hm
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc Ht] with -
    · inext; iexists σ, m; iframe; ipureintro; exact Hm
    imodintro
    imodintro
    unfold kmSeenQ
    iframe Hlb
    ipureintro; exact Hp.2

/-- **What a write learns** (fired once): the state after it is one the client saw, the state it
met after the changes `l0`, and, if the write made a revision, that revision's token. -/
def kmWriteQ (γ : KMNames) (l0 : List (List Change)) (op : KVOp) (σ : KVState) : IProp GF :=
  iprop(monoListLbOwn γ.ch (kvOpStep op σ).changes ∗ monoListLbOwn γ.ch σ.changes ∗
    ⌜l0 <+: σ.changes⌝ ∗
    (if (kvOpStep op σ).rev = σ.rev + 1 then
      ghostMapElem (K := Nat) (V := Unit) γ.tok (σ.rev + 1) (DFrac.own 1) ()
     else iprop(True)))

/-- **Every operation keeps the application's property** (`γ.W`; e.g. none, `fun _ => True`,
`KMWritable.of_true`): what the clients' write contracts take, any write being allowed. -/
class KMWritable (γ : KMNames) : Prop where
  keep : ∀ (op : KVOp) (σ : KVState), γ.W σ.changes → γ.W (kvOpStep op σ).changes

theorem KMWritable.of_true (γ : KMNames) (h : ∀ c, γ.W c) : KMWritable γ := ⟨fun _ _ _ => h _⟩

/-- **A write's update at the adapter** (fired at most once): the KV's step by `op`, minting the
token of the revision it makes; the step keeps the application's property (`hW`). -/
theorem km_write_au (γ : KMNames) (l0 : List (List Change)) (op : KVOp)
    (hW : ∀ σ : KVState, γ.W σ.changes → γ.W (kvOpStep op σ).changes) :
    kmInv (GF := GF) γ ∗ monoListLbOwn γ.ch l0 ⊢ kvOpAu1 γ.kv op (kmWriteQ γ l0 op) := by
  have Hm := kmN_mask
  iintro ⟨#Hinv, #Hl0⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc
  iunfold kmInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %m, Hσ, Hc, Ht, %Hm⟩
  ihave %Hp := mono_list_auth_lb_valid γ.ch 1 σ.changes l0 $$ Hc Hl0
  ihave #Hlb := monoListLbOwn_get γ.ch 1 σ.changes $$ Hc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑kmN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc Ht] with -
    · inext; iexists σ, m; iframe; ipureintro; exact Hm
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    obtain ⟨cs, hc1, hc2⟩ := kvOpStep_commit op σ
    obtain ⟨hpre, hrev⟩ := commit_changes σ cs
    rw [← hc1] at hpre
    rw [← hc2] at hrev
    imod (monoListAuthOwn_update (kvOpStep op σ).changes hpre) $$ Hc with ⟨Hc, #Hlb'⟩
    by_cases hr : (kvOpStep op σ).rev = σ.rev + 1
    · -- a new revision: its token
      have hfresh : m.lookup (σ.rev + 1) = none := by
        cases h : m.lookup (σ.rev + 1) with
        | none => rfl
        | some _ => have := Hm.1 _ (by rw [h]; simp); omega
      imod (ghost_map_insert (σ.rev + 1) () hfresh) $$ Ht with ⟨Ht, Htok⟩
      imod Hclose $$ [Hσ Hc Ht] with -
      · inext; iexists kvOpStep op σ, _; iframe
        ipureintro
        refine ⟨fun n hn => ?_, hW σ Hm.2⟩
        by_cases hn1 : n = σ.rev + 1
        · omega
        · have : m.lookup n ≠ none := by
            have h' := GMap.lookup_insert_ne m (v := ()) (Ne.symm hn1)
            exact fun h0 => hn (by rw [← h0]; exact h')
          have := Hm.1 n this; omega
      imodintro
      unfold kmWriteQ
      iframe Hlb' Hlb
      isplitr
      · ipureintro; exact Hp.2
      rw [ite_cond_eq_true _ _ (eq_true hr)]
      iexact Htok
    · imod Hclose $$ [Hσ Hc Ht] with -
      · inext; iexists kvOpStep op σ, m; iframe
        ipureintro
        refine ⟨fun n hn => ?_, hW σ Hm.2⟩
        have := Hm.1 n hn
        rcases hrev with h | h <;> omega
      imodintro
      unfold kmWriteQ
      iframe Hlb' Hlb
      isplitr
      · ipureintro; exact Hp.2
      rw [ite_cond_eq_false _ _ (eq_false hr)]
      itrivial

/-! ## What the specs' replies give the model -/

/-- **etcd's state at a revision of a state the client saw** (persistent), well formed through
it (`kvLogOkTo`): the state at `r` restricted to `pfx`, well formed under `pfx`. -/
theorem km_etcdState_of (γ : KMNames) (σ : KVState) (r : Nat) (pfx : GoString)
    (h : kvLogOkTo σ r) :
    monoListLbOwn (GF := GF) γ.ch σ.changes ⊢
      □ kmEtcdState γ (W64 (r : Int)) pfx (underPfx pfx (stateAt σ.log r)) ∗
      ⌜EtcdStateWf pfx (underPfx pfx (stateAt σ.log r))⌝ := by
  obtain ⟨he, hr, hr63, hw, hs⟩ := h
  have hc : σ.compacted = 0 := by rw [he]; rfl
  have hrl : r + 1 ≤ σ.log.length := by
    simp only [KVState.log, List.length_cons]
    simp only [KVState.rev, hc] at hr; omega
  have hz : sint.Z (W64 (r : Int)) = r := by word
  iintro #Hlb
  isplitl
  · imodintro
    unfold kmEtcdState
    iexists σ.log.take (r + 1)
    isplitl
    · unfold kmLog
      iexists σ.changes
      iframe Hlb
      ipureintro
      refine ⟨List.take_prefix _ _, hw, ?_, hs⟩
      rw [List.length_take]; omega
    ipureintro
    refine ⟨by rw [hz]; omega, by rw [hz, List.length_take]; omega, ?_⟩
    rw [hz, show ((r : Int)).toNat = r by omega,
      stateAt_of_prefix (List.take_prefix (r + 1) σ.log) (r := r) (by rw [List.length_take]; omega)]
  · ipureintro; exact stateAtPfx_wf σ.log r pfx

/-- A well-formed state's revision is its number of changes, its store its log's last. -/
theorem kvLogOk_rev (σ : KVState) (h : kvLogOk σ) : σ.rev = σ.changes.length := by
  have hc : σ.compacted = 0 := by rw [h.1]; rfl
  simp only [KVState.rev, hc, Nat.zero_add]

theorem kvLogOk_kvs (σ : KVState) (h : kvLogOk σ) : σ.kvs = stateAfter σ.log := by
  have he := h.1
  have : σ.kvs = (kvStateOf σ.log).kvs := by rw [← he]
  rw [this, kvStateOf_kvs]

/-- **A floor from what the caller knows** (`etcdReached lo`): changes the client saw, `lo` of
them or more. -/
theorem km_reached_lb (γ : KMNames) (lo : w64) :
    etcdReached (EM := etcdModelOfKV (GF := GF) γ) lo ⊢
      |==> ∃ l0 : List (List Change), monoListLbOwn γ.ch l0 ∗ ⌜sint.Z lo ≤ l0.length⌝ := by
  unfold etcdReached
  iintro (%H | ⟨%r', %Hr, #Ha⟩)
  · imod (monoListLbOwn_nil (GF := GF) (A := List Change) γ.ch) with #H0
    imodintro
    iexists []
    iframe H0
    ipureintro; simp; omega
  · rw [etcdModelOfKV_etcdReachedAt]
    iunfold kmReachedAt at Ha
    icases Ha with ⟨%l, #Hl, %Hle⟩
    imodintro
    iexists l
    iframe Hl
    ipureintro; omega

/-- **etcd has reached a revision the client saw** (`etcdReached`, `etcdReadAt`). -/
theorem km_reached_of (γ : KMNames) (l : List (List Change)) (n : Nat) (h : n ≤ l.length)
    (h63 : n < 2 ^ 63) :
    monoListLbOwn (GF := GF) γ.ch l ⊢
      etcdReached (EM := etcdModelOfKV γ) (W64 (n : Int)) ∗ kmReachedAt γ (W64 (n : Int)) := by
  have hz : sint.Z (W64 (n : Int)) = n := by word
  iintro #Hl
  ihave #Ha : kmReachedAt γ (W64 (n : Int)) $$ []
  · unfold kmReachedAt; iexists l; iframe Hl; ipureintro; omega
  iframe Ha
  unfold etcdReached
  iright
  iexists W64 (n : Int)
  isplitr
  · ipureintro; exact Int.le_refl _
  imodintro
  rw [etcdModelOfKV_etcdReachedAt]
  iexact Ha

/-- **etcd's state at a well-formed state's current revision** (`km_etcdState_of` at the last). -/
theorem km_etcdState_last (γ : KMNames) (σ : KVState) (pfx : GoString) (h : kvLogOk σ) :
    monoListLbOwn (GF := GF) γ.ch σ.changes ⊢
      □ kmEtcdState γ (W64 (σ.rev : Int)) pfx (underPfx pfx (stateAfter σ.log)) ∗
      ⌜EtcdStateWf pfx (underPfx pfx (stateAfter σ.log))⌝ := by
  have hl := (kvLogOk_log h).2.2.2
  have hst : stateAt σ.log σ.rev = stateAfter σ.log := by
    rw [show σ.rev = σ.log.length - 1 by omega, stateAt_last]
  rw [← hst]
  exact km_etcdState_of γ σ σ.rev pfx h

end ghost

end client
end EtcdGrove
end Perennial
