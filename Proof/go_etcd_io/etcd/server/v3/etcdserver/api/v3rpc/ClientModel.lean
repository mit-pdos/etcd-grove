/-
**The clients' model of etcd, implemented by the server** (the vertical slice's unit V1,
2026-10-13; `notes/STATUS.md`, "The vertical slice: client to server"; `notes/decisions.md`, "The
client's model as a class the server instantiates; the wire as the handler's theorem
transported"). Lean-first, no Rocq counterpart.

The clients (the cache, `client/v3/concurrency`, `client/v3/leasing`, the recipes) state their
results over `EtcdModel GF` (`cache/v3/EtcdModel.lean`): four predicates and their laws, fourteen
axioms until V1. `etcdModelOfServer E γr on` instantiates it with the server's facts, for the server whose apply
thread's environment is `E` (the revisions' tokens, the committed log's lower bounds `E.γs`), at
its read names `γr` and auth mode `on` (the raft witness `srvApi.kvNx γr on`, which the store
invariant's logs carry). Strict M1 (2026-11-05): over the server's witness, with no mvcc internal
(mvcc's seals `idxSealed`, certificates `idxCert`/`certOk` and `storeSmall` are gone):

* `etcdState rev pfx s` (`srvEtcdState`): some log of the server's history (`srvLog`: a prefix of
  the KV model of a committed raft log, well formed, fewer than `2 ^ 63` revisions, small, its keys
  short) has revision `rev`, and its state at `rev` restricted to `pfx` is `s`. A read's log is one
  (its witness `E.Nx log`, `srvLog_of_nx`; `etcdState_of_nx`), and so is a certified lower bound
  of the notified log, the watch path's `histLb` (`srvLog_of_histLb`).
* `etcdReachedAt r` (`srvReachedAt`, unit W-M3): `srvApi.srvRevLbA`, the KV model of a committed
  raft log has revision `r` (`etcdReached_of_nx`).
* `etcdReadAt r` (`srvReadAt`): a lower bound of the committed log (`srvApi.kvLogLb E.γs`) has
  revision `r`.
* `etcdRevToken r` (`revTok E r`, `InvRequest.lean`): the token the apply thread minted when the
  KV's log grew to revision `r` (`revAuth_step`), carried by the entry's result to the proposer.
* `EtcdStep r0 r1 pfx evs` (`srvStep`): some log of the server's history has revision `r1`, no
  event under `pfx` strictly between `r0` and `r1` (`txn.revEvs`), and `evs` are `r1`'s.

Two logs of the history are in prefix order (`srvLog_two`: the committed raft logs are, and the
model grows with them, `kvModelM_prefix`), which is all the laws need of the logs. Every law is a
theorem (`txn/HistoryLaws.lean`, `txn/ClientLaws.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreRead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode mvcc txn

/-! ## Pure lemmas: two sealed logs -/

theorem longer_log {L1 L2 : Log} (h : L1 <+: L2 ∨ L2 <+: L1) :
    ∃ L, L1 <+: L ∧ L2 <+: L ∧ (L = L1 ∨ L = L2) := by
  rcases h with h | h
  · exact ⟨L2, h, List.prefix_refl _, Or.inr rfl⟩
  · exact ⟨L1, List.prefix_refl _, h, Or.inl rfl⟩

theorem toNat_cast {z : Int} (h : 0 ≤ z) : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg h

/-- A range under the prefix selects the same keys from the state and its restriction. -/
theorem rangeIn_underPfx (pfx : GoString) (s : List EtcdKv) (o : OpFull)
    (h : KeyRangeUnder pfx o.key o.base.rangeEnd) : rangeIn (underPfx pfx s) o = rangeIn s o := by
  unfold rangeIn underPfx
  rw [List.filter_filter]
  apply List.filter_congr
  intro v _
  by_cases hi : inRange o.key o.base.rangeEnd v.key = true
  · simp [hi, h v.key hi]
  · simp [hi]

theorem rangeSel_underPfx (pfx : GoString) (s : List EtcdKv) (o : OpFull)
    (h : KeyRangeUnder pfx o.key o.base.rangeEnd) : rangeSel (underPfx pfx s) o = rangeSel s o := by
  unfold rangeSel; rw [rangeIn_underPfx pfx s o h]

theorem underPfx_wf (log : Log) (r : Nat) (pfx : GoString) :
    EtcdStateWf pfx (underPfx pfx (stateAt log r)) := stateAtPfx_wf log r pfx

/-- A prefix of a well-formed log is well formed (`LogWf'.prefix`, iterated). -/
theorem logWf'_of_prefix {L L' : Log} (h : L <+: L') (hw : LogWf' L') : LogWf' L := by
  obtain ⟨D, rfl⟩ := h
  induction D generalizing L with
  | nil => simpa using hw
  | cons d D ih =>
    have : LogWf' (L ++ [d]) := ih (by rw [List.append_assoc]; exact hw)
    exact this.prefix

section model
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A mode-`on` entry's step extends the model's log. -/
theorem kvEntryOn_extends (c₀ : w64) (ch : apply.Chain) (st : auth.AuthState × Log)
    (m : EntryModel) : st.2 <+: (kvEntryOn c₀ ch st m).2 := by
  unfold kvEntryOn
  split
  · split
    · split
      · exact List.prefix_refl _
      · split
        · exact List.prefix_refl _
        · exact kvEntry_prefix c₀ ch [] st.2 m
    · exact List.prefix_refl _
  · exact kvEntry_prefix c₀ ch [] st.2 m

theorem kvRaftOfOn_extends (c₀ : w64) (ch : apply.Chain) (B : List EntryModel) :
    ∀ st : auth.AuthState × Log, st.2 <+: (kvRaftOfOn c₀ ch st B).2 := by
  induction B with
  | nil => intro st; exact List.prefix_refl _
  | cons m B ih =>
    intro st
    exact (kvEntryOn_extends c₀ ch st m).trans (ih (kvEntryOn c₀ ch st m))

/-- **The KV model (either mode) grows with the raft log.** -/
theorem kvModelM_prefix (on : Bool) (γk : KVNames) (A B : List EntryModel) (h : A <+: B) :
    kvModelM on γk A <+: kvModelM on γk B := by
  cases on
  · exact kvRaftOf_prefix _ _ _ _ _ h
  · obtain ⟨D, rfl⟩ := h
    show (kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0) A).2 <+:
      (kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0) (A ++ D)).2
    rw [kvRaftOfOn_append]
    exact kvRaftOfOn_extends _ _ D _


/-! ## The predicates -/

/-- **A log of the server's history** (strict M1, 2026-11-05: over the server's raft witness
`srvApi.kvNx γr on`, in place of mvcc's seal `idxSealed`): a prefix of the KV model (in the auth
mode `on`) of a committed raft log, well formed, of fewer than `2 ^ 63` revisions, small
(`LogSmall`: at most `2 ^ 62` changes) and (2026-10-30, `notes/keylen.md`) its keys short. A
read's log is one (its witness `E.Nx log`, `srvLog_of_nx`), and so is a certified lower bound of
the notified log (`histLb`, the watch path's, `srvLog_of_histLb`); two are in prefix order
(`srvLog_two`: the committed raft logs are). Not `srvApi.srvLogA` (`histLb`'s): a read's log, a
lower bound of the committed log, is not one of the notified log. -/
def srvLog (γr : ReadNames) (on : Bool) (log : Log) : IProp GF :=
  iprop(∃ L' : Log, srvApi.kvNx γr on L' ∗
    ⌜log <+: L' ∧ LogWf' log ∧ log.length < 2 ^ 63 ∧ LogSmall log ∧ mvcc.LogPutsLe etcdKeyMax log⌝)

instance srvLog_persistent (γr : ReadNames) (on : Bool) (log : Log) :
    Persistent (srvLog (GF := GF) γr on log) := by
  unfold srvLog; infer_instance

instance srvLog_timeless (γr : ReadNames) (on : Bool) (log : Log) :
    Timeless (srvLog (GF := GF) γr on log) := by
  unfold srvLog; infer_instance

/-- **etcd's state at `rev` under `pfx`, on the server**: a log of the server's history has
revision `rev`, and `s` is its state at `rev` restricted to `pfx`. -/
def srvEtcdState (γr : ReadNames) (on : Bool) (rev : w64) (pfx : GoString) (s : List EtcdKv) :
    IProp GF :=
  iprop(∃ log : Log, srvLog γr on log ∗
    ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧
      s = underPfx pfx (stateAt log (sint.Z rev).toNat)⌝)

/-- **etcd has reached `r`, on the server** (unit W-M3; strict M1: `srvApi.srvRevLbA`, raft-only):
the KV model of a committed raft log has revision `r`. -/
def srvReachedAt (γr : ReadNames) (on : Bool) (r : w64) : IProp GF :=
  srvApi.srvRevLbA γr on (sint.Z r)

instance srvReachedAt_timeless (γr : ReadNames) (on : Bool) (r : w64) :
    Timeless (srvReachedAt (GF := GF) γr on r) := by
  unfold srvReachedAt srvApi.srvRevLbA; infer_instance

/-- **The store had committed `r`, on the server** (K2e-6; strict M1: a lower bound of the
committed log, `srvApi.kvLogLb`, in place of mvcc's `idxCert`) has revision `r`. -/
def srvReadAt (E : apply.AEnv GF) (r : w64) : IProp GF :=
  iprop(∃ log : Log, srvApi.kvLogLb E.γs log ∗ ⌜sint.Z r < log.length⌝)

instance srvReadAt_persistent (E : apply.AEnv GF) (r : w64) : Persistent (srvReadAt E r) := by
  unfold srvReadAt srvApi.kvLogLb; infer_instance

instance srvReadAt_timeless (E : apply.AEnv GF) (r : w64) : Timeless (srvReadAt E r) := by
  unfold srvReadAt srvApi.kvLogLb; infer_instance

/-- **A step of etcd's history, on the server**: a log of the server's history has revision `r1`
(above `r0 ≥ 0`), no event under `pfx` at a revision strictly between `r0` and `r1`, and `evs`
are the events under `pfx` at `r1`. (D23, 2026-10-20: the log a prefix of the KV model of a
committed raft log, so that a client knowing what the committed log holds knows the step's;
strict M1: `srvLog`'s witness, mvcc's `certOk` gone.) -/
def srvStep (γr : ReadNames) (on : Bool) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) :
    IProp GF :=
  iprop(∃ log : Log, srvLog γr on log ∗
    ⌜0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < log.length ∧
      (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → revEvs log pfx x = []) ∧
      revEvs log pfx (sint.Z r1).toNat = evs⌝)

instance srvStep_persistent (γr : ReadNames) (on : Bool) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : Persistent (srvStep (GF := GF) γr on r0 r1 pfx evs) := by
  unfold srvStep; infer_instance

instance srvStep_timeless (γr : ReadNames) (on : Bool) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : Timeless (srvStep (GF := GF) γr on r0 r1 pfx evs) := by
  unfold srvStep; infer_instance

/-! ## Two logs of the history -/

theorem srvLog_two (γr : ReadNames) (on : Bool) (L1 L2 : Log) :
    srvLog (GF := GF) γr on L1 ∗ srvLog γr on L2 ⊢
      ⌜∃ L, L1 <+: L ∧ L2 <+: L ∧ LogWf' L ∧ L.length < 2 ^ 63 ∧ LogSmall L ∧
        (L = L1 ∨ L = L2)⌝ := by
  unfold srvLog srvApi.kvNx
  iintro ⟨⟨%M1, ⟨%A1, #HA1, %hA1⟩, %h1⟩, ⟨%M2, ⟨%A2, #HA2, %hA2⟩, %h2⟩⟩
  ihave %Hp := srvRLogLb_prefix γr.raft A1 A2 $$ [$HA1 $HA2]
  ipureintro
  obtain ⟨hA1, -⟩ := hA1
  obtain ⟨hA2, -⟩ := hA2
  obtain ⟨p1, w1, l1, s1, -⟩ := h1
  obtain ⟨p2, w2, l2, s2, -⟩ := h2
  have hM : M1 <+: M2 ∨ M2 <+: M1 := by
    subst hA1 hA2
    rcases Hp with h | h
    · exact Or.inl (kvModelM_prefix on γr.kv _ _ h)
    · exact Or.inr (kvModelM_prefix on γr.kv _ _ h)
  have hc : L1 <+: L2 ∨ L2 <+: L1 := by
    rcases hM with h | h
    · exact List.prefix_or_prefix_of_prefix (p1.trans h) p2
    · exact List.prefix_or_prefix_of_prefix p1 (p2.trans h)
  obtain ⟨L, q1, q2, hL⟩ := longer_log hc
  refine ⟨L, q1, q2, ?_⟩
  rcases hL with rfl | rfl
  · exact ⟨w1, l1, s1, Or.inl rfl⟩
  · exact ⟨w2, l2, s2, Or.inr rfl⟩

/-! ## The laws -/

theorem srvEtcdState_agree (γr : ReadNames) (on : Bool) (rev : w64) (pfx : GoString) (s s' : List EtcdKv) :
    srvEtcdState (GF := GF) γr on rev pfx s ∗ srvEtcdState (GF := GF) γr on rev pfx s' ⊢ ⌜s = s'⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]

theorem srvEtcdState_revs (γr : ReadNames) (on : Bool) (r : w64) (pfx : GoString) (s : List EtcdKv) :
    srvEtcdState (GF := GF) γr on r pfx s ⊢
      ⌜∀ v ∈ s, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
        sint.Z v.modRev ≤ sint.Z r ∧ 0 < sint.Z v.version⌝ := by
  unfold srvEtcdState srvLog
  iintro ⟨%L, ⟨%M, -, %Hs⟩, %h⟩
  ipureintro
  obtain ⟨h0, hl, rfl⟩ := h
  intro v hv
  have := stateAt_client_revs L Hs.2.1 Hs.2.2.1 Hs.2.2.2.1 (sint.Z r).toNat (by omega) v (mem_underPfx.1 hv).1
  rw [toNat_cast h0] at this
  exact this

/-- **Keys are short** (2026-10-30, `notes/keylen.md`): the sealed log's. -/
theorem srvEtcdState_keys (γr : ReadNames) (on : Bool) (r : w64) (pfx : GoString) (s : List EtcdKv) :
    srvEtcdState (GF := GF) γr on r pfx s ⊢ ⌜∀ v ∈ s, v.key.length ≤ etcdKeyMax⌝ := by
  unfold srvEtcdState srvLog
  iintro ⟨%L, ⟨%M, -, %Hs⟩, %h⟩
  ipureintro
  obtain ⟨-, -, rfl⟩ := h
  intro v hv
  exact stateAt_keys Hs.2.2.2.2 _ v (mem_underPfx.1 hv).1

theorem srvEtcdState_vals (γr : ReadNames) (on : Bool) (r : w64) (pfx : GoString) (s : List EtcdKv) :
    srvEtcdState (GF := GF) γr on r pfx s ⊢ ⌜∀ v ∈ s, v.value.length ≤ etcdKeyMax⌝ := by
  unfold srvEtcdState srvLog
  iintro ⟨%L, ⟨%M, -, %Hs⟩, %h⟩
  ipureintro
  obtain ⟨-, -, rfl⟩ := h
  intro v hv
  exact stateAt_vals Hs.2.2.2.2 _ v (mem_underPfx.1 hv).1

theorem srvEtcdState_create_persist (γr : ReadNames) (on : Bool) (r a : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    srvEtcdState (GF := GF) γr on r pfx s ∗ srvEtcdState (GF := GF) γr on a pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.createRev ≤ sint.Z a → sint.Z a ≤ sint.Z r →
        ∃ v' ∈ s', v'.key = v.key ∧ v'.createRev = v.createRev⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := (sint.Z r).toNat) (by omega),
    ← stateAt_of_prefix p2 (r := (sint.Z a).toNat) (by omega)]
  have hr : (sint.Z r).toNat < L.length := by have := p1.length_le; omega
  intro v hv hc ha
  exact stateAtPfx_create_persist L hlen _ _ hr pfx v hv (by rw [toNat_cast h2a]; exact hc)
    (by omega)

theorem srvEtcdState_modrev_det (γr : ReadNames) (on : Bool) (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    srvEtcdState (GF := GF) γr on a pfx s ∗ srvEtcdState (GF := GF) γr on b pfx s' ⊢
      ⌜∀ v ∈ s, ∀ v' ∈ s', v.key = v'.key → v.modRev = v'.modRev → v = v'⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  exact stateAtPfx_modrev_det L hlen _ _ (by have := p1.length_le; omega)
    (by have := p2.length_le; omega) pfx

theorem srvEtcdState_modrev_persist (γr : ReadNames) (on : Bool) (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    srvEtcdState (GF := GF) γr on a pfx s ∗ srvEtcdState (GF := GF) γr on b pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  intro v hv hm hba
  exact stateAtPfx_modrev_persist L hlen _ _ (by have := p1.length_le; omega) pfx v hv
    (by rw [toNat_cast h2a]; exact hm) (by omega)

theorem srvStep_transfer (γr : ReadNames) (on : Bool) (r0 a r1 : w64) (pfx : GoString) (s : List EtcdKv)
    (evs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    srvStep (GF := GF) γr on r0 r1 pfx evs ∗ srvEtcdState (GF := GF) γr on a pfx s ⊢
      srvEtcdState (GF := GF) γr on r1 pfx (applyEvsState s evs) := by
  unfold srvStep srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
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

/-- **Restriction** (`EtcdModel.etcdStep_restrict`): the quiet part of a step is a quiet step, over
the same log. -/
theorem srvStep_restrict (γr : ReadNames) (on : Bool) (p a x b : w64) (pfx : GoString) (evs : List EtcdEv) :
    sint.Z p ≤ sint.Z a → sint.Z a < sint.Z x → (sint.Z x < sint.Z b ∨ (x = b ∧ evs = [])) →
    srvStep (GF := GF) γr on p b pfx evs ⊢ srvStep (GF := GF) γr on a x pfx [] := by
  intro hpa hax hxb
  unfold srvStep
  iintro ⟨%L, #H, %h⟩
  iexists L
  isplitr
  · iexact H
  ipureintro
  obtain ⟨h0, h1, h2, hq, he⟩ := h
  have hxb' : sint.Z x ≤ sint.Z b := by rcases hxb with h | ⟨rfl, -⟩ <;> omega
  refine ⟨by omega, by omega, by omega, fun y hy1 hy2 => hq y (by omega) (by omega), ?_⟩
  rcases hxb with hxb | ⟨rfl, rfl⟩
  · exact hq _ (by omega) (by omega)
  · exact he

theorem srvStep_compose (γr : ReadNames) (on : Bool) (a b c : w64) (pfx : GoString) (evs : List EtcdEv) :
    srvStep (GF := GF) γr on a b pfx [] ∗ srvStep (GF := GF) γr on b c pfx evs ⊢ srvStep (GF := GF) γr on a c pfx evs := by
  unfold srvStep
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
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

theorem srvStep_delete_present (γr : ReadNames) (on : Bool) (r0 a r1 : w64) (pfx : GoString)
    (s : List EtcdKv) (cs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    srvStep (GF := GF) γr on r0 r1 pfx cs ∗ srvEtcdState (GF := GF) γr on a pfx s ⊢
      ⌜∀ (i : Nat) (c : EtcdEv), cs[i]? = some c → c.typ = W32 1 →
        ∃ v ∈ applyEvsState s (cs.take i), v.key = c.kv.key⌝ := by
  unfold srvStep srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two (GF := GF) γr on L1 L2 $$ [$H1 $H2]
  iunfold srvLog at H1
  icases H1 with ⟨%M, -, %Hw⟩
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

/-- **The server's instance of the clients' model of etcd** (see the file header): every field
the server's fact, every law a theorem. A `def`, applied where the slice is stated. Strict M1
(2026-11-05): at the read names `γr` and the auth mode `on` of the server's raft witness
(`srvApi.kvNx γr on`, the store invariant's), beside the apply thread's environment `E` (the
revisions' tokens, the committed log's lower bounds). -/
@[instance_reducible]
def etcdModelOfServer (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) : EtcdModel GF where
  etcdState := srvEtcdState γr on
  etcdState_agree := srvEtcdState_agree γr on
  etcdState_revs := srvEtcdState_revs γr on
  etcdState_keys := srvEtcdState_keys γr on
  etcdState_vals := srvEtcdState_vals γr on
  etcdState_create_persist := srvEtcdState_create_persist γr on
  etcdState_modrev_det := srvEtcdState_modrev_det γr on
  etcdState_modrev_persist := srvEtcdState_modrev_persist γr on
  etcdReachedAt := srvReachedAt γr on
  etcdReachedAt_timeless := srvReachedAt_timeless γr on
  etcdReadAt := srvReadAt E
  etcdReadAt_persistent := srvReadAt_persistent E
  etcdReadAt_timeless := srvReadAt_timeless E
  etcdRevToken := revTok E
  etcdRevToken_excl := revTok_excl E
  EtcdStep := srvStep γr on
  EtcdStep_persistent := srvStep_persistent γr on
  EtcdStep_timeless := srvStep_timeless γr on
  etcdStep_transfer := srvStep_transfer γr on
  etcdStep_compose := srvStep_compose γr on
  etcdStep_restrict := srvStep_restrict γr on
  etcdStep_delete_present := srvStep_delete_present γr on

theorem etcdModelOfServer_etcdState (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) :
    (etcdModelOfServer E γr on).etcdState = srvEtcdState γr on := rfl
theorem etcdModelOfServer_etcdReachedAt (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) :
    (etcdModelOfServer E γr on).etcdReachedAt = srvReachedAt γr on := rfl
theorem etcdModelOfServer_etcdRevToken (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) :
    (etcdModelOfServer E γr on).etcdRevToken = revTok E := rfl
theorem etcdModelOfServer_EtcdStep (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) :
    (etcdModelOfServer E γr on).EtcdStep = srvStep γr on := rfl

/-! ## What the server's answers give the clients' model -/

/-- **etcd has reached a witnessed revision** (unit W-M3; strict M1: the server's raft witness
`kvNx`, what a read's or a write's answer gives as `E.Nx log`, in place of mvcc's `certOk`): the
revisions of the KV model of a committed raft log are reached (`etcdReached`, the clients'
downward-closed form). -/
theorem etcdReached_of_nx (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) (log : Log) (r : w64)
    (h : sint.Z r < log.length) :
    srvApi.kvNx γr on log ⊢ etcdReached (EM := etcdModelOfServer E γr on) r := by
  iintro #H
  unfold etcdReached
  iright
  iexists r
  isplitr
  · ipureintro; exact Int.le_refl _
  imodintro
  rw [etcdModelOfServer_etcdReachedAt]
  unfold srvReachedAt srvApi.srvRevLbA
  iunfold srvApi.kvNx at H
  icases H with ⟨%A, #HA, %hA⟩
  obtain ⟨hA, -⟩ := hA
  iexists A
  iframe HA
  ipureintro; rw [hA]; exact h

/-- **A witnessed log is one of the server's history** (a read's: `E.Nx log`, with what its
receipt gives, `srvApi.logOk_of_receipt`, and the keys' bound, `srvKVCoreM_keys`). -/
theorem srvLog_of_nx (γr : ReadNames) (on : Bool) (log : Log) (hw : LogWf' log)
    (hl : log.length < 2 ^ 63) (hs : LogSmall log) (hk : mvcc.LogPutsLe etcdKeyMax log) :
    srvApi.kvNx (GF := GF) γr on log ⊢ srvLog γr on log := by
  iintro #H
  iunfold srvLog
  iexists log
  iframe H
  ipureintro; exact ⟨List.prefix_refl _, hw, hl, hs, hk⟩

/-- **A certified lower bound of the notified log is one of the server's history** (the watch
path's `histLb`, with `histLb_model.law`'s facts). -/
theorem srvLog_of_histLb (γr : ReadNames) (on : Bool) (γs : srvApi.KVSNames) (L : Log)
    (hl : L.length < 2 ^ 63) (hs : LogSmall L) (hk : mvcc.LogPutsLe etcdKeyMax L) :
    srvApi.histLb (GF := GF) γr on γs L ⊢ srvLog γr on L := by
  iintro #H
  iunfold srvApi.histLb at H
  icases H with ⟨-, %L', %hL', #Hx, -⟩
  iunfold srvLog
  iexists L'
  iframe Hx
  ipureintro; exact ⟨hL'.1, logWf'_of_prefix hL'.1 hL'.2, hl, hs, hk⟩

/-- **etcd's state at a witnessed revision**: the state at revision `r` of the KV model of a
committed raft log (well formed, small, its keys short), restricted to `pfx`, is etcd's state at
`r` (persistent), and well formed under `pfx`. -/
theorem etcdState_of_nx (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) (log : Log) (r : w64)
    (pfx : GoString) (h0 : 0 ≤ sint.Z r) (h : sint.Z r < log.length) (hw : LogWf' log)
    (hl : log.length < 2 ^ 63) (hs : LogSmall log) (hk : mvcc.LogPutsLe etcdKeyMax log) :
    srvApi.kvNx γr on log ⊢
      □ etcdState (self := etcdModelOfServer E γr on) r pfx
          (underPfx pfx (stateAt log (sint.Z r).toNat)) ∗
      ⌜EtcdStateWf pfx (underPfx pfx (stateAt log (sint.Z r).toNat))⌝ := by
  iintro #H
  ihave #Hl := srvLog_of_nx γr on log hw hl hs hk $$ H
  isplitl
  · imodintro
    rw [etcdModelOfServer_etcdState]
    unfold srvEtcdState
    iexists log
    iframe Hl
    ipureintro; exact ⟨h0, h, rfl⟩
  · ipureintro; exact underPfx_wf log _ pfx

/-- `etcdState_of_nx` at a log's last revision. -/
theorem etcdState_of_nx_last (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) (log : Log)
    (pfx : GoString) (h2 : 2 ≤ log.length) (h3 : log.length + 3 ≤ 2 ^ 63) (hw : LogWf' log)
    (hs : LogSmall log) (hk : mvcc.LogPutsLe etcdKeyMax log) :
    srvApi.kvNx γr on log ⊢
      □ etcdState (self := etcdModelOfServer E γr on) (W64 ((log.length : Int) - 1)) pfx
          (underPfx pfx (stateAfter log)) ∗
      ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ := by
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  have hst : stateAt log (sint.Z (W64 ((log.length : Int) - 1))).toNat = stateAfter log := by
    rw [hr, show ((log.length : Int) - 1).toNat = log.length - 1 by omega, stateAt_last]
  rw [← hst]
  exact etcdState_of_nx E γr on log _ pfx (by omega) (by omega) hw (by omega) hs hk

/-! ### A put's revision -/

/-- An applied outcome without the quota's `ErrNoSpace` passes through every layer of a chain:
it is the backend's. -/
theorem chainStep_applied_false : ∀ (c : apply.Chain) {rq : apply.IRRModel} {log l : Log},
    apply.chainStep apply.backendStep c rq log (.applied l false) →
      apply.backendStep rq log (.applied l false)
  | .backend, _, _, _, h => h
  | .corrupt c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · cases h
    · exact chainStep_applied_false c h
  | .capped c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · cases h
    · split at h
      · rcases h with h | h
        · cases h
        · exact chainStep_applied_false c h
      · exact chainStep_applied_false c h
  | .auth _ c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rcases h with ⟨-, h⟩ | h
      · cases h
      · exact chainStep_applied_false c h
    · exact chainStep_applied_false c h
  | .quota c, _, _, _, h => by
    simp only [apply.chainStep] at h
    exact chainStep_applied_false c h

/-- **A successful put appended a revision**: the request's application (applied, no
`ErrNoSpace`) appended one revision to the KV's log. -/
theorem put_appended (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV) (l : Log)
    (skip : Bool)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    ∃ cs, x'.log = x.log ++ [cs] := by
  have hk : apply.dispatchKind (apply.withHeader (irrPut o) hm) = .put := by
    simp [apply.dispatchKind, apply.withHeader, irrPut, apply.irrEmpty]
  obtain ⟨-, hd, hl, -⟩ := h
  rw [hl]
  unfold apply.dispatchStep at hd
  rw [hk] at hd
  simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, ↓reduceIte,
    false_or] at hd
  have hb := chainStep_applied_false x.chain hd
  unfold apply.backendStep at hb
  rw [hk] at hb
  obtain ⟨op, -, hb | hb | hb⟩ := hb
  · cases hb.2
  · cases hb.2.2
  · cases hb.2
    exact ⟨_, rfl⟩

end model

end v3rpc
end EtcdGrove
end Perennial
