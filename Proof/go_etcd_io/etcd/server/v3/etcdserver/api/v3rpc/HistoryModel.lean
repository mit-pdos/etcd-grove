/-
**The clients' model of etcd over the cluster's committed history** (W3a of
`notes/watch-cut-plan.md`, 2026-10-22; `notes/decisions.md` D32). Lean-first, no Rocq counterpart.

`etcdModelOfServer E` (`ClientModel.lean`) instantiates the clients' model with one server's
facts: its sealed and certified logs. A client of several members (a watch resumed at another
member after a cut, D32) cannot name the member in its contract. `etcdModelOfHistory γ γk`
instantiates the model with the cluster's history instead, at the raft names `γ` the members share
and the KV names `γk` they agree on (`c0`, `ch0`, `log0`, what the KV model reads):

* its logs (`histLog`) are prefixes of the KV models of committed raft prefixes (`srvRLogLb γ A`,
  `kvModel γk A`), well formed, fewer than `2 ^ 63` revisions, small. Two such logs are in prefix order by a
  plain entailment (`histLog_two`: `srvRLogLb_prefix`, `kvRaftOf_prefix`), which is all the laws
  need of logs: they are `ClientModel.lean`'s, with `srvLog_two` replaced;
* `etcdState`, `EtcdStep`: `srvEtcdState`'s and `srvStep`'s, over history logs;
* `etcdReachedAt r` (and `etcdReadAt r`, the same): the KV model of a committed raft prefix has
  revision `r` (no well-formedness: no law reads it);
* `etcdRevToken`: `False`. A revision's token is the apply thread's of one member (`revTok`), which
  no member-free contract can hand out; no watch result needs one.

**From a member's facts**: a member whose read names `γr` agree with `γ` and `γk` (`memberOf`)
turns its facts into the history's by plain entailments (strict M1, 2026-11-05: over the member's
raft witness, `srvApi.kvNx γr false`; mvcc's certificates and their invariant are gone): its logs
(`ClientModel`'s `srvLog`, prefixes of the models of committed raft logs) are history logs, which
are such prefixes too (`histLog_of_srv`); its steps are the history's (`histStep_of_srv`); its
reached revisions are (`histReached_of_srv`, `histReached_of_nx`), and its watched logs
(`histWL_of_srv`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVCertCmp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode mvcc txn go_etcd_io.etcd.server.v3.etcdserver

section model
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-! ## The predicates -/

/-- **A log of the history** (persistent): a prefix of the KV model of a committed raft prefix
(strict M1, 2026-11-05: a prefix, as `ClientModel`'s `srvLog`, whose witness is the server's
`kvNx` of an extension), well formed, of fewer than `2 ^ 63` revisions, small, (2026-10-30,
`notes/keylen.md`) its keys short. -/
def histLog (γ : ServerRaftNames) (γk : KVNames) (log : Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗
    ⌜log <+: kvModel γk A ∧ LogWf' log ∧ log.length < 2 ^ 63 ∧ LogSmall log ∧
      mvcc.LogPutsLe etcdKeyMax log⌝)

instance histLog_persistent (γ : ServerRaftNames) (γk : KVNames) (log : Log) :
    Persistent (histLog (GF := GF) γ γk log) := by
  unfold histLog; infer_instance

instance histLog_timeless (γ : ServerRaftNames) (γk : KVNames) (log : Log) :
    Timeless (histLog (GF := GF) γ γk log) := by
  unfold histLog; infer_instance

/-- **etcd's state at `rev` under `pfx`, in the history.** -/
def histEtcdState (γ : ServerRaftNames) (γk : KVNames) (rev : w64) (pfx : GoString)
    (s : List EtcdKv) : IProp GF :=
  iprop(∃ log : Log, histLog γ γk log ∗
    ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧
      s = underPfx pfx (stateAt log (sint.Z rev).toNat)⌝)

/-- **The history has reached `r`**: the KV model of a committed raft prefix has revision `r`. -/
def histReachedAt (γ : ServerRaftNames) (γk : KVNames) (r : w64) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γ A ∗ ⌜sint.Z r < (kvModel γk A).length⌝)

instance histReachedAt_persistent (γ : ServerRaftNames) (γk : KVNames) (r : w64) :
    Persistent (histReachedAt (GF := GF) γ γk r) := by
  unfold histReachedAt; infer_instance

instance histReachedAt_timeless (γ : ServerRaftNames) (γk : KVNames) (r : w64) :
    Timeless (histReachedAt (GF := GF) γ γk r) := by
  unfold histReachedAt; infer_instance

/-- **A step of the history**: `srvStep`'s, over a history log. -/
def histStep (γ : ServerRaftNames) (γk : KVNames) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : IProp GF :=
  iprop(∃ log : Log, histLog γ γk log ∗
    ⌜0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < log.length ∧
      (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → revEvs log pfx x = []) ∧
      revEvs log pfx (sint.Z r1).toNat = evs⌝)

instance histStep_persistent (γ : ServerRaftNames) (γk : KVNames) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : Persistent (histStep (GF := GF) γ γk r0 r1 pfx evs) := by
  unfold histStep; infer_instance

instance histStep_timeless (γ : ServerRaftNames) (γk : KVNames) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : Timeless (histStep (GF := GF) γ γk r0 r1 pfx evs) := by
  unfold histStep; infer_instance

/-! ## Two history logs -/

/-- **Two history logs are in prefix order** (`ClientModel`'s `srvLog_two`, for the history). -/
theorem histLog_two (γ : ServerRaftNames) (γk : KVNames) (L1 L2 : Log) :
    histLog (GF := GF) γ γk L1 ∗ histLog γ γk L2 ⊢
      ⌜∃ L, L1 <+: L ∧ L2 <+: L ∧ LogWf' L ∧ L.length < 2 ^ 63 ∧ LogSmall L ∧
        (L = L1 ∨ L = L2)⌝ := by
  unfold histLog
  iintro ⟨⟨%A1, #H1, %h1⟩, ⟨%A2, #H2, %h2⟩⟩
  ihave %Hp := srvRLogLb_prefix γ A1 A2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨e1, w1, l1, s1, -⟩ := h1
  obtain ⟨e2, w2, l2, s2, -⟩ := h2
  have hc : L1 <+: L2 ∨ L2 <+: L1 := by
    rcases Hp with h | h
    · exact List.prefix_or_prefix_of_prefix (e1.trans (kvRaftOf_prefix _ _ _ _ _ h)) e2
    · exact List.prefix_or_prefix_of_prefix e1 (e2.trans (kvRaftOf_prefix _ _ _ _ _ h))
  obtain ⟨L, p1, p2, hL⟩ := longer_log hc
  refine ⟨L, p1, p2, ?_⟩
  rcases hL with rfl | rfl
  · exact ⟨w1, l1, s1, Or.inl rfl⟩
  · exact ⟨w2, l2, s2, Or.inr rfl⟩

/-! ## The laws (`ClientModel.lean`'s, over history logs) -/

theorem histEtcdState_agree (γ : ServerRaftNames) (γk : KVNames) (rev : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    histEtcdState (GF := GF) γ γk rev pfx s ∗ histEtcdState γ γk rev pfx s' ⊢ ⌜s = s'⌝ := by
  unfold histEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]

theorem histEtcdState_revs (γ : ServerRaftNames) (γk : KVNames) (r : w64) (pfx : GoString)
    (s : List EtcdKv) :
    histEtcdState (GF := GF) γ γk r pfx s ⊢
      ⌜∀ v ∈ s, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
        sint.Z v.modRev ≤ sint.Z r ∧ 0 < sint.Z v.version⌝ := by
  unfold histEtcdState histLog
  iintro ⟨%L, ⟨%A, -, %HL⟩, %h⟩
  ipureintro
  obtain ⟨-, hw, hl, hs, -⟩ := HL
  obtain ⟨h0, hlt, rfl⟩ := h
  intro v hv
  have := stateAt_client_revs L hw hl hs (sint.Z r).toNat (by omega) v (mem_underPfx.1 hv).1
  rw [toNat_cast h0] at this
  exact this

/-- **Keys are short** (2026-10-30, `notes/keylen.md`): the history log's. -/
theorem histEtcdState_keys (γ : ServerRaftNames) (γk : KVNames) (r : w64) (pfx : GoString)
    (s : List EtcdKv) :
    histEtcdState (GF := GF) γ γk r pfx s ⊢ ⌜∀ v ∈ s, v.key.length ≤ etcdKeyMax⌝ := by
  unfold histEtcdState histLog
  iintro ⟨%L, ⟨%A, -, %HL⟩, %h⟩
  ipureintro
  obtain ⟨-, -, rfl⟩ := h
  intro v hv
  exact stateAt_keys HL.2.2.2.2 _ v (mem_underPfx.1 hv).1

theorem histEtcdState_vals (γ : ServerRaftNames) (γk : KVNames) (r : w64) (pfx : GoString)
    (s : List EtcdKv) :
    histEtcdState (GF := GF) γ γk r pfx s ⊢ ⌜∀ v ∈ s, v.value.length ≤ etcdKeyMax⌝ := by
  unfold histEtcdState histLog
  iintro ⟨%L, ⟨%A, -, %HL⟩, %h⟩
  ipureintro
  obtain ⟨-, -, rfl⟩ := h
  intro v hv
  exact stateAt_vals HL.2.2.2.2 _ v (mem_underPfx.1 hv).1

theorem histEtcdState_create_persist (γ : ServerRaftNames) (γk : KVNames) (r a : w64)
    (pfx : GoString) (s s' : List EtcdKv) :
    histEtcdState (GF := GF) γ γk r pfx s ∗ histEtcdState γ γk a pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.createRev ≤ sint.Z a → sint.Z a ≤ sint.Z r →
        ∃ v' ∈ s', v'.key = v.key ∧ v'.createRev = v.createRev⌝ := by
  unfold histEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
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

theorem histEtcdState_modrev_det (γ : ServerRaftNames) (γk : KVNames) (a b : w64)
    (pfx : GoString) (s s' : List EtcdKv) :
    histEtcdState (GF := GF) γ γk a pfx s ∗ histEtcdState γ γk b pfx s' ⊢
      ⌜∀ v ∈ s, ∀ v' ∈ s', v.key = v'.key → v.modRev = v'.modRev → v = v'⌝ := by
  unfold histEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  exact stateAtPfx_modrev_det L hlen _ _ (by have := p1.length_le; omega)
    (by have := p2.length_le; omega) pfx

theorem histEtcdState_modrev_persist (γ : ServerRaftNames) (γk : KVNames) (a b : w64)
    (pfx : GoString) (s s' : List EtcdKv) :
    histEtcdState (GF := GF) γ γk a pfx s ∗ histEtcdState γ γk b pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝ := by
  unfold histEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  intro v hv hm hba
  exact stateAtPfx_modrev_persist L hlen _ _ (by have := p1.length_le; omega) pfx v hv
    (by rw [toNat_cast h2a]; exact hm) (by omega)

theorem histStep_transfer (γ : ServerRaftNames) (γk : KVNames) (r0 a r1 : w64) (pfx : GoString)
    (s : List EtcdKv) (evs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    histStep (GF := GF) γ γk r0 r1 pfx evs ∗ histEtcdState γ γk a pfx s ⊢
      histEtcdState γ γk r1 pfx (applyEvsState s evs) := by
  unfold histStep histEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
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
theorem histStep_restrict (γ : ServerRaftNames) (γk : KVNames) (p a x b : w64) (pfx : GoString) (evs : List EtcdEv) :
    sint.Z p ≤ sint.Z a → sint.Z a < sint.Z x → (sint.Z x < sint.Z b ∨ (x = b ∧ evs = [])) →
    histStep (GF := GF) γ γk p b pfx evs ⊢ histStep (GF := GF) γ γk a x pfx [] := by
  intro hpa hax hxb
  unfold histStep
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

theorem histStep_compose (γ : ServerRaftNames) (γk : KVNames) (a b c : w64) (pfx : GoString)
    (evs : List EtcdEv) :
    histStep (GF := GF) γ γk a b pfx [] ∗ histStep γ γk b c pfx evs ⊢ histStep γ γk a c pfx evs := by
  unfold histStep
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
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

theorem histStep_delete_present (γ : ServerRaftNames) (γk : KVNames) (r0 a r1 : w64)
    (pfx : GoString) (s : List EtcdKv) (cs : List EtcdEv)
    (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    histStep (GF := GF) γ γk r0 r1 pfx cs ∗ histEtcdState γ γk a pfx s ⊢
      ⌜∀ (i : Nat) (c : EtcdEv), cs[i]? = some c → c.typ = W32 1 →
        ∃ v ∈ applyEvsState s (cs.take i), v.key = c.kv.key⌝ := by
  unfold histStep histEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := histLog_two γ γk L1 L2 $$ [$H1 $H2]
  iunfold histLog at H1
  icases H1 with ⟨%A1, -, %HL1⟩
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h10, h1a, h1b, h1q, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  have e2 : stateAt L2 (sint.Z a).toNat = stateAt L1 (sint.Z a).toNat := by
    rw [← stateAt_of_prefix p1 (r := (sint.Z a).toNat) (by omega),
      ← stateAt_of_prefix p2 (r := (sint.Z a).toNat) (by omega)]
  rw [e2]
  exact step_delete_present L1 HL1.2.1 pfx (sint.Z a).toNat (sint.Z r1).toNat (by omega)
    (by omega) (fun x hx1 hx2 => h1q x (by omega) (by omega))

/-! ## The instance -/

/-- **The history's instance of the clients' model of etcd** (see the file header). -/
@[instance_reducible]
def etcdModelOfHistory (γ : ServerRaftNames) (γk : KVNames) : EtcdModel GF where
  etcdState := histEtcdState γ γk
  etcdState_agree := histEtcdState_agree γ γk
  etcdState_revs := histEtcdState_revs γ γk
  etcdState_keys := histEtcdState_keys γ γk
  etcdState_vals := histEtcdState_vals γ γk
  etcdState_create_persist := histEtcdState_create_persist γ γk
  etcdState_modrev_det := histEtcdState_modrev_det γ γk
  etcdState_modrev_persist := histEtcdState_modrev_persist γ γk
  etcdReachedAt := histReachedAt γ γk
  etcdReachedAt_timeless := histReachedAt_timeless γ γk
  etcdReadAt := histReachedAt γ γk
  etcdReadAt_persistent := histReachedAt_persistent γ γk
  etcdReadAt_timeless := histReachedAt_timeless γ γk
  etcdRevToken _ := iprop(False)
  etcdRevToken_excl _ := by iintro ⟨H, -⟩; iexact H
  EtcdStep := histStep γ γk
  EtcdStep_persistent := histStep_persistent γ γk
  EtcdStep_timeless := histStep_timeless γ γk
  etcdStep_transfer := histStep_transfer γ γk
  etcdStep_compose := histStep_compose γ γk
  etcdStep_restrict := histStep_restrict γ γk
  etcdStep_delete_present := histStep_delete_present γ γk

theorem etcdModelOfHistory_etcdState (γ : ServerRaftNames) (γk : KVNames) :
    (etcdModelOfHistory (GF := GF) γ γk).etcdState = histEtcdState γ γk := rfl
theorem etcdModelOfHistory_etcdReachedAt (γ : ServerRaftNames) (γk : KVNames) :
    (etcdModelOfHistory (GF := GF) γ γk).etcdReachedAt = histReachedAt γ γk := rfl
theorem etcdModelOfHistory_EtcdStep (γ : ServerRaftNames) (γk : KVNames) :
    (etcdModelOfHistory (GF := GF) γ γk).EtcdStep = histStep γ γk := rfl

/-! ## From a member's facts -/

variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A member's KV names agree with the history's** on what the model reads, and its raft names
are the history's but for the storage registry (2026-10-27, the server port: `SrvRaft.reg` is the
member's own `MemoryStorage` registry, which the history does not read; until then the raft names
were the history's). -/
def memberOf (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames) : Prop :=
  { γr.raft with raft := { γr.raft.raft with reg := γ.raft.reg } } = γ ∧
    γr.kv.c0 = γk.c0 ∧ γr.kv.ch0 = γk.ch0 ∧ γr.kv.log0 = γk.log0

/-- A member whose raft names are the history's is one. -/
theorem memberOf_of_eq (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames) (hr : γr.raft = γ)
    (hc0 : γr.kv.c0 = γk.c0) (hch : γr.kv.ch0 = γk.ch0) (hlog : γr.kv.log0 = γk.log0) :
    memberOf γ γk γr := ⟨by subst hr; rfl, hc0, hch, hlog⟩

/-- The committed log's lower bounds do not read the storage registry. -/
theorem srvRLogLb_reg (γ : ServerRaftNames) (r : GName) (A : List EntryModel) :
    srvRLogLb (GF := GF) γ A ⊢ srvRLogLb { γ with raft := { γ.raft with reg := r } } A :=
  BI.entails_refl

/-- **A member's log is a history log** (strict M1, 2026-11-05: `ClientModel`'s `srvLog` at the
mode off, a prefix of the model of a committed raft log by the member's witness; no update: mvcc's
certificates' invariant is gone, and with it the short logs' case). -/
theorem histLog_of_srv (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (hm : memberOf γ γk γr) (log : Log) :
    srvLog (GF := GF) γr false log ⊢ histLog γ γk log := by
  obtain ⟨hr, hc0, hch, hlog⟩ := hm
  iintro #Hl
  iunfold srvLog at Hl
  icases Hl with ⟨%L', #Hx, %h⟩
  iunfold srvApi.kvNx at Hx
  icases Hx with ⟨%A, #HA, %hA⟩
  obtain ⟨hA, -⟩ := hA
  iunfold histLog
  iexists A
  rw [← hr]
  ihave #HA' := srvRLogLb_reg γr.raft γ.raft.reg A $$ HA
  iframe HA'
  ipureintro
  obtain ⟨hp, hw, hl, hs, hk⟩ := h
  refine ⟨?_, hw, hl, hs, hk⟩
  rw [← kvModel_congr γk γr.kv hc0 hch hlog]
  rw [kvModelM_false] at hA
  rw [hA]; exact hp

/-- **A member's step is the history's.** -/
theorem histStep_of_srv (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (hm : memberOf γ γk γr) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) :
    srvStep (GF := GF) γr false r0 r1 pfx evs ⊢ histStep γ γk r0 r1 pfx evs := by
  iintro #Hs
  iunfold srvStep at Hs
  icases Hs with ⟨%log, #Hl, %h⟩
  ihave #Hh := histLog_of_srv γ γk γr hm log $$ Hl
  iunfold histStep
  iexists log
  iframe Hh
  ipureintro; exact h

/-- **A member's reached revision is the history's.** -/
theorem histReached_of_srv (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (hm : memberOf γ γk γr) (r : w64) :
    srvReachedAt (GF := GF) γr false r ⊢ histReachedAt γ γk r := by
  obtain ⟨hr, hc0, hch, hlog⟩ := hm
  iintro H
  unfold srvReachedAt srvApi.srvRevLbA
  icases H with ⟨%A, #HA, %hA⟩
  iunfold histReachedAt
  iexists A
  rw [← hr]
  ihave #HA' := srvRLogLb_reg γr.raft γ.raft.reg A $$ HA
  iframe HA'
  ipureintro
  rw [← kvModel_congr γk γr.kv hc0 hch hlog]
  rw [kvModelM_false] at hA; exact hA

/-- **A member's witnessed revision is the history's**: a revision of the KV model of a
committed raft log (the member's witness `kvNx`, a read's or a write's `E.Nx log`) is reached in
the history. -/
theorem histReached_of_nx (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (hm : memberOf γ γk γr) (log : Log) (r : w64) (h : sint.Z r < log.length) :
    srvApi.kvNx (GF := GF) γr false log ⊢ etcdReached (EM := etcdModelOfHistory γ γk) r := by
  iintro #Hx
  unfold etcdReached
  iright
  iexists r
  isplitr
  · ipureintro; exact Int.le_refl _
  imodintro
  rw [etcdModelOfHistory_etcdReachedAt]
  iapply histReached_of_srv γ γk γr hm r
  unfold srvReachedAt srvApi.srvRevLbA
  iunfold srvApi.kvNx at Hx
  icases Hx with ⟨%A, #HA, %hA⟩
  obtain ⟨hA, -⟩ := hA
  iexists A
  iframe HA
  ipureintro; rw [hA]; exact h

/-! ## The watched logs of a client of the cluster (W4c) -/

/-- **A watched log of the history** (persistent; W4c of `notes/watch-cut-plan.md`): a prefix of
a history log. A member watches logs of at most two revisions (the start log's prefixes) that no
committed raft prefix models exactly; the prefixes of history logs take them in. -/
def histWL (γ : ServerRaftNames) (γk : KVNames) (L : Log) : IProp GF :=
  iprop(∃ L' : Log, histLog γ γk L' ∗ ⌜L <+: L'⌝)

instance histWL_persistent (γ : ServerRaftNames) (γk : KVNames) (L : Log) :
    Persistent (histWL (GF := GF) γ γk L) := by
  unfold histWL; infer_instance

/-- A watched log's revisions are reached. -/
theorem histWL_reached (γ : ServerRaftNames) (γk : KVNames) (L : Log) (r : w64)
    (h : sint.Z r < L.length) :
    histWL (GF := GF) γ γk L ⊢ etcdReached (EM := etcdModelOfHistory γ γk) r := by
  iintro #H
  iunfold histWL at H
  icases H with ⟨%L', #HL, %hp⟩
  unfold etcdReached
  by_cases hle : sint.Z r ≤ 0
  · ileft; ipureintro; exact hle
  iright
  iexists r
  isplitr
  · ipureintro; exact Int.le_refl _
  imodintro
  rw [etcdModelOfHistory_etcdReachedAt]
  iunfold histLog at HL
  icases HL with ⟨%A, #HA, %hA⟩
  iunfold histReachedAt
  iexists A
  iframe HA
  ipureintro
  have := hp.length_le
  have := hA.1.length_le
  omega

/-- A watched log's states are the history's. -/
theorem histWL_state (γ : ServerRaftNames) (γk : KVNames) (L : Log) (r : w64) (pfx : GoString)
    (h : 0 ≤ sint.Z r ∧ sint.Z r < L.length) :
    histWL (GF := GF) γ γk L ⊢
      histEtcdState γ γk r pfx (underPfx pfx (stateAt L (sint.Z r).toNat)) := by
  iintro #H
  iunfold histWL at H
  icases H with ⟨%L', #HL, %hp⟩
  iunfold histEtcdState
  iexists L'
  iframe HL
  ipureintro
  have := hp.length_le
  refine ⟨h.1, by omega, ?_⟩
  rw [stateAt_of_prefix hp (by omega)]

/-- A watched log's steps are the history's. -/
theorem histWL_step (γ : ServerRaftNames) (γk : KVNames) (L : Log) (r0 r1 : w64)
    (pfx : GoString) (evs : List EtcdEv)
    (h : 0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < L.length ∧
      (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → revEvs L pfx x = []) ∧
      revEvs L pfx (sint.Z r1).toNat = evs) :
    histWL (GF := GF) γ γk L ⊢ histStep γ γk r0 r1 pfx evs := by
  iintro #H
  iunfold histWL at H
  icases H with ⟨%L', #HL, %hp⟩
  iunfold histStep
  iexists L'
  iframe HL
  ipureintro
  obtain ⟨h0, h01, h1, hmid, hevs⟩ := h
  have := hp.length_le
  refine ⟨h0, h01, by omega, fun x hx0 hx1 => ?_, ?_⟩
  · rw [revEvs_prefix hp (by omega)]; exact hmid x hx0 hx1
  · rw [revEvs_prefix hp (by omega)]; exact hevs

/-- The start log `[[], []]` is well formed and small. -/
theorem startLog_ok : LogWf' ([[], []] : Log) ∧ ([[], []] : Log).length < 2 ^ 63 ∧
    LogSmall ([[], []] : Log) := by
  refine ⟨⟨fun _ => rfl, fun r cs i k hr hi => ?_⟩, by decide, ?_⟩
  · have hcs : cs = [] := by
      rcases r with _ | _ | r <;> simp_all
    subst hcs; simp at hi
  · unfold LogSmall; decide

/-- **A member's watched log is the history's** (W4c; strict M1: a member's log, `srvLog`, is a
history log, `histLog_of_srv`). -/
theorem histWL_of_srv (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (hm : memberOf γ γk γr) (L : Log) :
    srvLog (GF := GF) γr false L ⊢ histWL γ γk L := by
  iintro #Hl
  ihave #Hh := histLog_of_srv γ γk γr hm L $$ Hl
  iunfold histWL
  iexists L
  iframe Hh
  ipureintro; exact List.prefix_refl L

end model

end v3rpc
end EtcdGrove
end Perennial
