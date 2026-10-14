/-
**The clients' model of etcd, implemented by the server** (the vertical slice's unit V1,
2026-10-13; `notes/STATUS.md`, "The vertical slice: client to server"; `notes/decisions.md`, "The
client's model as a class the server instantiates; the wire as the handler's theorem
transported"). Lean-first, no Rocq counterpart.

The clients (the cache, `client/v3/concurrency`, `client/v3/leasing`, the recipes) state their
results over `EtcdModel GF` (`cache/v3/EtcdModel.lean`): four predicates and their laws, fourteen
axioms until V1. `etcdModelOfServer E` instantiates it with the server's facts, for the server
whose apply thread's environment is `E` (the store's ghost names `E.γ`, the revisions' tokens
`E.γrev`):

* `etcdState rev pfx s` (`srvEtcdState`): some certified log (`idxCert`, mvcc's lower bound of the
  committed log), small (`LogSmall`, the read path's `storeSmall`), has revision `rev`, and its
  state at `rev` restricted to `pfx` is `s` (`underPfx pfx (stateAt log rev)`). The server's
  revision of a log is its last index: a read at a log answers `log.length - 1`.
* `etcdReachedAt r` (`srvReachedAt`): some certified log has revision `r`.
* `etcdRevToken r` (`revTok E r`, `InvRequest.lean`): the token the apply thread minted when the
  KV's log grew to revision `r` (`revAuth_step`), carried by the entry's result to the proposer.
* `EtcdStep r0 r1 pfx evs` (`srvStep`): some certified small log has revision `r1`, no event under
  `pfx` strictly between `r0` and `r1` (`txn.revEvs`: the client's events of a revision's
  changes under the prefix), and `evs` are `r1`'s.

Every law is a theorem (`txn/HistoryLaws.lean`, unit 4 of the txn package, and
`txn/ClientLaws.lean`); `#print axioms etcdModelOfServer` lists none of the clients' former
axioms (`Results.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode mvcc txn

/-! ## Pure lemmas: two certified logs -/

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

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-! ## The predicates -/

/-- **A certified small log**: mvcc's certificate of `log` (a lower bound of the committed log)
and `LogSmall` (at most `2 ^ 62` changes: the read path's `storeSmall`). -/
def srvLog (E : apply.AEnv GF) (log : Log) : IProp GF :=
  iprop(idxCert E.γ.idx log ∗ ⌜LogSmall log⌝)

instance srvLog_persistent (E : apply.AEnv GF) (log : Log) : Persistent (srvLog E log) := by
  unfold srvLog; infer_instance

instance srvLog_timeless (E : apply.AEnv GF) (log : Log) : Timeless (srvLog E log) := by
  unfold srvLog; infer_instance

/-- **etcd's state at `rev` under `pfx`, on the server**: a certified small log has revision
`rev`, and `s` is its state at `rev` restricted to `pfx`. -/
def srvEtcdState (E : apply.AEnv GF) (rev : w64) (pfx : GoString) (s : List EtcdKv) : IProp GF :=
  iprop(∃ log : Log, srvLog E log ∗
    ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length ∧
      s = underPfx pfx (stateAt log (sint.Z rev).toNat)⌝)

instance srvEtcdState_persistent (E : apply.AEnv GF) (rev : w64) (pfx : GoString)
    (s : List EtcdKv) : Persistent (srvEtcdState E rev pfx s) := by
  unfold srvEtcdState; infer_instance

/-- **etcd has reached `r`, on the server**: a certified log has revision `r`. -/
def srvReachedAt (E : apply.AEnv GF) (r : w64) : IProp GF :=
  iprop(∃ log : Log, idxCert E.γ.idx log ∗ ⌜sint.Z r < log.length⌝)

instance srvReachedAt_persistent (E : apply.AEnv GF) (r : w64) :
    Persistent (srvReachedAt E r) := by
  unfold srvReachedAt; infer_instance

instance srvReachedAt_timeless (E : apply.AEnv GF) (r : w64) : Timeless (srvReachedAt E r) := by
  unfold srvReachedAt; infer_instance

/-- **A step of etcd's history, on the server**: a certified small log has revision `r1` (above
`r0 ≥ 0`), no
event under `pfx` at a revision strictly between `r0` and `r1`, and `evs` are the events under
`pfx` at `r1`. -/
def srvStep (E : apply.AEnv GF) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) : IProp GF :=
  iprop(∃ log : Log, srvLog E log ∗
    ⌜0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < log.length ∧
      (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → revEvs log pfx x = []) ∧
      revEvs log pfx (sint.Z r1).toNat = evs⌝)

instance srvStep_persistent (E : apply.AEnv GF) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : Persistent (srvStep E r0 r1 pfx evs) := by
  unfold srvStep; infer_instance

instance srvStep_timeless (E : apply.AEnv GF) (r0 r1 : w64) (pfx : GoString)
    (evs : List EtcdEv) : Timeless (srvStep E r0 r1 pfx evs) := by
  unfold srvStep; infer_instance

/-! ## The certificates' pure facts -/

theorem idxCert_pure (γ : IdxNames) (log : Log) :
    idxCert (GF := GF) γ log ⊢ ⌜LogWf' log ∧ log.length < 2 ^ 63⌝ := by
  unfold idxCert
  iintro ⟨-, -, %H, -⟩
  ipureintro; exact ⟨H.1, H.2.1⟩

theorem srvLog_two (E : apply.AEnv GF) (L1 L2 : Log) :
    srvLog E L1 ∗ srvLog E L2 ⊢
      ⌜∃ L, L1 <+: L ∧ L2 <+: L ∧ LogWf' L ∧ L.length < 2 ^ 63 ∧ LogSmall L ∧
        (L = L1 ∨ L = L2)⌝ := by
  unfold srvLog
  iintro ⟨⟨#H1, %Hs1⟩, ⟨#H2, %Hs2⟩⟩
  ihave %Hp := idxCert_prefix E.γ.idx L1 L2 $$ [$H1 $H2]
  ihave %Hw1 := idxCert_pure E.γ.idx L1 $$ H1
  ihave %Hw2 := idxCert_pure E.γ.idx L2 $$ H2
  ipureintro
  obtain ⟨L, h1, h2, hL⟩ := longer_log Hp
  refine ⟨L, h1, h2, ?_⟩
  rcases hL with rfl | rfl
  · exact ⟨Hw1.1, Hw1.2, Hs1, Or.inl rfl⟩
  · exact ⟨Hw2.1, Hw2.2, Hs2, Or.inr rfl⟩

/-! ## The laws -/

theorem srvEtcdState_agree (E : apply.AEnv GF) (rev : w64) (pfx : GoString) (s s' : List EtcdKv) :
    srvEtcdState E rev pfx s ∗ srvEtcdState E rev pfx s' ⊢ ⌜s = s'⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two E L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]

theorem srvEtcdState_revs (E : apply.AEnv GF) (r : w64) (pfx : GoString) (s : List EtcdKv) :
    srvEtcdState E r pfx s ⊢
      ⌜∀ v ∈ s, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
        sint.Z v.modRev ≤ sint.Z r ∧ 0 < sint.Z v.version⌝ := by
  unfold srvEtcdState srvLog
  iintro ⟨%L, ⟨#H, %Hs⟩, %h⟩
  ihave %Hw := idxCert_pure E.γ.idx L $$ H
  ipureintro
  obtain ⟨h0, hl, rfl⟩ := h
  intro v hv
  have := stateAt_client_revs L Hw.1 Hw.2 Hs (sint.Z r).toNat (by omega) v (mem_underPfx.1 hv).1
  rw [toNat_cast h0] at this
  exact this

theorem srvEtcdState_create_persist (E : apply.AEnv GF) (r a : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    srvEtcdState E r pfx s ∗ srvEtcdState E a pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.createRev ≤ sint.Z a → sint.Z a ≤ sint.Z r →
        ∃ v' ∈ s', v'.key = v.key ∧ v'.createRev = v.createRev⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two E L1 L2 $$ [$H1 $H2]
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

theorem srvEtcdState_modrev_det (E : apply.AEnv GF) (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    srvEtcdState E a pfx s ∗ srvEtcdState E b pfx s' ⊢
      ⌜∀ v ∈ s, ∀ v' ∈ s', v.key = v'.key → v.modRev = v'.modRev → v = v'⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two E L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  exact stateAtPfx_modrev_det L hlen _ _ (by have := p1.length_le; omega)
    (by have := p2.length_le; omega) pfx

theorem srvEtcdState_modrev_persist (E : apply.AEnv GF) (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
    srvEtcdState E a pfx s ∗ srvEtcdState E b pfx s' ⊢
      ⌜∀ v ∈ s, sint.Z v.modRev ≤ sint.Z b → sint.Z b ≤ sint.Z a → v ∈ s'⌝ := by
  unfold srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two E L1 L2 $$ [$H1 $H2]
  ipureintro
  obtain ⟨L, p1, p2, -, hlen, -, -⟩ := Hl
  obtain ⟨h1a, h1b, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  rw [← stateAt_of_prefix p1 (r := _) (by omega), ← stateAt_of_prefix p2 (r := _) (by omega)]
  intro v hv hm hba
  exact stateAtPfx_modrev_persist L hlen _ _ (by have := p1.length_le; omega) pfx v hv
    (by rw [toNat_cast h2a]; exact hm) (by omega)

theorem srvStep_transfer (E : apply.AEnv GF) (r0 a r1 : w64) (pfx : GoString) (s : List EtcdKv)
    (evs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    srvStep E r0 r1 pfx evs ∗ srvEtcdState E a pfx s ⊢
      srvEtcdState E r1 pfx (applyEvsState s evs) := by
  unfold srvStep srvEtcdState
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two E L1 L2 $$ [$H1 $H2]
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

theorem srvStep_compose (E : apply.AEnv GF) (a b c : w64) (pfx : GoString) (evs : List EtcdEv) :
    srvStep E a b pfx [] ∗ srvStep E b c pfx evs ⊢ srvStep E a c pfx evs := by
  unfold srvStep
  iintro ⟨⟨%L1, #H1, %h1⟩, ⟨%L2, #H2, %h2⟩⟩
  ihave %Hl := srvLog_two E L1 L2 $$ [$H1 $H2]
  obtain ⟨L, p1, p2, -, -, -, hL⟩ := Hl
  obtain ⟨h10, h1a, h1b, h1q, h1e⟩ := h1
  obtain ⟨h20, h2a, h2b, h2q, h2e⟩ := h2
  iexists L
  isplitl
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

theorem srvStep_delete_present (E : apply.AEnv GF) (r0 a r1 : w64) (pfx : GoString)
    (s : List EtcdKv) (cs : List EtcdEv) (h : sint.Z r0 ≤ sint.Z a ∧ sint.Z a < sint.Z r1) :
    srvStep E r0 r1 pfx cs ∗ srvEtcdState E a pfx s ⊢
      ⌜∀ (i : Nat) (c : EtcdEv), cs[i]? = some c → c.typ = W32 1 →
        ∃ v ∈ applyEvsState s (cs.take i), v.key = c.kv.key⌝ := by
  unfold srvStep srvEtcdState srvLog
  iintro ⟨⟨%L1, ⟨#H1, %Hs1⟩, %h1⟩, ⟨%L2, ⟨#H2, %Hs2⟩, %h2⟩⟩
  ihave %Hp := idxCert_prefix E.γ.idx L1 L2 $$ [$H1 $H2]
  ihave %Hw := idxCert_pure E.γ.idx L1 $$ H1
  ipureintro
  obtain ⟨L, p1, p2, -⟩ := longer_log Hp
  obtain ⟨h10, h1a, h1b, h1q, rfl⟩ := h1
  obtain ⟨h2a, h2b, rfl⟩ := h2
  have e2 : stateAt L2 (sint.Z a).toNat = stateAt L1 (sint.Z a).toNat := by
    rw [← stateAt_of_prefix p1 (r := (sint.Z a).toNat) (by omega),
      ← stateAt_of_prefix p2 (r := (sint.Z a).toNat) (by omega)]
  rw [e2]
  exact step_delete_present L1 Hw.1 pfx (sint.Z a).toNat (sint.Z r1).toNat (by omega) (by omega)
    (fun x hx1 hx2 => h1q x (by omega) (by omega))

/-! ## The instance -/

/-- **The server's instance of the clients' model of etcd** (see the file header): every field
the server's fact, every law a theorem. A `def`, applied where the slice is stated. -/
@[instance_reducible]
def etcdModelOfServer (E : apply.AEnv GF) : EtcdModel GF where
  etcdState := srvEtcdState E
  etcdState_agree := srvEtcdState_agree E
  etcdState_revs := srvEtcdState_revs E
  etcdState_create_persist := srvEtcdState_create_persist E
  etcdState_modrev_det := srvEtcdState_modrev_det E
  etcdState_modrev_persist := srvEtcdState_modrev_persist E
  etcdReachedAt := srvReachedAt E
  etcdReachedAt_timeless := srvReachedAt_timeless E
  etcdRevToken := revTok E
  etcdRevToken_excl := revTok_excl E
  EtcdStep := srvStep E
  EtcdStep_persistent := srvStep_persistent E
  EtcdStep_timeless := srvStep_timeless E
  etcdStep_transfer := srvStep_transfer E
  etcdStep_compose := srvStep_compose E
  etcdStep_delete_present := srvStep_delete_present E

theorem etcdModelOfServer_etcdState (E : apply.AEnv GF) :
    (etcdModelOfServer E).etcdState = srvEtcdState E := rfl
theorem etcdModelOfServer_etcdReachedAt (E : apply.AEnv GF) :
    (etcdModelOfServer E).etcdReachedAt = srvReachedAt E := rfl
theorem etcdModelOfServer_etcdRevToken (E : apply.AEnv GF) :
    (etcdModelOfServer E).etcdRevToken = revTok E := rfl
theorem etcdModelOfServer_EtcdStep (E : apply.AEnv GF) :
    (etcdModelOfServer E).EtcdStep = srvStep E := rfl

/-! ## What the server's answers give the clients' model -/

/-- **etcd has reached a certified revision**: a certified log's revisions are reached
(`etcdReached`, the clients' downward-closed form). -/
theorem etcdReached_of_cert (E : apply.AEnv GF) (log : Log) (r : w64)
    (h : sint.Z r < log.length) :
    idxCert E.γ.idx log ⊢ etcdReached (EM := etcdModelOfServer E) r := by
  iintro #H
  unfold etcdReached
  iright
  iexists r
  isplitr
  · ipureintro; exact Int.le_refl _
  imodintro
  rw [etcdModelOfServer_etcdReachedAt]
  unfold srvReachedAt
  iexists log
  iframe H
  ipureintro; exact h

/-- **etcd's state at a certified revision**, with the store's size premise (`storeSmall`, the
read path's): the state at revision `r` of a certified log, restricted to `pfx`, is etcd's
state at `r` (persistent), and well formed under `pfx`. -/
theorem etcdState_of_cert (E : apply.AEnv GF) (log : Log) (r : w64) (pfx : GoString)
    (h0 : 0 ≤ sint.Z r) (h : sint.Z r < log.length) :
    storeSmall E.γ ∗ idxCert E.γ.idx log ⊢
      □ etcdState (self := etcdModelOfServer E) r pfx (underPfx pfx (stateAt log (sint.Z r).toNat)) ∗
      ⌜EtcdStateWf pfx (underPfx pfx (stateAt log (sint.Z r).toNat))⌝ := by
  iintro ⟨#Hsm, #H⟩
  iunfold storeSmall at Hsm
  ihave %Hs := Hsm $$ %log H
  isplitl
  · imodintro
    rw [etcdModelOfServer_etcdState]
    unfold srvEtcdState srvLog
    iexists log
    isplitl
    · iframe H; ipureintro; exact Hs
    ipureintro; exact ⟨h0, h, rfl⟩
  · ipureintro; exact underPfx_wf log _ pfx

/-- `etcdState_of_cert` at a log's last revision. -/
theorem etcdState_of_cert_last (E : apply.AEnv GF) (log : Log) (pfx : GoString)
    (h2 : 2 ≤ log.length) (h3 : log.length + 3 ≤ 2 ^ 63) :
    storeSmall E.γ ∗ idxCert E.γ.idx log ⊢
      □ etcdState (self := etcdModelOfServer E) (W64 ((log.length : Int) - 1)) pfx
          (underPfx pfx (stateAfter log)) ∗
      ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ := by
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  have hst : stateAt log (sint.Z (W64 ((log.length : Int) - 1))).toNat = stateAfter log := by
    rw [hr, show ((log.length : Int) - 1).toNat = log.length - 1 by omega, stateAt_last]
  rw [← hst]
  exact etcdState_of_cert E log _ pfx (by omega) (by omega)

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
  | .auth c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · rcases h with h | h
      · cases h
      · exact chainStep_applied_false c h
    · exact chainStep_applied_false c h
  | .quota c, _, _, _, h => by
    simp only [apply.chainStep] at h
    split at h
    · obtain ⟨o', h1, h2 | ⟨l', -, h2⟩⟩ := h
      · subst h2; exact chainStep_applied_false c h1
      · cases h2
    · exact chainStep_applied_false c h

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
  · cases hb
    exact ⟨_, rfl⟩

end model

end v3rpc
end EtcdGrove
end Perennial
