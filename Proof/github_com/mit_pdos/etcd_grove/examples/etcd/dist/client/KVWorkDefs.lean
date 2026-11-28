/- Lean-first (no Rocq counterpart).

# The putget and durable workloads of `examples/etcd/dist/client`: their vocabulary (#50 N9a)

`notes/etcd-dist-plan.md` §23. Both run on their orchestrator machine against every member's client endpoint,
over the clientv3 specs `kv.Put.spec`/`kv.Get.spec`, at the cluster's view `Γ`, and each
owns its key prefix of the cluster's KV (`etcd_dist.kvPfx`, `KVPfxDist.lean`): putget `pg/`, durable `du/`.

**putget** (`RunPutGet`, compacted's check in rounds): round `i` puts `pg/k<i>` with `v<i>` and gets it.
Its invariant (`pgInv γ γP`, namespace `kvClientN.@"pg"`) keeps the prefix's key-values (the owner's half
of `pfxView pg/`) with: every key-value's value is its key's (`pgVal`: `"v"` and the key after `pg/k`), and
every key of the list `P` (a monotone list at `γP`: the keys whose put fired) has a key-value. A put's update
appends its key (`pgPutAu`, result `pgFired γP k`); a get's read update after it (`pgGetAu`) gives the key a
key-value, each of value `pgVal k` (`pgReadOk`). Rounds whose put failed may fire later: their key-values have
their keys' values, so nothing they do breaks a later round's check. This is `client.putGetInv`'s argument
(the single-process putget's), per key and under the prefix.

**durable** (`RunDurable`, restartN's check): `n ≤ 256` puts of `durKey j ↦ durVal j` (`du/` `k` and the
byte `j`; `v` and `j`), then one linearizable range of `du/`. Its invariant (`durInv γ γF γs n`, namespace
`kvClientN.@"du"`) keeps the prefix's key-values with: each is `durKey j ↦ durVal j` at version `1` for some
`j` of the fired list `F` (monotone at `γF`), `j < n`, and each `j ∈ F` has its key-value. Put `j` fires at
most once (`kv.Put.spec`'s one-shot update): its update holds the token `γs[j]`, which it gives to the
invariant when it fires (`durPutAu`), so the key is absent before (version `1`); its result is
`durFired γF j`. The range's read update (`durGetAu`) gives the state's `du/` key-values those facts
(`durReadOk`) and, for each fired put the caller knows of, its key-value. This is restart1's `r1Ok` argument
(keys distinct, values at version `1`) under the prefix, with unknown outcomes.

**Shares** (what the start supplies; global, at `[GooseGlobalGS]`): `putgetShare eps`, `durableShare eps`:
some view `Γ` with auth off, every endpoint serving a member of it (`membersAt`), the prefix owned at some
`γ` (`kvPfx`), and the owner's half at `[]`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPfxDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange
public import Proof.go_etcd_io.etcd.client.v3.KeyOps
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist

/-! ## Pure part -/

section pure
variable [GooseExts]

/-- putget's prefix (`putgetPrefix`). -/
abbrev putgetPfx : GoString := go!"pg/"

/-- **putget's value of a key**: `"v"` followed by what follows `pg/k` (round `i`'s key `pg/k<i>`, value
`v<i>`). -/
def pgVal (k : GoString) : GoString := go!"v" ++ k.drop 4

theorem pgVal_key (s : GoString) : pgVal (go!"pg/k" ++ s) = go!"v" ++ s := by
  unfold pgVal
  rw [show (4 : Nat) = (go!"pg/k").length from rfl, List.drop_left]

theorem putgetPfx_key (s : GoString) : putgetPfx <+: go!"pg/k" ++ s :=
  ⟨go!"k" ++ s, rfl⟩

/-- putget's invariant's facts about the prefix's key-values `v` and the fired keys `P`. -/
def PgOk (P : List GoString) (v : List EtcdKv) : Prop :=
  (∀ x ∈ v, x.value = pgVal x.key) ∧ (∀ k ∈ P, ∃ x ∈ v, x.key = k)

/-- What a get of `k` after its put fired reads: `k` has a key-value, each of `k`'s has `pgVal k`. -/
def pgReadOk (k : GoString) (σ : KVState) : Prop :=
  (∀ x ∈ σ.kvs, x.key = k → x.value = pgVal k) ∧ ∃ x ∈ σ.kvs, x.key = k

theorem pgOk_nil : PgOk [] [] := ⟨by simp, by simp⟩

/-- A put of `k ↦ pgVal k` (under `pg/`) keeps the facts, `k` fired. -/
theorem pgOk_put {P : List GoString} {σ : KVState} {k : GoString} (hk : putgetPfx <+: k)
    (h : PgOk P (pfxView putgetPfx σ)) :
    PgOk (P ++ [k]) (pfxView putgetPfx (kvOpStep (.put (putKeyOp k (pgVal k))) σ)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases mem_pfxView_put hx with rfl | hx
    · rw [putKvNew_value, putKvNew_key]
    · exact h1 x hx
  · intro k' hk'
    rcases List.mem_append.1 hk' with hk' | hk'
    · obtain ⟨x, hx, hxk⟩ := h2 k' hk'
      by_cases hxk' : x.key = k
      · exact ⟨_, pfxView_put_new σ hk, by rw [putKvNew_key, ← hxk, hxk']⟩
      · exact ⟨x, pfxView_put_keep hx hxk', hxk⟩
    · have : k' = k := by simpa using hk'
      subst this
      exact ⟨_, pfxView_put_new σ hk, putKvNew_key _ _ _ _ _⟩

theorem pgReadOk_of {P : List GoString} {σ : KVState} {k : GoString} (hk : putgetPfx <+: k)
    (h : PgOk P (pfxView putgetPfx σ)) (hkP : k ∈ P) : pgReadOk k σ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx hxk
    have hx' : x ∈ pfxView putgetPfx σ := mem_pfxView_of hx (by rw [hxk]; exact hk)
    rw [h1 x hx', hxk]
  · obtain ⟨x, hx, hxk⟩ := h2 k hkP
    exact ⟨x, (mem_of_mem_pfxView hx).1, hxk⟩

/-- **The get's answer** (`srvRangeOk_getKey`'s selection): a first key-value, of value `pgVal k`. -/
theorem pgReadOk_head {k : GoString} {σ : KVState} (h : pgReadOk k σ) :
    ∃ kv0, (σ.kvs.filter (fun v => decide (v.key = k)))[0]? = some kv0 ∧ kv0.value = pgVal k := by
  obtain ⟨h1, x, hx, hxk⟩ := h
  have hne : σ.kvs.filter (fun v => decide (v.key = k)) ≠ [] := by
    intro he
    have : x ∈ σ.kvs.filter (fun v => decide (v.key = k)) := List.mem_filter.2 ⟨hx, by simp [hxk]⟩
    rw [he] at this
    simp at this
  obtain ⟨kv0, rest, hkv⟩ := List.exists_cons_of_ne_nil hne
  have hm : kv0 ∈ σ.kvs.filter (fun v => decide (v.key = k)) := by rw [hkv]; simp
  obtain ⟨hm1, hm2⟩ := List.mem_filter.1 hm
  refine ⟨kv0, by rw [hkv]; rfl, h1 kv0 hm1 (by simpa using hm2)⟩

/-- Round `i`'s put and get fit a gRPC message (`s` is `strconv.Itoa(i)`). -/
theorem pg_sizes (s : GoString) (hs : s.length ≤ 66) :
    opSizeOk (opPutModel (go!"pg/k" ++ s) (go!"v" ++ s) []) ∧ opSizeOk (opGetModel (go!"pg/k" ++ s) []) := by
  have h1 : (go!"pg/k" ++ s).length ≤ 70 := by
    rw [List.length_append]
    have : (go!"pg/k").length = 4 := rfl
    omega
  have h2 : (go!"v" ++ s).length ≤ 67 := by
    rw [List.length_append]
    have : (go!"v").length = 1 := rfl
    omega
  exact ⟨opSizeOk_opPutModel (K := 70) (E := 0) (V := 67) (optsKeep_nil _ _ _) h1 h2 (by decide),
    opSizeOk_opGetModel (K := 70) (E := 0) (V := 0) (optsKeep_nil _ _ _) h1 (by decide)⟩

/-- durable's prefix (`durablePrefix`). -/
abbrev durablePfx : GoString := go!"du/"

/-- **durable's `j`th key** (`durableKey(j)`): `du/`, `k` and the byte `j`. -/
def durKey (j : Nat) : GoString := durablePfx ++ [W8 107, W8 (j : Int)]

/-- **durable's `j`th value** (`durableValue(j)`): `v` and the byte `j`. -/
def durVal (j : Nat) : GoString := [W8 118, W8 (j : Int)]

theorem durKey_pfx (j : Nat) : durablePfx <+: durKey j := List.prefix_append _ _

/-- A key's value is its last byte's. -/
theorem durVal_of_key {j j' : Nat} (h : durKey j = durKey j') : durVal j = durVal j' := by
  unfold durKey at h
  have h' := List.append_cancel_left h
  have h2 : W8 (j : Int) = W8 (j' : Int) := (List.cons.inj (List.cons.inj h').2).1
  unfold durVal
  rw [h2]

theorem durKey_inj {j j' : Nat} (hj : j < 256) (hj' : j' < 256) (h : durKey j = durKey j') :
    j = j' := by
  unfold durKey at h
  have h' := List.append_cancel_left h
  have h2 : W8 (j : Int) = W8 (j' : Int) := (List.cons.inj (List.cons.inj h').2).1
  have := congrArg BitVec.toNat h2
  simp at this
  omega

/-- Put `j`'s and the range's requests fit a gRPC message. -/
theorem dur_sizes (j : Nat) :
    opSizeOk (opPutModel (durKey j) (durVal j) []) ∧ opSizeOk (opGetModel durablePfx [withPrefixM]) :=
  ⟨opSizeOk_opPutModel (K := 5) (E := 0) (V := 2) (optsKeep_nil _ _ _) (by simp [durKey, durablePfx])
      (by simp [durVal]) (by decide),
    opSizeOk_opGetModel (K := 3) (E := 3) (V := 0)
      (optsKeep_cons (withPrefixM_keep (by decide) (Nat.le_refl _)) (optsKeep_nil _ _ _))
      (by simp [durablePfx]) (by decide)⟩

/-- durable's invariant's facts about the prefix's key-values `v`, the fired puts `F`, `n` puts. -/
def DurOk (n : Nat) (F : List Nat) (v : List EtcdKv) : Prop :=
  (∀ x ∈ v, ∃ j, j ∈ F ∧ j < n ∧ x.key = durKey j ∧ x.value = durVal j ∧ x.version = W64 1) ∧
    (∀ j ∈ F, ∃ x ∈ v, x.key = durKey j)

/-- What durable's range reads: every key-value under `du/` is a put's, at version `1`, and each put of
`S` (fired) has its key-value. -/
def durReadOk (n : Nat) (S : Nat → Prop) (σ : KVState) : Prop :=
  (∀ x ∈ pfxView durablePfx σ, ∃ j, j < n ∧ x.key = durKey j ∧ x.value = durVal j ∧
    x.version = W64 1) ∧ (∀ j, S j → ∃ x ∈ pfxView durablePfx σ, x.key = durKey j)

theorem durOk_nil (n : Nat) : DurOk n [] [] := ⟨by simp, by simp⟩

/-- A put of `durKey j ↦ durVal j`, `j` not fired, keeps the facts, `j` fired. -/
theorem durOk_put {n : Nat} {F : List Nat} {σ : KVState} {j : Nat} (hn : n ≤ 256) (hjn : j < n)
    (hjF : j ∉ F)
    (h : DurOk n F (pfxView durablePfx σ)) :
    DurOk n (F ++ [j]) (pfxView durablePfx (kvOpStep (.put (putKeyOp (durKey j) (durVal j))) σ)) := by
  obtain ⟨h1, h2⟩ := h
  -- the key is absent: a key-value of it would be a fired put's
  have habs : ∀ x ∈ σ.kvs, x.key ≠ durKey j := by
    intro x hx hxk
    have hx' : x ∈ pfxView durablePfx σ := mem_pfxView_of hx (by rw [hxk]; exact durKey_pfx j)
    obtain ⟨j', hj'F, hj'n, hk', -, -⟩ := h1 x hx'
    have hjj : j = j' := by
      apply durKey_inj (by omega) (by omega)
      rw [← hxk, hk']
    · exact hjF (hjj ▸ hj'F)
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases mem_pfxView_put hx with rfl | hx
    · exact ⟨j, by simp, hjn, putKvNew_key _ _ _ _ _, putKvNew_value _ _ _ _ _,
        putKvNew_version _ _ _ _ _ habs⟩
    · obtain ⟨j', hj'F, hj'n, hk, hv, hver⟩ := h1 x hx
      exact ⟨j', List.mem_append_left _ hj'F, hj'n, hk, hv, hver⟩
  · intro j' hj'
    rcases List.mem_append.1 hj' with hj' | hj'
    · obtain ⟨x, hx, hxk⟩ := h2 j' hj'
      have hxk' : x.key ≠ durKey j := habs x (mem_of_mem_pfxView hx).1
      exact ⟨x, pfxView_put_keep hx hxk', hxk⟩
    · have : j' = j := by simpa using hj'
      subst this
      exact ⟨_, pfxView_put_new σ (durKey_pfx j'), putKvNew_key _ _ _ _ _⟩

theorem durReadOk_of {n : Nat} {F : List Nat} {S : Nat → Prop} {σ : KVState}
    (h : DurOk n F (pfxView durablePfx σ)) (hS : ∀ j, S j → j ∈ F) : durReadOk n S σ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨j, -, hjn, hk, hv, hver⟩ := h1 x hx
    exact ⟨j, hjn, hk, hv, hver⟩
  · intro j hj
    exact h2 j (hS j hj)

/-- durable's `acked` slice after `acks`' puts, of `N`. -/
theorem acks_set (acks : List Bool) (N : Nat) (b : Bool) (h : acks.length < N) :
    (acks ++ List.replicate (N - acks.length) false).set acks.length b =
      (acks ++ [b]) ++ List.replicate (N - (acks ++ [b]).length) false := by
  have e : N - acks.length = (N - (acks.length + 1)) + 1 := by omega
  rw [e, List.replicate_succ, List.length_append, List.length_singleton]
  simp

theorem acks_snoc_true {acks : List Bool} {j : Nat} (h : (acks ++ [true])[j]? = some true) :
    acks[j]? = some true ∨ j = acks.length := by
  by_cases hj : j < acks.length
  · left; rwa [List.getElem?_append_left hj] at h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    cases hk : j - acks.length with
    | zero => omega
    | succ k => rw [hk] at h; simp at h

theorem acks_snoc_false {acks : List Bool} {j : Nat} (h : (acks ++ [false])[j]? = some true) :
    acks[j]? = some true := by
  by_cases hj : j < acks.length
  · rwa [List.getElem?_append_left hj] at h
  · exfalso
    rw [List.getElem?_append_right (by omega)] at h
    cases hk : j - acks.length with
    | zero => rw [hk] at h; simp at h
    | succ k => rw [hk] at h; simp at h

/-- The get of a prefix with no other option. -/
abbrev rangeOpPlain (k e : GoString) : OpFull :=
  txn.rangeOpOf k e (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

/-- **A get of a range with no other option selects the state's key-values of the range**, no `More`
(txnlin's `srvRangeOk_list`). -/
theorem srvRangeOk_plain (k e : GoString) (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (rangeOpPlain k e) s kvs more) :
    kvs = s.filter (fun v => inRange k e v.key) ∧ more = false := by
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre (rangeOpPlain k e) s = s.filter (fun v => inRange k e v.key) := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk]
  have hord : (rangeOpPlain k e).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (rangeOpPlain k e) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore (rangeOpPlain k e) L = false := by
    simp [txn.srvMore]
  refine ⟨?_, by rw [hmore, hm]⟩
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hid : txn.respKv (rangeOpPlain k e) = id := by funext v; simp [txn.respKv]
  simp [hid]

/-- `Get("du/", WithPrefix())`'s request. -/
theorem durGetOp_eq :
    rangeWireOf (opGetModel durablePfx [withPrefixM]) =
      rangeOpPlain durablePfx (prefixRangeEnd durablePfx) := by
  first
  | rfl
  | decide
  | simp [rangeWireOf, opGetModel, opFold, withPrefixM, OpFull.getInit, OpFull.newOp, OpModel.zero,
      sortOrderWire, sortTargetWire, durablePfx]

theorem durGet_ok : ¬ opGetPanics [withPrefixM] ∧ (opGetModel durablePfx [withPrefixM]).t = W64 1 :=
  ⟨by simp [opGetPanics, opFold, withPrefixM, OpFull.newOp, OpModel.zero], rfl⟩

/-- **The range of `du/` is the prefix's key-values.** -/
theorem durRange_eq (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (rangeWireOf (opGetModel durablePfx [withPrefixM])) s kvs more) :
    kvs = s.filter (fun v => decide (durablePfx <+: v.key)) := by
  rw [durGetOp_eq] at h
  rw [(srvRangeOk_plain _ _ s kvs more h).1]
  apply List.filter_congr
  intro v _
  have := concurrency.inRange_prefix durablePfx v.key (by simp [durablePfx])
  by_cases hv : durablePfx <+: v.key
  · rw [this.2 hv]; simp [hv]
  · have : inRange durablePfx (prefixRangeEnd durablePfx) v.key = false := by
      cases h' : inRange durablePfx (prefixRangeEnd durablePfx) v.key
      · rfl
      · exact absurd (this.1 h') hv
    rw [this]; simp [hv]

end pure

/-! ## The invariants and their updates -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- putget's part of its invariant, over its prefix's key-values `v`. -/
def pgW (γP : GName) (v : List EtcdKv) : IProp GF :=
  iprop(∃ P : List GoString, monoListAuthOwn γP 1 P ∗ ⌜PgOk P v⌝)

instance pgW_timeless (γP : GName) (v : List EtcdKv) : Timeless (pgW (GF := GF) γP v) := by
  unfold pgW; infer_instance

/-- **putget's invariant** (see the file header). -/
def pgInv (γ γP : GName) : IProp GF :=
  inv (client.kvClientN .@ "pg") iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ pgW γP v)

instance pgInv_persistent (γ γP : GName) : Persistent (pgInv (GF := GF) γ γP) := by
  unfold pgInv; infer_instance

/-- **The put of `k` fired** (persistent). -/
def pgFired (γP : GName) (k : GoString) : IProp GF :=
  iprop(∃ l : List GoString, monoListLbOwn γP l ∗ ⌜k ∈ l⌝)

instance pgFired_persistent (γP : GName) (k : GoString) : Persistent (pgFired (GF := GF) γP k) := by
  unfold pgFired; infer_instance

/-- **A put's update** of `k ↦ pgVal k` (fired at most once), result `pgFired γP k`. -/
theorem pgPutAu (γk : KVNames) (γ γP : GName) (k : GoString) (hk : putgetPfx <+: k) :
    kvPfx (GF := GF) γk putgetPfx γ ∗ pgInv γ γP ⊢
      AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk (kvOpStep (.put (putKeyOp k (pgVal k))) σ) ∗ ⌜kvRoom σ⌝,
           COMM pgFired γP k }> := by
  iintro ⟨#Hp, #Hi⟩
  iunfold pgInv at Hi
  iapply (kvPfx_au1 γk putgetPfx γ "pg" (by decide) (pgW γP) _ (pfxLocal_putKey _ _ _ hk)
    (fun _ => pgFired γP k))
  isplitr
  · iexact Hp
  isplitr
  · iexact Hi
  iintro %σ HW
  iunfold pgW at HW
  icases HW with ⟨%P, Ha, %Hok⟩
  imod (monoListAuthOwn_update_app (GF := GF) [k]) $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  isplitl [Ha]
  · iunfold pgW
    iexists (P ++ [k])
    iframe Ha
    ipureintro; exact pgOk_put hk Hok
  · iunfold pgFired
    iexists (P ++ [k])
    iframe Hlb
    ipureintro; simp

/-- **A get's read update** of `k` after its put fired: `pgReadOk k`. -/
theorem pgGetAu (γk : KVNames) (γ γP : GName) (k : GoString) (hk : putgetPfx <+: k) :
    kvPfx (GF := GF) γk putgetPfx γ ∗ pgInv γ γP ∗ pgFired γP k ⊢
      kvReadAu γk (fun σ => iprop(⌜pgReadOk k σ⌝)) := by
  iintro ⟨#Hp, #Hi, #Hf⟩
  iunfold pgInv at Hi
  iapply (kvPfx_readAu γk putgetPfx γ "pg" (by decide) (pgW γP) (fun σ => iprop(⌜pgReadOk k σ⌝)))
  isplitr
  · iexact Hp
  isplitr
  · iexact Hi
  iintro !> %σ HW
  iunfold pgW at HW
  icases HW with ⟨%P, Ha, %Hok⟩
  iunfold pgFired at Hf
  icases Hf with ⟨%l, #Hlb, %Hkl⟩
  ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γP 1 P l $$ Ha Hlb
  imodintro
  isplitl [Ha]
  · iunfold pgW
    iexists P
    iframe Ha
    ipureintro; exact Hok
  · iintro !>
    ipureintro
    exact pgReadOk_of hk Hok (Hpre.2.subset Hkl)

/-- Round `s`'s put's update (`pgPutAu` at `pg/k<s> ↦ v<s>`). -/
theorem pgPutAu_round (γk : KVNames) (γ γP : GName) (s : GoString) :
    kvPfx (GF := GF) γk putgetPfx γ ∗ pgInv γ γP ⊢
      AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk (kvOpStep (.put (putKeyOp (go!"pg/k" ++ s) (go!"v" ++ s))) σ) ∗ ⌜kvRoom σ⌝,
           COMM pgFired γP (go!"pg/k" ++ s) }> := by
  have h := pgPutAu (GF := GF) γk γ γP (go!"pg/k" ++ s) (putgetPfx_key s)
  rw [pgVal_key] at h
  exact h

/-- durable's part of its invariant: the fired list (monotone at `γF`), the fired puts' tokens. -/
def durW (γF : GName) (γs : List GName) (n : Nat) (v : List EtcdKv) : IProp GF :=
  iprop(∃ F : List Nat, monoListAuthOwn γF 1 F ∗
    ([∗list] j ∈ F, ∃ g : GName, ⌜γs[j]? = some g⌝ ∗ token g) ∗ ⌜DurOk n F v⌝)

instance durW_timeless (γF : GName) (γs : List GName) (n : Nat) (v : List EtcdKv) :
    Timeless (durW (GF := GF) γF γs n v) := by
  unfold durW; infer_instance

/-- **durable's invariant** (see the file header), for `n` puts with tokens `γs`. -/
def durInv (γ γF : GName) (γs : List GName) (n : Nat) : IProp GF :=
  inv (client.kvClientN .@ "du") iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ durW γF γs n v)

instance durInv_persistent (γ γF : GName) (γs : List GName) (n : Nat) :
    Persistent (durInv (GF := GF) γ γF γs n) := by
  unfold durInv; infer_instance

/-- **Put `j` fired** (persistent). -/
def durFired (γF : GName) (j : Nat) : IProp GF :=
  iprop(∃ l : List Nat, monoListLbOwn γF l ∗ ⌜j ∈ l⌝)

instance durFired_persistent (γF : GName) (j : Nat) : Persistent (durFired (GF := GF) γF j) := by
  unfold durFired; infer_instance

/-- `n` tokens. -/
theorem tokens_alloc (n : Nat) :
    ⊢ |==> ∃ γs : List GName, ⌜γs.length = n⌝ ∗ [∗list] g ∈ γs, token (GF := GF) g := by
  induction n with
  | zero =>
    imodintro
    iexists []
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.2
      itrivial
  | succ n ih =>
    ihave H := ih
    imod H with ⟨%γs, %hl, Hs⟩
    imod (token_alloc (GF := GF)) with Hγ
    icases Hγ with ⟨%g, Hg⟩
    imodintro
    iexists (γs ++ [g])
    isplitr
    · ipureintro; simp [hl]
    · iapply BigSepL.bigSepL_append.2
      iframe Hs
      iapply BigSepL.bigSepL_cons.2
      iframe Hg
      iapply BigSepL.bigSepL_nil.2
      itrivial

/-- **The puts of `S` fired** (persistent). -/
def durFiredAll (γF : GName) (S : Nat → Prop) : IProp GF :=
  iprop(∃ l : List Nat, monoListLbOwn γF l ∗ ⌜∀ j, S j → j ∈ l⌝)

instance durFiredAll_persistent (γF : GName) (S : Nat → Prop) :
    Persistent (durFiredAll (GF := GF) γF S) := by
  unfold durFiredAll; infer_instance

/-- One more fired put. -/
theorem durFiredAll_add (γF : GName) (S : Nat → Prop) (j : Nat) :
    durFiredAll (GF := GF) γF S ∗ durFired γF j ⊢ durFiredAll γF (fun j' => S j' ∨ j' = j) := by
  iintro ⟨#H, #Hj⟩
  iunfold durFiredAll at H
  iunfold durFiredAll
  iunfold durFired at Hj
  icases H with ⟨%l, #Hlb, %Hl⟩
  icases Hj with ⟨%l', #Hlb', %Hl'⟩
  ihave %Hc := mono_list_lb_valid (GF := GF) γF l l' $$ Hlb Hlb'
  rcases Hc with Hc | Hc
  · iexists l'
    iframe Hlb'
    ipureintro
    intro j' hj'
    rcases hj' with hj' | rfl
    · exact Hc.subset (Hl j' hj')
    · exact Hl'
  · iexists l
    iframe Hlb
    ipureintro
    intro j' hj'
    rcases hj' with hj' | rfl
    · exact Hl j' hj'
    · exact Hc.subset Hl'

/-- **Put `j`'s update** of `durKey j ↦ durVal j` (fired at most once: it holds put `j`'s token, which it
gives to the invariant), result `durFired γF j`. -/
theorem durPutAu (γk : KVNames) (γ γF : GName) (γs : List GName) (n j : Nat) (g : GName) (hn : n ≤ 256)
    (hjn : j < n)
    (hg : γs[j]? = some g) :
    kvPfx (GF := GF) γk durablePfx γ ∗ durInv γ γF γs n ∗ token g ⊢
      AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk (kvOpStep (.put (putKeyOp (durKey j) (durVal j))) σ) ∗ ⌜kvRoom σ⌝,
           COMM durFired γF j }> := by
  iintro ⟨#Hp, #Hi, Hg⟩
  iunfold durInv at Hi
  iapply (kvPfx_au1 γk durablePfx γ "du" (by decide) (durW γF γs n) _
    (pfxLocal_putKey _ _ _ (durKey_pfx j)) (fun _ => durFired γF j))
  isplitr
  · iexact Hp
  isplitr
  · iexact Hi
  iintro %σ HW
  iunfold durW at HW
  icases HW with ⟨%F, Ha, Hts, %Hok⟩
  by_cases hjF : j ∈ F
  · iexfalso
    ihave Hj := BigSepL.bigSepL_mem hjF $$ Hts
    icases Hj with ⟨%g', %hg', Hg'⟩
    rw [hg] at hg'
    obtain rfl := Option.some.inj hg'
    ihave Hf := token_exclusive (GF := GF) g $$ Hg Hg'
    iexact Hf
  imod (monoListAuthOwn_update_app (GF := GF) [j]) $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  isplitl [Ha Hts Hg]
  · iunfold durW
    iexists (F ++ [j])
    iframe Ha
    isplitl [Hts Hg]
    · iapply BigSepL.bigSepL_append.2
      iframe Hts
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hg]
      · iexists g
        iframe Hg
        ipureintro; exact hg
      iapply BigSepL.bigSepL_nil.2
      itrivial
    ipureintro; exact durOk_put hn hjn hjF Hok
  · iunfold durFired
    iexists (F ++ [j])
    iframe Hlb
    ipureintro; simp

/-- **The range's read update**: `durReadOk n S`, for fired puts `S`. -/
theorem durGetAu (γk : KVNames) (γ γF : GName) (γs : List GName) (n : Nat) (S : Nat → Prop) :
    kvPfx (GF := GF) γk durablePfx γ ∗ durInv γ γF γs n ∗ durFiredAll γF S ⊢
      kvReadAu γk (fun σ => iprop(⌜durReadOk n S σ⌝)) := by
  iintro ⟨#Hp, #Hi, #Hf⟩
  iunfold durInv at Hi
  iapply (kvPfx_readAu γk durablePfx γ "du" (by decide) (durW γF γs n)
    (fun σ => iprop(⌜durReadOk n S σ⌝)))
  isplitr
  · iexact Hp
  isplitr
  · iexact Hi
  iintro !> %σ HW
  iunfold durW at HW
  icases HW with ⟨%F, Ha, Hts, %Hok⟩
  iunfold durFiredAll at Hf
  icases Hf with ⟨%l, #Hlb, %Hl⟩
  ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γF 1 F l $$ Ha Hlb
  imodintro
  isplitl [Ha Hts]
  · iunfold durW
    iexists F
    iframe Ha Hts
    ipureintro; exact Hok
  · iintro !>
    ipureintro
    exact durReadOk_of Hok (fun j hj => Hpre.2.subset (Hl j hj))

end ghost


section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **putget's invariant, allocated** from the owner's half at `[]`. -/
theorem pgInv_alloc (γ : GName) (E : CoPset) :
    ghostVar (GF := GF) γ (1 : Qp).half ([] : List EtcdKv) ={E}=∗ ∃ γP, pgInv (Gg := hG.goose_globalGS) γ γP := by
  iintro Hh
  imod (mono_list_own_alloc (GF := GF) ([] : List GoString)) with ⟨%γP, Ha, -⟩
  imod (inv_alloc (client.kvClientN .@ "pg") E iprop(∃ v, ghostVar (GF := GF) γ (1 : Qp).half v ∗
      pgW (Gg := hG.goose_globalGS) γP v)) $$ [Hh Ha] with #Hinv
  · inext; iexists []; iframe Hh
    iunfold pgW; iexists []; iframe Ha; ipureintro; exact pgOk_nil
  imodintro
  iexists γP
  iunfold pgInv
  iexact Hinv


/-- **durable's invariant, allocated** from the owner's half at `[]`, with `n` puts' tokens (each
`token γs[j]` for put `j`). -/
theorem durInv_alloc (γ : GName) (n : Nat) (E : CoPset) :
    ghostVar (GF := GF) γ (1 : Qp).half ([] : List EtcdKv) ={E}=∗ ∃ (γF : GName) (γs : List GName),
      ⌜γs.length = n⌝ ∗ durInv (Gg := hG.goose_globalGS) γ γF γs n ∗ [∗list] g ∈ γs, token g := by
  iintro Hh
  ihave H := tokens_alloc (Gg := hG.goose_globalGS) n
  imod H with ⟨%γs, %hl, Hts⟩
  imod (mono_list_own_alloc (GF := GF) ([] : List Nat)) with ⟨%γF, Ha, -⟩
  imod (inv_alloc (client.kvClientN .@ "du") E iprop(∃ v, ghostVar (GF := GF) γ (1 : Qp).half v ∗
      durW (Gg := hG.goose_globalGS) γF γs n v)) $$ [Hh Ha] with #Hinv
  · inext; iexists []; iframe Hh
    iunfold durW; iexists []; iframe Ha
    isplitl
    · iapply BigSepL.bigSepL_nil.2
      itrivial
    ipureintro; exact durOk_nil n
  imodintro
  iexists γF, γs
  isplitr
  · ipureintro; exact hl
  iframe Hts
  iunfold durInv
  iexact Hinv



theorem durFiredAll_none (γF : GName) :
    ⊢ |==> durFiredAll (Gg := hG.goose_globalGS) γF (fun _ => False) := by
  ihave H := monoListLbOwn_nil (GF := GF) (A := Nat) γF
  imod H with #Hlb
  imodintro
  iunfold durFiredAll
  iexists []
  iframe Hlb
  ipureintro
  intro j hj
  exact hj.elim

theorem durFiredAll_mono (γF : GName) (S S' : Nat → Prop) (h : ∀ j, S' j → S j) :
    durFiredAll (GF := GF) γF S ⊢ durFiredAll γF S' := by
  iintro #H
  iunfold durFiredAll at H
  iunfold durFiredAll
  icases H with ⟨%l, #Hlb, %Hl⟩
  iexists l
  iframe Hlb
  ipureintro
  intro j hj
  exact Hl j (h j hj)


end alloc

/-! ## The orchestrator's shares (global) -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **A KV workload's share at the endpoints `eps`, owning the prefix `pfx`**: a view `Γ` of the cluster
with auth off, every endpoint serving a member of it, `pfx` owned at some `γ` in the cluster's shared KV,
and the owner's half at `[]` (no key-value under `pfx` yet). -/
def kvPfxShare (pfx : GoString) (eps : List GoString) : IProp GF :=
  iprop(∃ (Γ : DistView) (γ : GName), ⌜Γ.auth = false⌝ ∗ membersAt eps Γ ∗ kvPfx Γ.kv pfx γ ∗
    ghostVar γ (1 : Qp).half ([] : List EtcdKv))

/-- **putget's orchestrator share** (`RunPutGet.spec`'s): `kvPfxShare` at `pg/`. -/
abbrev putgetShare (eps : List GoString) : IProp GF := kvPfxShare putgetPfx eps

/-- **durable's orchestrator share** (`RunDurable.spec`'s): `kvPfxShare` at `du/`. -/
abbrev durableShare (eps : List GoString) : IProp GF := kvPfxShare durablePfx eps

end shares

end etcd_dist_client
end EtcdGrove
end Perennial

end
