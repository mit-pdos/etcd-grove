/- Lean-first (no Rocq counterpart).

# The compact workload of `examples/etcd/dist/client`: its vocabulary (#50 F5)

`notes/etcd-dist-plan.md` §26. `RunCompact` runs on its orchestrator machine against every member's client
endpoint, over the cross-machine contracts `KV_Put_dist`, `KV_Compact_dist`, `KV_Get_dist` and `Watch_dist`, at
the cluster's view `Γ`, owning the prefix `cw/` of the cluster's shared KV (`etcd_dist.kvPfxH`,
`KVPfxDist.lean`) beside putget's and durable's. It is compactwatch's argument (`compactwatch/Rounds.lean`)
with the whole-KV facts restricted to its prefix and its history:

- **Its discipline over its prefix's history** (`cwOk`, kept by the shared invariant): every change of a key
  under `cw/` is a put of `v` (only this workload writes them, each a `Put` of `v`). A watch of one of its keys
  therefore sees only `v` (`rangeEvents_cw`: an event's key and value are its change's, `evsOfRevM_of`).
- **Its invariant** (`cwInv γ γF`, namespace `kvClientN.@"cw"`) keeps the prefix's key-values (the owner's half
  of `pfxView cw/`) with: every value is `v`, and every key of the list `F` (monotone at `γF`: the keys whose
  put fired) has a key-value (`CwOk`, putget's `PgOk` at a constant value). A latest get of a fired key reads
  `v` (`cwReadOk`).
- **A put's result** (`cwPutAu`, fired at most once, `KV_Put_dist`'s one-shot update): its key fired, the state
  it met extending the start's (`KVExt σ₀`), and a lower bound of the history after it. A get at the put's
  revision later reads that state (`KVExt.at_eq`), where the key holds `v` (`cwAt_put`); a latest get later
  reads at a revision at least the put's (`cwSeen`'s bound).
- **A read's result** (`cwReadAu`, `KV_Get_dist`'s and `Watch_dist`'s persistent read update): `cwSeen σ₀ l0 k`:
  the state's history extends the caller's bound `l0` and the start's, keeps the discipline, and the fired key
  `k` reads `v`.

**The share** (what the start supplies; global): `compactShare eps`: a view `Γ` with auth off, in compaction
mode at retention `1` (`Γ.kv.cmp`, `Γ.kv.cret`), every endpoint serving a member of it (`membersAt`), the KV
invariant at the cluster's raft names (`kvInv`, a revision the cluster reached bounds a later read's,
`kvPfx_seen`), the prefix `cw/` owned under `cwOk` from a start state of revision at least `1`, and the owner's
half at `[]`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPfxDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
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

/-- The compact workload's prefix (`compactPrefix`). -/
abbrev compactPfx : GoString := go!"cw/"

/-- The compact workload's value (`compactValue`). -/
abbrev compactVal : GoString := go!"v"

/-- **compact's discipline over its prefix's history**: a change of one of its keys is a put of `v`. -/
def cwOk (c : mvcc.Change) : Prop := ∃ (k : GoString) (l : w64), c = .put k compactVal l

/-- What the invariant keeps of the prefix's key-values `v`, the fired keys `F`. -/
def CwOk (F : List GoString) (v : List EtcdKv) : Prop :=
  (∀ x ∈ v, x.value = compactVal) ∧ (∀ k ∈ F, ∃ x ∈ v, x.key = k)

/-- What a latest get of a fired `k` reads: `k` has a key-value, each of `k`'s has `v`. -/
def cwReadOk (k : GoString) (σ : KVState) : Prop :=
  (∀ x ∈ σ.kvs, x.key = k → x.value = compactVal) ∧ ∃ x ∈ σ.kvs, x.key = k

theorem cwOk_nil : CwOk [] [] := ⟨by simp, by simp⟩

/-- A put of `k ↦ v` (under `cw/`) keeps the facts, `k` fired. -/
theorem cwOk_put {F : List GoString} {σ : KVState} {k : GoString} (hk : compactPfx <+: k)
    (h : CwOk F (pfxView compactPfx σ)) :
    CwOk (F ++ [k]) (pfxView compactPfx (kvOpStep (.put (putKeyOp k compactVal)) σ)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases mem_pfxView_put hx with rfl | hx
    · rw [putKvNew_value]
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

theorem cwReadOk_of {F : List GoString} {σ : KVState} {k : GoString} (hk : compactPfx <+: k)
    (h : CwOk F (pfxView compactPfx σ)) (hkF : k ∈ F) : cwReadOk k σ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx hxk
    exact h1 x (mem_pfxView_of hx (by rw [hxk]; exact hk))
  · obtain ⟨x, hx, hxk⟩ := h2 k hkF
    exact ⟨x, (mem_of_mem_pfxView hx).1, hxk⟩

/-- **A latest get's answer** (`srvRangeOk_getKey`'s selection): a first key-value, of value `v`. -/
theorem cwReadOk_head {k : GoString} {σ : KVState} (h : cwReadOk k σ) :
    ∃ kv0, (σ.kvs.filter (fun v => decide (v.key = k)))[0]? = some kv0 ∧ kv0.value = compactVal := by
  obtain ⟨h1, x, hx, hxk⟩ := h
  have hne : σ.kvs.filter (fun v => decide (v.key = k)) ≠ [] := by
    intro he
    have : x ∈ σ.kvs.filter (fun v => decide (v.key = k)) := List.mem_filter.2 ⟨hx, by simp [hxk]⟩
    rw [he] at this
    simp at this
  obtain ⟨kv0, rest, hkv⟩ := List.exists_cons_of_ne_nil hne
  have hm : kv0 ∈ σ.kvs.filter (fun v => decide (v.key = k)) := by rw [hkv]; simp
  obtain ⟨hm1, hm2⟩ := List.mem_filter.1 hm
  exact ⟨kv0, by rw [hkv]; rfl, h1 kv0 hm1 (by simpa using hm2)⟩

/-- **compact's put keeps its discipline**: its one change is a put of `v`. -/
theorem cwOk_putKey (k : GoString) (σ : KVState) (new : List (List mvcc.Change))
    (h : (kvOpStep (.put (putKeyOp k compactVal)) σ).changes = σ.changes ++ new) :
    ∀ cs ∈ new, ∀ c ∈ cs, cwOk c := by
  obtain ⟨-, -, l, hl⟩ := kvOpStep_putKey_hist k compactVal σ
  rw [hl] at h
  have hn := List.append_cancel_left h
  subst hn
  intro cs hcs c hc
  simp only [List.mem_singleton] at hcs
  subst hcs
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨k, l, rfl⟩

/-- **A put's state, extending the start's** (the history): the state after it extends the start's too. -/
theorem KVExt_putKey {σ₀ σ : KVState} (k val : GoString) (h : KVExt σ₀ σ) :
    KVExt σ₀ (kvOpStep (.put (putKeyOp k val)) σ) := by
  obtain ⟨h1, h2, l, h3⟩ := kvOpStep_putKey_hist k val σ
  refine ⟨by rw [h1]; exact h.1, by rw [h2]; exact h.2.1, ?_⟩
  rw [h3]
  exact h.2.2.trans (List.prefix_append _ _)

theorem putKey_rev (k val : GoString) (σ : KVState) :
    (kvOpStep (.put (putKeyOp k val)) σ).rev = σ.rev + 1 := by
  obtain ⟨h1, -, l, h3⟩ := kvOpStep_putKey_hist k val σ
  unfold KVState.rev; rw [h1, h3]; simp; omega

/-- **The store at a put's revision, read later** (the get at the previous round's revision): a state
extending the start's whose history extends the put's has the put's key at `v` at the put's revision. -/
theorem cwAt_put {σ₀ σp σ : KVState} (k : GoString) (hp : KVExt σ₀ σp) (h : KVExt σ₀ σ)
    (hl : (kvOpStep (.put (putKeyOp k compactVal)) σp).changes <+: σ.changes) :
    (mvcc.findKey k (σ.at (σp.rev + 1)).kvs).map EtcdKv.value = some compactVal := by
  have he := KVExt_putKey k compactVal hp
  rw [← KVExt.at_eq he h hl (σp.rev + 1) (by rw [putKey_rev]; exact Nat.le_refl _)]
  rw [← putKey_rev k compactVal σp]
  exact (kvOpStep_putKey k compactVal σp (KVState.kvs_sorted _)).2

/-- **An event of a revision is one of its changes'**: its key is the change's, and a put's event has the
put's value. -/
theorem evsOfRevM_of (r : Nat) (before : List EtcdKv) (hs : before.Pairwise etcdKvLess)
    (cs : List mvcc.Change) (ev : mvcc.EvM) (h : ev ∈ mvcc.evsOfRevM r before cs) :
    ∃ c ∈ cs, ev.kv.key = c.key ∧ ∀ k v l, c = .put k v l → ev.kv.value = v := by
  unfold mvcc.evsOfRevM at h
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 h
  obtain ⟨kv, hkv, hev⟩ := Option.map_eq_some_iff.1 hi
  subst hev
  have hkv' := hkv
  unfold mvcc.changeKv at hkv'
  -- `evOfKv` keeps the key-value's key and value
  have hkey : (mvcc.evOfKv r kv).kv.key = kv.key := by unfold mvcc.evOfKv; split <;> rfl
  have hval : (mvcc.evOfKv r kv).kv.value = kv.value := by unfold mvcc.evOfKv; split <;> rfl
  cases hc : cs[i]? with
  | none => rw [hc] at hkv'; simp at hkv'
  | some c =>
    rw [hc] at hkv'
    refine ⟨c, List.mem_of_getElem? hc, ?_, ?_⟩
    · cases c with
      | put k v l => rw [hkey]; exact mvcc.findKey_key hkv'
      | del k =>
        simp only [Option.some.injEq] at hkv'
        rw [hkey, ← hkv']; rfl
    · intro k v l hcl
      subst hcl
      simp only at hkv'
      rw [hval]
      have htake : cs.take (i + 1) = cs.take i ++ [mvcc.Change.put k v l] := by
        rw [List.take_add_one, hc]; rfl
      rw [htake] at hkv'
      unfold mvcc.applyChanges at hkv'
      rw [List.foldl_append] at hkv'
      simp only [List.foldl_cons, List.foldl_nil, mvcc.applyChange] at hkv'
      have hs' : (List.foldl (mvcc.applyChange (W64 (r : Int))) before (cs.take i)).Pairwise
          etcdKvLess := mvcc.applyChanges_sorted _ _ hs
      rw [mvcc.findKey_putKv_self_eq hs'] at hkv'
      simp only [Option.some.injEq] at hkv'
      rw [← hkv']
      split <;> rfl

/-- **A watch of one of compact's keys sees only `v`**: under the discipline, every event of the key is a
put of `v`. -/
theorem rangeEvents_cw (σ : KVState) (o : OpFull) (hk : compactPfx <+: o.key)
    (hend : o.base.rangeEnd = []) (hok : PfxChOk compactPfx cwOk σ.changes) (lo hi : Nat)
    (ev : mvcc.EvM) (h : ev ∈ σ.rangeEvents o lo hi) : ev.kv.value = compactVal := by
  unfold KVState.rangeEvents at h
  obtain ⟨h1, hin⟩ := List.mem_filter.1 h
  obtain ⟨l, hl, hev⟩ := List.mem_flatten.1 h1
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hl
  have hkey : ev.kv.key = o.key := by
    unfold inRange at hin
    rw [hend] at hin
    simpa using hin
  unfold KVState.revEvents at hev
  obtain ⟨c, hc, hck, hcv⟩ := evsOfRevM_of r _ (KVStore.kvs_sorted _) _ ev hev
  have hcs : ∃ cs ∈ σ.changes, c ∈ cs := by
    unfold KVState.changesAt at hc
    split at hc
    · simp at hc
    · cases hg : σ.changes[r - σ.compacted - 1]? with
      | none => rw [hg] at hc; simp at hc
      | some cs => rw [hg] at hc; exact ⟨cs, List.mem_of_getElem? hg, hc⟩
  obtain ⟨cs, hcs, hccs⟩ := hcs
  obtain ⟨k, l', hput⟩ := hok cs hcs c hccs (by rw [← hck, hkey]; exact hk)
  exact hcv k compactVal l' hput

/-- A watch of `key` from revision 2: its request's facts (`Watch_dist`'s premise). -/
theorem cw_watch_ok (key : GoString) (hkl : key.length ≤ 70) :
    (opWatchModel key ([withRevM (W64 2)] : List (OpFull → OpFull))).isRangeWatchP (W64 2) = true ∧
      ¬ opWatchPanics key ([withRevM (W64 2)] : List (OpFull → OpFull)) ∧ 1 ≤ sint.Z (W64 2) ∧
      watchSizeOk (opWatchModel key ([withRevM (W64 2)] : List (OpFull → OpFull))) := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.isRangeWatchP, OpFull.newOp,
      OpModel.zero]
  · simp [opWatchPanics, OpFull.watchPanics, opWatchModel, opFold, OpFull.getInit, withRevM,
      OpFull.newOp, OpModel.zero]
  · unfold watchSizeOk
    simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.newOp, OpModel.zero]
    omega

/-- A key under `cw/` is not empty. -/
theorem cw_ne_nil {key : GoString} (h : compactPfx <+: key) : key ≠ [] := by
  intro hk
  rw [hk, List.prefix_nil] at h
  exact absurd h (by decide)

/-- The watch's normalized request is the key alone (no range end). -/
theorem cw_watchNorm (key : GoString) (hk : key ≠ []) :
    (opWatchModel key ([withRevM (W64 2)] : List (OpFull → OpFull))).watchNorm.key = key ∧
      (opWatchModel key ([withRevM (W64 2)] : List (OpFull → OpFull))).watchNorm.base.rangeEnd = [] := by
  constructor <;>
    simp [opWatchModel, opFold, OpFull.getInit, withRevM, OpFull.newOp, OpModel.zero, OpFull.watchNorm, hk]

end pure

/-! ## The invariant and the updates -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- compact's part of its invariant, over its prefix's key-values `v`. -/
def cwW (γF : GName) (v : List EtcdKv) : IProp GF :=
  iprop(∃ F : List GoString, monoListAuthOwn γF 1 F ∗ ⌜CwOk F v⌝)

instance cwW_timeless (γF : GName) (v : List EtcdKv) : Timeless (cwW (GF := GF) γF v) := by
  unfold cwW; infer_instance

/-- **compact's invariant** (see the file header). -/
def cwInv (γ γF : GName) : IProp GF :=
  inv (client.kvClientN .@ "cw") iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ cwW γF v)

instance cwInv_persistent (γ γF : GName) : Persistent (cwInv (GF := GF) γ γF) := by
  unfold cwInv; infer_instance

/-- **The put of `k` fired** (persistent). -/
def cwFired (γF : GName) (k : GoString) : IProp GF :=
  iprop(∃ l : List GoString, monoListLbOwn γF l ∗ ⌜k ∈ l⌝)

instance cwFired_persistent (γF : GName) (k : GoString) : Persistent (cwFired (GF := GF) γF k) := by
  unfold cwFired; infer_instance

/-- **What a put of `k` learns** (persistent; see the file header), at the state `σ` it met. -/
def cwPutQ (γF γh : GName) (σ₀ : KVState) (k : GoString) (σ : KVState) : IProp GF :=
  iprop(cwFired γF k ∗ monoListLbOwn γh (kvOpStep (.put (putKeyOp k compactVal)) σ).changes ∗
    ⌜KVExt σ₀ σ⌝)

instance cwPutQ_persistent (γF γh : GName) (σ₀ : KVState) (k : GoString) (σ : KVState) :
    Persistent (cwPutQ (GF := GF) γF γh σ₀ k σ) := by
  unfold cwPutQ; infer_instance

/-- **What a read learns** (see the file header): the state's history extends `l0` and the start's, keeps
compact's discipline, and the fired `k` reads `v`. -/
def cwSeen (σ₀ : KVState) (l0 : List (List mvcc.Change)) (k : GoString) (σ : KVState) : Prop :=
  l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk compactPfx cwOk σ.changes ∧ cwReadOk k σ

/-- **A put's update** of `k ↦ v` (fired at most once), result `cwPutQ`. -/
theorem cwPutAu (γk : KVNames) (γ γF γh : GName) (σ₀ : KVState) (k : GoString)
    (hk : compactPfx <+: k) :
    kvPfxH (GF := GF) γk compactPfx γ cwOk γh σ₀ ∗ cwInv γ γF ⊢
      AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk (kvOpStep (.put (putKeyOp k compactVal)) σ) ∗ ⌜kvRoom σ⌝,
           COMM cwPutQ γF γh σ₀ k σ }> := by
  iintro ⟨#Hp, #Hi⟩
  iunfold cwInv at Hi
  iapply (kvPfx_au1H γk compactPfx γ cwOk γh σ₀ "cw" (by decide) (cwW γF) _
    (pfxLocal_putKey _ _ _ hk) (fun σ new h => cwOk_putKey k σ new h) (cwPutQ γF γh σ₀ k))
  isplitr
  · iexact Hp
  isplitr
  · iexact Hi
  iintro %σ %Hext #Hlb HW
  iunfold cwW at HW
  icases HW with ⟨%F, Ha, %Hok⟩
  imod (monoListAuthOwn_update_app (GF := GF) [k]) $$ Ha with ⟨Ha, #HlbF⟩
  imodintro
  isplitl [Ha]
  · iunfold cwW
    iexists (F ++ [k])
    iframe Ha
    ipureintro; exact cwOk_put hk Hok
  · iunfold cwPutQ
    iframe Hlb
    isplitl []
    · iunfold cwFired
      iexists (F ++ [k])
      iframe HlbF
      ipureintro; simp
    · ipureintro; exact Hext.1

/-- **A read update** after `k`'s put fired, from a lower bound `l0` of the history: `cwSeen`. -/
theorem cwReadAu (γk : KVNames) (γ γF γh : GName) (σ₀ : KVState) (l0 : List (List mvcc.Change))
    (k : GoString) (hk : compactPfx <+: k) :
    kvPfxH (GF := GF) γk compactPfx γ cwOk γh σ₀ ∗ cwInv γ γF ∗ monoListLbOwn γh l0 ∗ cwFired γF k ⊢
      kvReadAu γk (fun σ => iprop(⌜cwSeen σ₀ l0 k σ⌝)) := by
  iintro ⟨#Hp, #Hi, #Hl0, #Hf⟩
  iunfold cwInv at Hi
  iapply (kvPfx_readAuH γk compactPfx γ cwOk γh σ₀ "cw" (by decide) (cwW γF) l0
    (fun σ => iprop(⌜cwSeen σ₀ l0 k σ⌝)))
  isplitr
  · iexact Hp
  isplitr
  · iexact Hi
  isplitr
  · iexact Hl0
  iintro !> %σ %Hh _Hlb HW
  iunfold cwW at HW
  icases HW with ⟨%F, Ha, %Hok⟩
  iunfold cwFired at Hf
  icases Hf with ⟨%l, #HlbF, %Hkl⟩
  ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γF 1 F l $$ Ha HlbF
  imodintro
  isplitl [Ha]
  · iunfold cwW
    iexists F
    iframe Ha
    ipureintro; exact Hok
  · iintro !>
    ipureintro
    exact ⟨Hh.1, Hh.2.1, Hh.2.2, cwReadOk_of hk Hok (Hpre.2.subset Hkl)⟩

end ghost

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **compact's invariant, allocated** from the owner's half at `[]`. -/
theorem cwInv_alloc (γ : GName) (E : CoPset) :
    ghostVar (GF := GF) γ (1 : Qp).half ([] : List EtcdKv) ={E}=∗
      ∃ γF, cwInv (Gg := hG.goose_globalGS) γ γF := by
  iintro Hh
  imod (mono_list_own_alloc (GF := GF) ([] : List GoString)) with ⟨%γF, Ha, -⟩
  imod (inv_alloc (client.kvClientN .@ "cw") E iprop(∃ v, ghostVar (GF := GF) γ (1 : Qp).half v ∗
      cwW γF v)) $$ [Hh Ha] with #Hinv
  · inext; iexists []; iframe Hh
    iunfold cwW; iexists []; iframe Ha; ipureintro; exact cwOk_nil
  imodintro
  iexists γF
  iunfold cwInv
  iexact Hinv

/-- **What `Client.Close` reads of a client, from `New`'s result** (the same as F2's
`LeaseDefs.clientCoreAt_of_new`, on `etcd-safe-f2`; one of them goes when the branches meet):
`retryClientOk` gives it non-nil with its logger, `clientKVAt` its connection and call options,
`clientNoProxy` its configuration. -/
theorem clientCore_of_new [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (eps : List GoString) (V : WEnv GF) :
    isNewClient cl eps V ∗ clientNoProxy cl ⊢ clientCoreAt cl := by
  iintro ⟨#Hnc, #Hnp⟩
  iunfold isNewClient at Hnc
  icases Hnc with ⟨#Hkv, #Hrc, -⟩
  iunfold clientKVAt at Hkv
  icases Hkv with ⟨%Hnn, %conn, %sl, #Hconn, -, #Hco, -⟩
  iunfold retryClientOk at Hrc
  icases Hrc with ⟨-, #Hlg, -⟩
  iunfold clientNoProxy at Hnp
  icases Hnp with ⟨%cfg, %n, -, #Hcfg, -⟩
  iunfold clientCoreAt
  iframe Hlg
  isplitr
  · ipureintro; exact Hnn
  isplitr
  · iexists conn; iexact Hconn
  isplitr
  · iexists sl; iexact Hco
  iexists cfg; iexact Hcfg

end alloc

/-! ## The orchestrator's share (global) -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.raft.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **compact's orchestrator share at the endpoints `eps`** (`RunCompact.spec`'s; see the file header). -/
def compactShare (eps : List GoString) : IProp GF :=
  iprop(∃ (Γ : DistView) (γr : ServerRaftNames) (γ γh : GName) (σ₀ : KVState),
    ⌜Γ.auth = false ∧ Γ.kv.cmp = true ∧ Γ.kv.cret = 1 ∧ 1 ≤ σ₀.rev⌝ ∗ membersAt eps Γ ∗
    kvInv γr Γ.kv ∗ kvPfxH Γ.kv compactPfx γ cwOk γh σ₀ ∗
    ghostVar γ (1 : Qp).half ([] : List EtcdKv))

end shares

end etcd_dist_client
end EtcdGrove
end Perennial

end
