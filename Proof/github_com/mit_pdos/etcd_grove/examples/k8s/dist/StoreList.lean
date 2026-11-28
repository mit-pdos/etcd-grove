/-
Lean-first (no Rocq counterpart).
# k8s-dist K8-11: the list pages' firings on the shared KV
`InvSteps.lean`'s plain first page (`plainL`, `plainL_read_au`) and later pages (`list_later_au`) on the shared
cluster, over the share's read (`kvPfxP_readAuH`), and what the pages' posts tell `GetList` without
`kvKeysShort`: on the shared KV other users' keys may be long and many, so only the facts under `/registry/` hold.
- `kvKeysShortP p`: `kvKeysShort` restricted to the keys under `p`; `keysOkP_shortP` (from the store's
  `keysOkP`).
- `SameL` transfers: `kvWfHist_sameL`, `keysOkP_sameL`, `valsOkP_sameL`, `kvKeysShortP_sameL`.
- `plainLD` (`plainL` at the caught-up state), `plainLD_pure`, `plainLD_read_au`; `listQD_pure` (K8-10's
  first page).
- `revOwnD_ext`, `listD_later_au` (`list_later_au`).

What `GetList` asks of a page's post (`store__GetList.spec`, `store__pagedChunks.spec`, the driver's
`call.spec`: `Q R σ ⊢ ⌜… ∧ kvKeysShort σ ∧ valsOk σ⌝`) is the whole state's; its proof uses it only for keys in
the list's scope, all under the store's prefix (`notes/k8s-dist-k8-scope.md`, Handoff K8-11).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.StoreRead

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s k8s_etcd3
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **`kvKeysShort` under a prefix** (K8-11): at every revision, fewer than `2 ^ 41` key-values under `p`, each
key under `p` shorter than `opKeyMax`. What a list of a scope under `p` needs (its count, its pages' last keys). -/
def kvKeysShortP (p : GoString) (σ : KVState) : Prop :=
  ∀ R ≤ σ.rev, ((σ.at R).kvs.filter (fun kv => decide (p <+: kv.key))).length < 2 ^ 41 ∧
    ∀ kv ∈ (σ.at R).kvs, p <+: kv.key → kv.key.length < opKeyMax

/-- The workload's keys under `/registry/` are few and short (`keysOk_short` restricted). -/
theorem keysOkP_shortP (σ : KVState) (h : keysOkP σ) : kvKeysShortP regP σ := by
  intro R hR
  have hs := KVStore.kvs_sorted (σ.at R)
  have hnd : ((σ.at R).kvs.map EtcdKv.key).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hs.imp fun hab e => by
      unfold etcdKvLess at hab; rw [e] at hab; exact go.goStringLt_irrefl _ hab
  have hnd' : (((σ.at R).kvs.filter (fun kv => decide (regP <+: kv.key))).map EtcdKv.key).Nodup :=
    hnd.sublist ((List.filter_sublist).map _)
  have hsub : ((σ.at R).kvs.filter (fun kv => decide (regP <+: kv.key))).map EtcdKv.key ⊆
      wkKeysL.map mkeyL := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
    obtain ⟨hv, hp⟩ := List.mem_filter.1 hv
    exact h R hR v hv (of_decide_eq_true hp)
  have hl := List.Nodup.length_le_of_subset hnd' hsub
  simp only [List.length_map] at hl
  refine ⟨by simp at hl; omega, fun kv hkv hp => ?_⟩
  have := h R hR kv hkv hp
  simp only [wkKeysL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at this
  rcases this with e | e | e | e <;> rw [e] <;> decide

/-- A longer prefix keeps the bound (a list's scope, under the store's prefix, under `/registry/`). -/
theorem kvKeysShortP_mono {p p' : GoString} {σ : KVState} (hp : p <+: p') (h : kvKeysShortP p σ) :
    kvKeysShortP p' σ := by
  intro R hR
  obtain ⟨h1, h2⟩ := h R hR
  refine ⟨Nat.lt_of_le_of_lt ?_ h1, fun kv hkv hk => h2 kv hkv (hp.trans hk)⟩
  have e : (σ.at R).kvs.filter (fun kv => decide (p' <+: kv.key)) =
      ((σ.at R).kvs.filter (fun kv => decide (p <+: kv.key))).filter
        (fun kv => decide (p' <+: kv.key)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro kv _
    by_cases hk : p' <+: kv.key
    · simp [hk, hp.trans hk]
    · simp [hk]
  rw [e]; exact List.length_filter_le _ _

/-- A property of every revision reads a state only up to its leases. -/
theorem revs_sameL {σc σ : KVState} (hs : SameL σc σ) (P : Nat → KVStore → Prop) :
    (∀ r ≤ σc.rev, P r (σc.at r)) ↔ (∀ r ≤ σ.rev, P r (σ.at r)) := by
  obtain ⟨er, ea⟩ := at_congr hs.1 hs.2.1 hs.2.2
  rw [er]; simp only [ea]

theorem keysOkP_sameL {σc σ : KVState} (hs : SameL σc σ) : keysOkP σc ↔ keysOkP σ :=
  revs_sameL hs (fun _ s => ∀ v ∈ s.kvs, regP <+: v.key → v.key ∈ wkKeysL.map mkeyL)

theorem valsOkP_sameL {σc σ : KVState} (hs : SameL σc σ) : valsOkP σc ↔ valsOkP σ :=
  revs_sameL hs (fun _ s => ∀ v ∈ s.kvs, regP <+: v.key →
    ∀ d, driverCodec.dec v.value = some d → d.1.val.length ≤ 2 ^ 20)

theorem kvKeysShortP_sameL (p : GoString) {σc σ : KVState} (hs : SameL σc σ) :
    kvKeysShortP p σc ↔ kvKeysShortP p σ :=
  revs_sameL hs (fun _ s => (s.kvs.filter (fun kv => decide (p <+: kv.key))).length < 2 ^ 41 ∧
    ∀ kv ∈ s.kvs, p <+: kv.key → kv.key.length < opKeyMax)

end pure

section defs

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem kvWfHist_sameL (c : StoreCfg GF DObj) {σc σ : KVState} (hs : SameL σc σ) :
    kvWfHist c σc ↔ kvWfHist c σ :=
  revs_sameL hs (fun r s => ∀ v ∈ s.kvs, (c.pfx <+: v.key → c.S.dec v.value ≠ none) ∧
    0 < uint.nat v.modRev ∧ uint.nat v.modRev ≤ r)

/-- **A list's plain first page's post on the shared KV** (`plainL`): at the store's caught-up state `σc`,
equal to the read's up to its leases, the store's facts restricted to `/registry/` (as `listQD`). -/
def plainLD (c : StoreCfg GF DObj) (γ : KNames) (σ : KVState) : IProp GF :=
  iprop(∃ σc : KVState, ⌜SameL σc σ⌝ ∗
    ⌜kvWf c σc ∧ kvWfHist c σc ∧ keysOkP σc ∧ σc.rev + 2 < 2 ^ 63 ∧ valsOkP σc⌝ ∗
    ghostMapElem γ.r σc.rev DFrac.discard σc)

instance plainLD_persistent (c : StoreCfg GF DObj) (γ : KNames) (σ : KVState) :
    Persistent (plainLD (GF := GF) c γ σ) := by
  unfold plainLD; infer_instance

/-- The pure facts of a state the store caught up to, at the read's state: `plainL_pure`'s, with
`kvKeysShort`/`valsOk` restricted to `/registry/`. -/
theorem facts_sameL (c : StoreCfg GF DObj) {σc σ : KVState} (hs : SameL σc σ)
    (h : kvWf c σc ∧ kvWfHist c σc ∧ keysOkP σc ∧ σc.rev + 2 < 2 ^ 63 ∧ valsOkP σc) :
    kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShortP regP σ ∧ σ.rev + 2 < 2 ^ 63 ∧ valsOkP σ :=
  ⟨(kvWf_sameL c hs).1 h.1, (kvWfHist_sameL c hs).1 h.2.1,
    (kvKeysShortP_sameL regP hs).1 (keysOkP_shortP σc h.2.2.1),
    hs.kvs_rev.2 ▸ h.2.2.2.1, (valsOkP_sameL hs).1 h.2.2.2.2⟩

theorem plainLD_pure (c : StoreCfg GF DObj) (γ : KNames) (σ : KVState) :
    plainLD (GF := GF) c γ σ ⊢
      ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShortP regP σ ∧ σ.rev + 2 < 2 ^ 63 ∧ valsOkP σ⌝ := by
  unfold plainLD
  iintro ⟨%σc, %hs, %h, -⟩
  ipureintro; exact facts_sameL c hs h

theorem listQD_pure (c : StoreCfg GF DObj) (γ : KNames) (γc : GName) (x : Input) (tl : Bool) (R : w64)
    (σ : KVState) :
    listQD (GF := GF) c γ γc x tl R σ ⊢
      ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShortP regP σ ∧ σ.rev + 2 < 2 ^ 63 ∧ valsOkP σ⌝ := by
  unfold listQD
  iintro ⟨%σc, %hs, %h, -⟩
  ipureintro; exact facts_sameL c hs h

/-- **A list's plain first page's read update, on the shared KV** (`plainL_read_au`): the share's read; at its
firing the store catches up (to `σc`) and nothing else moves. -/
theorem plainLD_read_au (γ : KNames) (c : StoreCfg GF DObj) (hc : CfgD c) (g0 : HSt) (γk : KVNames)
    (γs γsh : GName) (okS : mvcc.Change → Prop) (σ₀ : KVState) (l0 : List (List mvcc.Change)) :
    etcd_dist.kvPfxHP γk regP γs okS γsh σ₀ ∗ kInvD γ c g0 γs γsh σ₀ ∗ monoListLbOwn γsh l0 ⊢
      kvReadAu γk (plainLD c γ) := by
  unfold kInvD drvDInvN kInvDBody
  iintro ⟨#Hpfx, #Hinv, #Hl0⟩
  iapply (kvPfxP_readAuHG γk regP γs okS γsh σ₀ "k8s" (by decide) (kInvDV γ c g0 γsh σ₀) l0)
  isplitl []
  · iexact Hpfx
  isplitl []
  · iexact Hinv
  isplitl []
  · iexact Hl0
  iintro !> %σ %Hpre Ha HW
  obtain ⟨-, he, -, hroom⟩ := Hpre
  have hrb : RevBoundD σ := by unfold RevBoundD; unfold kvRoom at hroom; omega
  imod (kInvDV_catchup γ c hc g0 γsh he hrb) $$ [Ha HW] with ⟨Ha, %σc, %hs, H⟩
  · iframe
  iunfold kInvDW at H
  icases H with ⟨%h, %S, %M, %nx, Hh, HM, Hr, Hs, %Hpure⟩
  obtain ⟨hel, hrun, hok⟩ := Hpure
  have hrc : σc.rev + 2 < 2 ^ 63 := by rw [hs.kvs_rev.2]; exact kvRoom_two hroom
  ihave ⟨Hr, #Hel⟩ := revOwnD_elem γ σc $$ Hr
  ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
  · iunfold kInvDW
    iexists h, S, M, nx
    iframe
    ipureintro; exact ⟨hel, hrun, hok⟩
  ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
  · iframe
  imodintro
  iframe Ha HW
  imodintro
  unfold plainLD
  iexists σc
  isplitr
  · ipureintro; exact hs
  isplitr
  · ipureintro; exact ⟨hok.wf, hok.hwf, hok.keys, hrc, hok.vals⟩
  iexact Hel

/-- A state in the revisions' map is extended by the store's (`revOwn_ext`). -/
theorem revOwnD_ext (γ : KNames) (σ s : KVState) :
    revOwnD (GF := GF) γ σ ∗ ghostMapElem γ.r s.rev DFrac.discard s ⊢
      revOwnD γ σ ∗ ⌜k8s.KvExt s σ⌝ := by
  iintro ⟨H, #Hs⟩
  iunfold revOwnD at H
  icases H with ⟨%Mr, HA, #He, %Hok, Hch, %Hkh⟩
  ihave %Hl := ghost_map_lookup $$ HA Hs
  isplitl
  · iunfold revOwnD
    iexists Mr
    iframe HA He Hch
    ipureintro; exact ⟨Hok, Hkh⟩
  · ipureintro; exact Hok.2.2 _ _ Hl

/-- **A list's later page's read update, on the shared KV** (`list_later_au`), for the first page's state `σ1`,
equal up to its leases to the store's `s` in the revisions' map: it fires only at a state of `σ1`'s history,
not older. -/
theorem listD_later_au (γ : KNames) (c : StoreCfg GF DObj) (hc : CfgD c) (g0 : HSt) (γk : KVNames)
    (γs γsh : GName) (okS : mvcc.Change → Prop) (σ₀ : KVState) (l0 : List (List mvcc.Change))
    (s σ1 : KVState) (hs1 : SameL s σ1) :
    etcd_dist.kvPfxHP γk regP γs okS γsh σ₀ ∗ kInvD γ c g0 γs γsh σ₀ ∗ monoListLbOwn γsh l0 ∗
      ghostMapElem γ.r s.rev DFrac.discard s ⊢
      kvReadAu γk (listP σ1) := by
  unfold kInvD drvDInvN kInvDBody
  iintro ⟨#Hpfx, #Hinv, #Hl0, #Hs1⟩
  iapply (kvPfxP_readAuHG γk regP γs okS γsh σ₀ "k8s" (by decide) (kInvDV γ c g0 γsh σ₀) l0)
  isplitl []
  · iexact Hpfx
  isplitl []
  · iexact Hinv
  isplitl []
  · iexact Hl0
  iintro !> %σ %Hpre Ha HW
  obtain ⟨-, he, -, hroom⟩ := Hpre
  have hrb : RevBoundD σ := by unfold RevBoundD; unfold kvRoom at hroom; omega
  imod (kInvDV_catchup γ c hc g0 γsh he hrb) $$ [Ha HW] with ⟨Ha, %σc, %hs, H⟩
  · iframe
  iunfold kInvDW at H
  icases H with ⟨%h, %S, %M, %nx, Hh, HM, Hr, Hs, %Hpure⟩
  obtain ⟨hel, hrun, hok⟩ := Hpure
  ihave ⟨Hr, %Hext⟩ := revOwnD_ext γ σc s $$ [Hr Hs1]
  · iframe Hr Hs1
  ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
  · iunfold kInvDW
    iexists h, S, M, nx
    iframe
    ipureintro; exact ⟨hel, hrun, hok⟩
  ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
  · iframe
  imodintro
  iframe Ha HW
  imodintro
  unfold listP
  ipureintro
  have hx : k8s.KvExt σ1 σ :=
    ⟨hs1.1.symm.trans (Hext.1.trans hs.1), hs1.2.1.symm.trans (Hext.2.1.trans hs.2.1),
      hs1.2.2 ▸ hs.2.2 ▸ Hext.2.2⟩
  exact kvExt_sameHist hx

end defs

end k8s_dist
end EtcdGrove
end Perennial
