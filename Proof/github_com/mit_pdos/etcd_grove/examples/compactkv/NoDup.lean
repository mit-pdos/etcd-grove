/-
**`compactkv`'s store writes no key twice in a revision** (watches across a compaction, W4,
2026-11-01): the member's fact for watches (`mvcc.noDupKeys`, the arm of the create token's
`watchNoDup` for a compacting store).

* `oneChange_of_oneVal` (pure): a sealed log (`LogWf'`: its revision `0` empty) that is a prefix of a
  log whose revisions after `0` are each one put of `val`, or empty (`oneValW`), changes each key at
  most once a revision.
* `noDupKeys_of_rounds`: the rounds' read update (`oneValAu`) fires at every watched log
  (`srvKVCoreM_fire`, from the member's KV facts), at a committed log it is a prefix of.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.Rounds
public import Proof.go_etcd_io.etcd.client.v3.WatchFire
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.RespChan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- See the file header. -/
theorem oneChange_of_oneVal (val : GoString) (L C : mvcc.Log) (hov : oneValW val (C.drop 1))
    (hp : L <+: C) (hwf : mvcc.LogWf' L) : mvcc.oneChangePerKey L := by
  intro c cs _ hcs
  have hlt : c.toNat < L.length := (List.getElem?_eq_some_iff.1 hcs).1
  by_cases h0 : c.toNat = 0
  · have hL0 := hwf.1 (by intro h; rw [h] at hlt; simp at hlt)
    rw [h0, hL0] at hcs
    cases hcs
    simp
  · obtain ⟨t, rfl⟩ := hp
    have hC : ((L ++ t).drop 1)[c.toNat - 1]? = some cs := by
      rw [List.getElem?_drop, show 1 + (c.toNat - 1) = c.toNat by omega,
        List.getElem?_append_left hlt]
      exact hcs
    rcases hov cs (List.mem_of_getElem? hC) with h | ⟨k, l, h⟩
    · subst h; simp
    · subst h; simp

/-- **A bootstrap log's KV model is the start log** (its entries conf changes: `kvTableOf_boot`'s,
for the log). -/
theorem kvModel_boot (γk : KVNames) (ps : List w64) (bootLog : List EntryM)
    (hb : srvBootLogOk ps bootLog) : kvModel γk (bootEntries bootLog) = γk.log0 := by
  obtain ⟨-, -, he⟩ := hb
  unfold kvModel kvRaftOf kvRaftSt bootEntries
  rw [List.foldl_map]
  suffices h : ∀ (l : List EntryM) (s : mvcc.Log × LeaseTable), (∀ e ∈ l, e.Type' = W32 1) →
      l.foldl (fun s e => kvEntrySt γk.c0 γk.ch0 s (EntryModel.ofM e)) s = s by
    rw [h]
    intro e hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    exact (he k _ (List.getElem?_eq_getElem hk)).2.2.1
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons e l ih =>
    intro s hl
    rw [List.foldl_cons]
    have ht : e.Type' = W32 1 := hl e (List.mem_cons_self ..)
    have : kvEntrySt γk.c0 γk.ch0 s (EntryModel.ofM e) = s := by
      unfold kvEntrySt kvEntry kvTable
      simp only [EntryModel.ofM, ht]
      rfl
    rw [this]
    exact ih s (fun e' h' => hl e' (List.mem_cons_of_mem _ h'))

/-- **Every event of a revision of a state whose revisions are each one put of `val` is of
value `val`** (`oneValW`; the watch's events, W4). -/
theorem revEvents_val (σ : KVState) (val : GoString) (hov : oneValW val σ.changes) (r : Nat)
    (ev : mvcc.EvM) (h : ev ∈ σ.revEvents r) : ev.kv.value = val := by
  unfold KVState.revEvents at h
  have hcs : σ.changesAt r = [] ∨ ∃ (k : GoString) (l : w64), σ.changesAt r = [.put k val l] := by
    unfold KVState.changesAt
    split
    · left; rfl
    · cases hc : σ.changes[r - σ.compacted - 1]? with
      | none => left; rfl
      | some cs => simpa using hov cs (List.mem_of_getElem? hc)
  rcases hcs with h0 | ⟨k, l, h1⟩
  · rw [h0] at h; simp [mvcc.evsOfRevM] at h
  · rw [h1] at h
    have hs := KVStore.kvs_sorted (σ.at (r - 1))
    have hck : mvcc.changeKv (W64 r) (σ.at (r - 1)).kvs [.put k val l] 0 =
        mvcc.findKey k (putKv (W64 r) k val l (σ.at (r - 1)).kvs) := by
      simp [mvcc.changeKv, mvcc.applyChanges, mvcc.applyChange]
    rw [mvcc.findKey_putKv_self_eq hs] at hck
    simp only [mvcc.evsOfRevM, List.length_singleton, List.range_one, List.filterMap_cons,
      List.filterMap_nil, hck, Option.map_some] at h
    simp only [List.mem_singleton] at h
    subst h
    unfold mvcc.evOfKv
    split <;> (split <;> rfl)

/-- **Every event a range reads of such a state is of value `val`.** -/
theorem rangeEvents_val (σ : KVState) (val : GoString) (hov : oneValW val σ.changes) (o : OpFull)
    (lo hi : Nat) (ev : mvcc.EvM) (h : ev ∈ σ.rangeEvents o lo hi) : ev.kv.value = val := by
  unfold KVState.rangeEvents at h
  obtain ⟨h1, -⟩ := List.mem_filter.1 h
  obtain ⟨l, hl, hev⟩ := List.mem_flatten.1 h1
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hl
  exact revEvents_val σ val hov r ev hev

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
theorem noDupKeys_of_rounds [go_etcd_io.raft.v3.Assumptions] [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst) (val : GoString) :
    client.srvKVFacts V ∗ kvReadAu γ (fun σ => iprop(⌜oneValW val σ.changes⌝)) ⊢
      mvcc.noDupKeys V.R.E.γ := by
  iintro ⟨#Hkf, #Hau⟩
  iunfold client.srvKVFacts at Hkf
  icases Hkf with ⟨%on, %γr, #Hinvs, #H00, %Hkr⟩
  iunfold mvcc.noDupKeys
  iintro !> %log #Hev
  iunfold mvcc.evLog at Hev
  icases Hev with ⟨#Hs, #Hc⟩
  ihave #Hs' := Hs
  iunfold mvcc.idxSealed at Hs'
  icases Hs' with ⟨-, %Hwf, -⟩
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  imod (srvKVCoreM_fire on V.R.E γr γ (by rw [hst, Hkr.1]) Hkr.2.1 log
      (fun σ => iprop(⌜oneValW val σ.changes⌝))) $$ Hinvs H00 Hs Hc Hau with ⟨%C, #HQ, %Hp⟩
  icases HQ with %Hov
  imodintro
  ipureintro
  exact oneChange_of_oneVal val log C Hov Hp Hwf.1

/-- **One response of `compactkv`'s watch** (`Collect`'s premise at the Watch spec's responses,
`stateOk` at the rounds' read update `oneValW`): every event is of value `val`. -/
theorem resp_val (o : OpFull) (val : GoString) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v) :
    ⊢ common.stateOk (GF := GF) o (fun σ => iprop(⌜oneValW val σ.changes⌝)) c c' v r ={⊤}=∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        ∃ kvv : EtcdKv, kvValAt e.kv kvv ∗ ⌜kvv.value = val⌝ := by
  iintro Hok
  unfold common.stateOk
  icases Hok with ⟨%σ, #HQ, #Hr⟩
  icases HQ with %Hov
  unfold watchStateRespOk
  icases Hr with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hev⟩)
  · exact absurd H.1 hne
  · obtain ⟨-, he0, -, -⟩ := H
    imodintro; iintro !> %j %e %h
    rw [he0] at h; simp at h
  · obtain ⟨-, hp, -⟩ := H
    have he0 := isProgressNotify_events hp
    imodintro; iintro !> %j %e %h
    rw [he0] at h; simp at h
  · iunfold eventsIs at Hev
    icases Hev with ⟨%hlen, #Hall⟩
    imodintro
    iintro !> %j %e %hj
    have hjl : j < r.events.length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨ev, hev⟩ : ∃ ev, (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))[j]? = some ev :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact hjl)⟩
    ihave #Hei := Hall $$ %j %e %ev %hj %hev
    iunfold eventIs at Hei
    icases Hei with ⟨-, #Hkv⟩
    iexists ev.kv
    iframe Hkv
    ipureintro
    exact rangeEvents_val σ val Hov o _ _ ev (List.mem_of_getElem? hev)

end proof

end compactkv
end EtcdGrove
end Perennial
