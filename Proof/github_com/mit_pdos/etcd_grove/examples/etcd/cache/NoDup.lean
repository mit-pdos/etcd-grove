/-
**`cachekv`'s store writes no key twice in a revision** (the cache over a compacting member,
2026-11-02): the member's fact for watches (`mvcc.noDupKeys`, the arm of the create token's
`watchNoDup` for a compacting store), from the writers' plan (`etcd_watch.wkW`: every revision from
`2` on one put of the plan), as `compactkv`'s `noDupKeys_of_rounds`.

* `oneChange_of_wk` (pure): a sealed log (`LogWf'`: its revision `0` empty) that is a prefix of a
  log whose revisions after `0` are a watchkv log's changes changes each key at most once a revision.
* the adapter's `client.kmWAu` (its invariant gives a read update of its plan's fact).
* `noDupKeys_of_wk`: that read update fires at every watched log (`srvKVCoreM_fire`, from the
  member's KV facts), at a committed log it is a prefix of.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchFire
public import Proof.go_etcd_io.etcd.client.v3.KMClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Workload

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- See the file header. -/
theorem oneChange_of_wk (P : List (GoString × GoString)) (L C : mvcc.Log)
    (hw : etcd_watch.wkW P (C.drop 1)) (hp : L <+: C) (hwf : mvcc.LogWf' L) :
    mvcc.oneChangePerKey L := by
  have hnd := hw.1.noDup
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
    exact hnd cs (List.mem_cons_of_mem _ (List.mem_of_getElem? hC))

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
theorem noDupKeys_of_wk [go_etcd_io.raft.v3.Assumptions] [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst) (P : List (GoString × GoString)) :
    client.srvKVFacts V ∗ kvReadAu γ (fun σ => iprop(⌜etcd_watch.wkW P σ.changes⌝)) ⊢
      mvcc.noDupKeys V.R.E.γ := by
  iintro ⟨#Hkf, #Hau⟩
  iunfold client.srvKVFacts at Hkf
  icases Hkf with ⟨%on, %γr, #Hinvs, #H00, %Hkr, -⟩
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
      (fun σ => iprop(⌜etcd_watch.wkW P σ.changes⌝))) $$ Hinvs H00 Hs Hc Hau with ⟨%C, #HQ, %Hp⟩
  icases HQ with %Hw
  imodintro
  ipureintro
  exact oneChange_of_wk P log C Hw Hp Hwf.1

end proof

end etcd_cache
end EtcdGrove
end Perennial
