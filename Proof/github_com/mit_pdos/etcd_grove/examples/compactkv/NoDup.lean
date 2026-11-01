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

end proof

end compactkv
end EtcdGrove
end Perennial
