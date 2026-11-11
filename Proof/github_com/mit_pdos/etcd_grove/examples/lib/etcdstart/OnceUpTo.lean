/-
**The watch condition of a compacting member from its writers' plan** (R9, the `lean` merge,
2026-11-07). Lean-first (no Rocq counterpart).

The client's watch facts take the member's watch condition `v3rpc.srvOnce W` (every certified log
and permitted compaction revision meet mvcc's API's `onceUpTo`; `client.srvOnce_noCmp` for a member
that never compacts). For a member that compacts, the condition comes from the workload: a plan
`Pw` of the committed changes (an invariant of the clients' KV state, read by a read update
`kvReadAu`) under which every revision changes each key at most once (`hP`) gives it
(`srvOnce_of_plan`): the read update fires at every certified log, at a committed log it is a
prefix of (`srvKVFacts_fire`); revision `0` of a certified log is empty (its `LogWf'`). Until the
merge, mvcc's `noDupKeys` (the compacting arm of `watchNoDup`), proved per example
(`noDupKeys_of_wk`, `noDupKeys_of_rounds`, `noDupKeys_of_one`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchFire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure

/-- A prefix of a well-formed log (`LogWf'`: revision `0` empty) whose revisions after `0` are among
a list of change lists without a key twice changes each key at most once a revision. -/
theorem onceUpTo_of_prefix (L L' C : mvcc.Log) (hwf : mvcc.LogWf' L') (hL : L <+: L')
    (hp : L <+: C) (hnd : ∀ cs ∈ C.drop 1, (cs.map mvcc.Change.key).Nodup) (lo : Nat) (c : Int) :
    mvcc.api.onceUpTo L lo c := by
  intro r _ _
  by_cases hr : r < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
    by_cases h0 : r = 0
    · subst h0
      have hne : L' ≠ [] := List.ne_nil_of_length_pos (by have := hL.length_le; omega)
      have hL0 : L'[0]? = some [] := hwf.1 hne
      obtain ⟨t, rfl⟩ := hL
      rw [List.getElem?_append_left hr, List.getElem?_eq_getElem hr] at hL0
      rw [Option.some.inj hL0]
      simp
    · obtain ⟨t, rfl⟩ := hp
      apply hnd
      have hC : ((L ++ t).drop 1)[r - 1]? = some L[r] := by
        rw [List.getElem?_drop, show 1 + (r - 1) = r by omega, List.getElem?_append_left hr,
          List.getElem?_eq_getElem hr]
      exact List.mem_of_getElem? hC
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    simp

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
theorem srvOnce_of_plan (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst)
    (Pw : List (List mvcc.Change) → Prop)
    (hP : ∀ ch, Pw ch → ∀ cs ∈ ch, (cs.map mvcc.Change.key).Nodup) :
    client.srvKVFacts V ∗ kvReadAu γ (fun σ => iprop(⌜Pw σ.changes⌝)) ⊢ v3rpc.srvOnce V.W := by
  iintro ⟨#Hk, #Hau⟩
  ihave #Hk' := Hk
  iunfold client.srvKVFacts at Hk'
  icases Hk' with ⟨%on, %γr, -, -, -, %Ht⟩
  iunfold v3rpc.srvOnce
  rw [Ht.1]
  iintro !> %L %c %lo #HL -
  ihave #HL' := HL
  iunfold srvApi.histLb at HL'
  icases HL' with ⟨-, %L', %HL', -, -⟩
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  imod (srvKVFacts_fire V γ hst L (fun σ => iprop(⌜Pw σ.changes⌝))) $$ [Hk HL Hau]
    with ⟨%C, #HQ, %HC⟩
  · iframe Hk Hau
    rw [Ht.1]
    iexact HL
  icases HQ with %Hw
  imodintro
  ipureintro
  exact onceUpTo_of_prefix L L' C HL'.2 HL'.1 HC (hP _ Hw) lo c

end proof

end etcdstart
end EtcdGrove
end Perennial
