/-
**A watch's completeness, as the cache's contract states it** (the watch slice's unit W-K, K2e-7):
from mvcc's watch events of a sealed log to the cache's chain of steps (`watchChain`,
`cache/v3/InvEtcd.lean`), for a watch whose range covers exactly the keys under a prefix. Lean-first,
no Rocq counterpart.

* `splitBatches_head`, `splitBatches_block`: a leading block of one revision's events, followed by
  later ones, is the first batch.
* `watchChain_of_watch`: the watch events of the revisions `[b, d)` of a sealed small log, with no
  watch event in `[p + 1, b)`, are a chain of steps from `p`, batch by batch.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchContent

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open mvcc txn

/-! ## Batches -/

/-- The first batch's revision is the first event's. -/
theorem splitBatches_head : ∀ B : List EvModel,
    (splitBatches B).head?.map batchRev = B.head?.map EvModel.rev
  | [] => rfl
  | e :: es => by
    unfold splitBatches
    split
    · rfl
    · split <;> rfl

/-- **A leading block of one revision** `x`'s events, followed by events not starting at `x`, is
the first batch. -/
theorem splitBatches_block (x : w64) (B : List EvModel)
    (hB : ∀ e, B.head? = some e → e.rev ≠ x) :
    ∀ A : List EvModel, A ≠ [] → (∀ e ∈ A, e.rev = x) →
      splitBatches (A ++ B) = A :: splitBatches B
  | [], h, _ => absurd rfl h
  | [e], _, hA => by
    have he : e.rev = x := hA e List.mem_cons_self
    show splitBatches (e :: B) = [e] :: splitBatches B
    rw [splitBatches.eq_2]
    cases hs : splitBatches B with
    | nil =>
      have : B = [] := by
        cases B with
        | nil => rfl
        | cons b bs =>
          have h1 := splitBatches_head (b :: bs)
          rw [hs] at h1; simp at h1
      subst this; rfl
    | cons b bs =>
      have h1 := splitBatches_head B
      rw [hs] at h1
      cases B with
      | nil => simp at h1
      | cons b0 bs0 =>
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h1
        have hne := hB b0 rfl
        simp only
        have hc : ¬ batchRev b = e.rev := by rw [h1, he]; exact hne
        simp only [hc, ↓reduceIte]
  | e :: e' :: A', _, hA => by
    have ih := splitBatches_block x B hB (e' :: A') (by simp)
      (fun y hy => hA y (List.mem_cons_of_mem _ hy))
    show splitBatches (e :: (e' :: A' ++ B)) = (e :: e' :: A') :: splitBatches B
    rw [splitBatches.eq_2, show e' :: A' ++ B = e' :: (A' ++ B) from rfl] at *
    rw [ih]
    have h1 : batchRev (e' :: A') = e.rev := by
      show e'.rev = e.rev
      rw [hA e' (List.mem_cons_of_mem _ List.mem_cons_self), hA e List.mem_cons_self]
    simp only [h1, ↓reduceIte]

/-! ## The chain of steps of a block of watch events -/

section chain
open Iris Iris.BI Iris.ProofMode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris Iris.BI Iris.ProofMode

/-- **One revision's watch events, as one batch's step** (`etcdStepCertBody`): from `p` to `b`,
no watch event in `[p + 1, b)`, the events of `b` (with their key-values read-only at `kvs`). -/
theorem stepCert_of_watch (V : WEnv GF) (L : mvcc.Log) (rg : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (p b : Nat) (hpb : p + 1 ≤ b) (hb : b < L.length)
    (hst : V.R.γ.st = V.R.E.γ) (hnone : mvcc.watchEvents L rg (p + 1) b = []) (kvs : List Loc)
    (hkl : kvs.length = (mvcc.watchEvents L rg b (b + 1)).length)
    (hAne : mvcc.watchEvents L rg b (b + 1) ≠ []) :
    mvcc.evLog V.R.γ.st L ∗ srvLogsSmall V.R ∗
      □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜(mvcc.watchEvents L rg b (b + 1))[k]? = some ev⌝ →
        ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ⊢
      etcdStepCertBody (EM := V.EM) pfx (W64 (p : Int))
        (List.zipWith evModelOf (mvcc.watchEvents L rg b (b + 1)) kvs) := by
  iintro ⟨#HL, #Hsm, #Hkv⟩
  ihave #Hs := mvcc.evLog_sealed _ _ $$ HL
  ihave #Hc := mvcc.evLog_certOk _ _ $$ HL
  irevert Hs Hc; rw [hst]; iintro #Hs #Hc
  ihave %Hsmall : ⌜LogSmall L⌝ $$ []
  · iunfold srvLogsSmall at Hsm
    iapply Hsm; rw [hst]; iexact Hs
  ihave #Hsl : v3rpc.srvLog V.R.E L $$ []
  · unfold v3rpc.srvLog; iframe Hs; ipureintro; exact Hsmall
  ihave %Hw := v3rpc.sealed_pure _ L $$ Hs
  have hlen : L.length < 2 ^ 63 := Hw.2
  have hnone' : ∀ x : Nat, p < x → x < b → mvcc.watchEvents L rg x (x + 1) = [] := by
    intro x h1 h2
    have := hnone
    rw [mvcc.watchEvents_append L rg (show p + 1 ≤ x by omega) (show x ≤ b by omega),
      mvcc.watchEvents_append L rg (show x ≤ x + 1 by omega) (show x + 1 ≤ b by omega)] at this
    exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 this).2).1
  ihave #Hstep := v3rpc.srvStep_of_watch V.R.E L rg pfx hcov p b (by omega) hb hnone' $$ Hsl
  generalize hA : mvcc.watchEvents L rg b (b + 1) = A at *
  unfold etcdStepCertBody
  iexists A.map v3rpc.evmToEtcd
  have hbr : batchRev (List.zipWith evModelOf A kvs) = W64 (b : Int) := by
    cases hAe : A with
    | nil => exact absurd hAe hAne
    | cons ev evs =>
      cases kvs with
      | nil => rw [hAe] at hkl; simp at hkl
      | cons kv kvs' =>
        show ev.kv.modRev = _
        have hm : ev ∈ mvcc.watchEvents L rg b (b + 1) := by rw [hA, hAe]; exact List.mem_cons_self
        obtain ⟨j, h1, h2, hj⟩ := v3rpc.watchEvents_mem_rev L rg b (b + 1) ev hm
        have : j = b := by omega
        rw [hj, this]
  isplitr
  · unfold evsMatch
    isplitr
    · ipureintro
      refine ⟨by simp [hkl], fun i e c he hc => ?_⟩
      rw [List.getElem?_zipWith] at he
      rw [List.getElem?_map] at hc
      cases hai : A[i]? with
      | none => rw [hai] at he; simp at he
      | some ev =>
        cases hki : kvs[i]? with
        | none => rw [hai, hki] at he; simp at he
        | some kv =>
          rw [hai, hki] at he; rw [hai] at hc
          simp only [Option.map_some, Option.some.injEq] at he hc
          subst he; subst hc
          exact ⟨rfl, rfl, rfl⟩
    iintro !> %i %e %c %he %hc
    rw [List.getElem?_zipWith] at he
    rw [List.getElem?_map] at hc
    cases hai : A[i]? with
    | none => rw [hai] at he; simp at he
    | some ev =>
      cases hki : kvs[i]? with
      | none => rw [hai, hki] at he; simp at he
      | some kv =>
        rw [hai, hki] at he; rw [hai] at hc
        simp only [Option.map_some, Option.some.injEq] at he hc
        subst he; subst hc
        ihave #Hk := Hkv $$ %i %ev %kv %hai %hki
        ihave ⟨#Hv, -⟩ := kvPtrFixed_facts kv ev.kv $$ Hk
        simp only [evModelOf, v3rpc.evmToEtcd]
        iexact Hv
  isplitr
  · rw [hbr]; iexact Hstep
  isplitr
  · ipureintro
    intro c hc _
    obtain ⟨ev, hev, rfl⟩ := List.mem_map.1 hc
    rw [← hA] at hev
    exact (hcov _).1 (List.mem_filter.1 hev).2
  rw [hbr]
  iapply v3rpc.etcdReached_of_certOk V.R.E L (W64 (b : Int)) (by word) $$ Hc

/-- **A block of watch events as the cache's chain of steps** (`watchChain`): the watch events of
`[b, d)` of a sealed log (`d` within it), a range covering exactly the keys under `pfx`, no watch
event in `[p + 1, b)`: a chain of steps from `p`, one per revision with events. -/
theorem watchChain_of_watch (V : WEnv GF) (L : mvcc.Log) (rg : mvcc.WatchRange) (pfx : GoString)
    (hcov : ∀ k, rg.covers k = true ↔ pfx <+: k) (d : Nat) (hd : d ≤ L.length)
    (hst : V.R.γ.st = V.R.E.γ) :
    ∀ (n p b : Nat) (kvs : List Loc), d - b = n → p + 1 ≤ b →
      mvcc.watchEvents L rg (p + 1) b = [] →
      kvs.length = (mvcc.watchEvents L rg b d).length →
      mvcc.evLog V.R.γ.st L ∗ srvLogsSmall V.R ∗
        □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜(mvcc.watchEvents L rg b d)[k]? = some ev⌝ →
          ⌜kvs[k]? = some kv⌝ → mvcc.kvPtrFixed kv ev.kv) ⊢
      watchChain (EM := V.EM) pfx (W64 (p : Int))
        (splitBatches (List.zipWith evModelOf (mvcc.watchEvents L rg b d) kvs))
  | 0, p, b, kvs, hn, _, _, _ => by
    rw [mvcc.watchEvents_empty L rg (show d ≤ b by omega)]
    iintro -
    simp only [List.zipWith_nil_left, splitBatches]
    unfold watchChain; itrivial
  | n + 1, p, b, kvs, hn, hpb, hnone, hkl => by
    iintro ⟨#HL, #Hsm, #Hkv⟩
    ihave #Hs := mvcc.evLog_sealed _ _ $$ HL
    ihave %Hw := v3rpc.sealed_pure _ L $$ Hs
    have hlen : L.length < 2 ^ 63 := Hw.2
    have hsplit := mvcc.watchEvents_append L rg (show b ≤ b + 1 by omega) (show b + 1 ≤ d by omega)
    by_cases hA : mvcc.watchEvents L rg b (b + 1) = []
    · -- no event at `b`: on to `b + 1`, from the same `p`
      have hevs : mvcc.watchEvents L rg b d = mvcc.watchEvents L rg (b + 1) d := by
        rw [hsplit, hA, List.nil_append]
      rw [hevs] at hkl ⊢
      iapply watchChain_of_watch V L rg pfx hcov d hd hst n p (b + 1) kvs (by omega) (by omega)
        (by rw [mvcc.watchEvents_append L rg hpb (show b ≤ b + 1 by omega), hnone, hA]; rfl) hkl
      iframe HL Hsm
      iintro !> %k %ev %kv %h1 %h2
      iapply Hkv $$ %k %ev %kv %h1 %h2
    · -- the events at `b`: the first batch, then the rest from `b`
      generalize hAe : mvcc.watchEvents L rg b (b + 1) = A at *
      generalize hBe : mvcc.watchEvents L rg (b + 1) d = B at *
      have hkl' : kvs.length = A.length + B.length := by rw [hkl, hsplit, List.length_append]
      have hkvs : kvs = kvs.take A.length ++ kvs.drop A.length := (List.take_append_drop _ _).symm
      have hzip : List.zipWith evModelOf (A ++ B) kvs =
          List.zipWith evModelOf A (kvs.take A.length) ++
            List.zipWith evModelOf B (kvs.drop A.length) := by
        calc List.zipWith evModelOf (A ++ B) kvs
            = List.zipWith evModelOf (A ++ B) (kvs.take A.length ++ kvs.drop A.length) := by
              rw [List.take_append_drop]
          _ = _ := List.zipWith_append (by simp [hkl'])
      have hrevA : ∀ e ∈ List.zipWith evModelOf A (kvs.take A.length), e.rev = W64 (b : Int) := by
        intro e he
        obtain ⟨ev, hev, hr⟩ := mem_zipWith_evModel he
        rw [hr]
        obtain ⟨j, h1, h2, hj⟩ := v3rpc.watchEvents_mem_rev L rg b (b + 1) ev (by rw [hAe]; exact hev)
        rw [hj, show j = b by omega]
      have hrevB : ∀ e, (List.zipWith evModelOf B (kvs.drop A.length)).head? = some e →
          e.rev ≠ W64 (b : Int) := by
        intro e he hr
        obtain ⟨ev, hev, hr'⟩ := mem_zipWith_evModel (List.mem_of_head? he)
        obtain ⟨j, h1, h2, hj⟩ := v3rpc.watchEvents_mem_rev L rg (b + 1) d ev (by rw [hBe]; exact hev)
        rw [hr', hj] at hr
        have := W64_inj_of_lt (by omega) (by omega) hr
        omega
      have hAne' : List.zipWith evModelOf A (kvs.take A.length) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp only [List.length_zipWith, List.length_take, List.length_nil] at this
        apply hA
        apply List.eq_nil_of_length_eq_zero
        omega
      rw [hsplit, hzip, splitBatches_block (W64 (b : Int)) _ hrevB _ hAne' hrevA]
      have hbr : batchRev (List.zipWith evModelOf A (kvs.take A.length)) = W64 (b : Int) := by
        cases hz : List.zipWith evModelOf A (kvs.take A.length) with
        | nil => exact absurd hz hAne'
        | cons e es => exact hrevA e (by rw [hz]; exact List.mem_cons_self)
      unfold watchChain
      rw [hbr]
      isplitr
      · have H1 := stepCert_of_watch V L rg pfx hcov p b hpb (by omega) hst hnone (kvs.take A.length)
          (by rw [hAe]; simp [hkl']) (by rw [hAe]; exact hA)
        rw [hAe] at H1
        iapply H1
        iframe HL Hsm
        iintro !> %k %ev %kv %h1 %h2
        iapply Hkv $$ %k %ev %kv
          %(by rw [List.getElem?_append_left (by
              rw [List.getElem?_take] at h2; split at h2
              · exact (List.getElem?_eq_some_iff.1 h1).1
              · cases h2)]; exact h1)
          %(by rw [List.getElem?_take] at h2; split at h2
               · exact h2
               · cases h2)
      isplitr
      · ipureintro; word
      have H2 := watchChain_of_watch V L rg pfx hcov d hd hst n b (b + 1) (kvs.drop A.length)
        (by omega) (by omega) (mvcc.watchEvents_empty L rg (Nat.le_refl _)) (by rw [hBe]; simp [hkl'])
      rw [hBe] at H2
      iapply H2
      iframe HL Hsm
      iintro !> %k %ev %kv %h1 %h2
      rw [List.getElem?_drop] at h2
      iapply Hkv $$ %(A.length + k) %ev %kv
        %(by rw [List.getElem?_append_right (by omega)]; simpa using h1) %h2

end chain

end client
end EtcdGrove
end Perennial
