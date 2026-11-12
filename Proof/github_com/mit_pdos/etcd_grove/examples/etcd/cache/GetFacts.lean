/-
**The cache's `Get` at a watchkv server**: what `Main`'s check of the cache's answer rests on
(`checkGet`'s premise, `CheckGetOk`). The cache's `Get` of the prefix at revision `r` answers
etcd's state there (`cacheGetOk`'s `isEtcdKvs`, at the adapter's model: a log the client saw,
`client.kmEtcdState`); that log is a watchkv log (the adapter's invariant at the plan's fact,
`kmInv`, as `km_step_log`), and holds the watch's events at their revisions (`collect`'s
`etcdstart.kmRevAt`s, its lower bounds agreeing with the log's); the pure law `checkGetOk_of'`
(`GetCheck.lean`) does the rest.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.CacheFacts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.GetCheck
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.hasKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.cache.v3

/-- A watchkv log has only empty and single-put revisions. -/
theorem onePuts_of_wk {P : List (GoString × GoString)} {L : mvcc.Log} (h : etcd_watch.WkLog P L) :
    OnePuts L := by
  intro cs hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
  by_cases h2 : j < 2
  · exact Or.inl (h.1 j cs h2 hj)
  · obtain ⟨k, v, -, rfl⟩ := h.2 j cs (by omega) hj
    exact Or.inr ⟨k, v, rfl⟩

/-- `snapshot.Range`'s selection is `inRange`'s. -/
theorem kvRange_eq_filter (start end_ : GoString) (m : KvMap) :
    kvRange start end_ m = m.filter (fun e => inRange start end_ e.1) := by
  unfold kvRange inRange
  split
  · rfl
  · split <;> rfl

/-- A map whose keys all have the prefix is its whole prefix range. -/
theorem kvRange_prefix (m : KvMap) (h : ∀ e ∈ m, ckPfx <+: e.1) :
    kvRange ckPfx (prefixRangeEnd ckPfx) m = m := by
  rw [kvRange_eq_filter, List.filter_eq_self]
  intro e he
  exact (concurrency.inRange_prefix ckPfx e.1 (by decide)).2 (h e he)

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The check of the cache's `Get` holds** (see the file header): for the events `evs` the
watch read gap-free from revision `2` (`collect`'s facts) and a `Get` of the prefix at a revision
`1 ≤ r ≤ 1 + evs.length`, the answer's key-values `s` (`kvValsAt m s`) pass `checkGet`. -/
theorem getCheck_km (γ : client.KMNames) (P : List (GoString × GoString))
    (hW : γ.W = etcd_watch.wkW P) (evs : List etcdstart.wev) (r : w64) (m : KvMap)
    (hrev : ∀ (i : Nat) (e : etcdstart.wev), evs[i]? = some e →
      sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P)
    (hpk : ∀ kv ∈ P, ckPfx <+: kv.1)
    (hr1 : 1 ≤ sint.Z r) (hre : sint.Z r ≤ 1 + evs.length) :
    ⊢ client.kmInv (GF := GF) γ -∗
      (□ ∀ (i : Nat) (e : etcdstart.wev), ⌜evs[i]? = some e⌝ -∗
        etcdstart.kmRevAt γ (2 + i) e.Key' e.Val') -∗
      isEtcdKvs (EM := client.etcdModelOfKV γ) r ckPfx m ={⊤}=∗
      ∃ s : List EtcdKv, ⌜CheckGetOk evs r s ∧ m.length = s.length ∧
        kvRange ckPfx (prefixRangeEnd ckPfx) m = m⌝ ∗ kvValsAt m s := by
  iintro #Hinv #Hrev Hm
  icases isEtcdKvs_elim (EM := client.etcdModelOfKV γ) _ _ _ $$ Hm with ⟨%s, #Hst, %Hm, #Hv⟩
  ihave Hst' : client.kmEtcdState γ r ckPfx s $$ []
  · rw [← client.etcdModelOfKV_etcdState]; iexact Hst
  icases client.kmEtcdState_elim _ _ _ _ $$ Hst' with ⟨%L, #HL, %HLs⟩
  -- the log is a watchkv log: a prefix of the changes of a state satisfying the plan's fact
  imod client.kmLog_W γ L $$ Hinv HL with %HW
  obtain ⟨cs, hcs, hLcs⟩ := HW
  have hwk : etcd_watch.WkLog P L :=
    etcd_watch.wkW_prefix (by rw [← hW]; exact hcs) (List.prefix_refl _) hLcs
  -- the events' puts are the log's, where it has them
  ihave %Hput : ⌜∀ (i : Nat) (e : etcdstart.wev), evs[i]? = some e → 2 + i < L.length →
      L[2 + i]? = some [mvcc.Change.put e.Key' e.Val' (W64 0)]⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %i
    iapply BI.pure_forall.2
    iintro %e
    by_cases hi : evs[i]? = some e
    · ihave Hr := Hrev $$ %i %e %hi
      by_cases hiL : 2 + i < L.length
      · ihave %h := etcdstart.kmRevAt_log γ L (2 + i) e.Key' e.Val' hiL $$ [$HL $Hr]
        ipureintro; intro _ _; exact h
      · ipureintro; intro _ h; exact absurd h hiL
    · ipureintro; intro h; exact absurd h hi
  imodintro
  iexists s
  iframe Hv
  ipureintro
  refine ⟨?_, Hm.1, kvRange_prefix m Hm.2⟩
  rw [HLs.2.2]
  refine checkGetOk_of' L evs r ckPfx (onePuts_of_wk hwk) hwk.1 (fun i e h => (hrev i e h).1)
    Hput (fun e he => ?_) hr1 HLs.2.1 hre
  obtain ⟨i, hi⟩ := List.getElem?_of_mem he
  exact hpk _ (hrev i e hi).2

theorem isEtcdKvs_cast [EM : EtcdModel GF] {R R' : w64} {p p' : GoString} {m : KvMap}
    (h1 : R = R') (h2 : p = p') : isEtcdKvs (GF := GF) R p m ⊢ isEtcdKvs R' p' m := by
  subst h1; subst h2; iintro H; iexact H

/-- The answer's key-values hold the state's values (`checkGet`'s premise). -/
theorem kvsHold_of_vals (m : KvMap) (s : List EtcdKv) (h : m.length = s.length) :
    kvValsAt (GF := GF) m s ⊢ kvsHold (m.map Prod.snd) s := by
  iintro #H
  iapply kvsHold_intro
  isplitr
  · ipureintro; simpa using h
  imodintro
  iintro %i %p %v %hp %hv
  rw [List.getElem?_map] at hp
  cases he : m[i]? with
  | none => rw [he] at hp; cases hp
  | some e =>
    rw [he] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    subst hp
    iapply kvValsAt_at m s i e v he hv $$ H

end iris

end etcd_cache
end EtcdGrove
end Perennial
