/-
**The cache's `Get` at a watchkv server**: what `Main`'s check of the cache's answer rests on
(`checkGet`'s premise, `CheckGetOk`). The cache's `Get` of the prefix at revision `r` answers
etcd's state there (`cacheGetOk`'s `isEtcdKvs`, at the adapter's model: a log the client saw,
`client.kmEtcdState`); that log is a watchkv log (the adapter's invariant at the plan's fact,
`kmInv`, as `km_step_log`), and holds the watch's events at their revisions (`collect`'s
`common.kmRevAt`s, its lower bounds agreeing with the log's); the pure law `checkGetOk_of'`
(`GetCheck.lean`) does the rest.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.CacheFacts
public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.GetCheck
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.hasKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.cache.v3

/-- A watchkv log has only empty and single-put revisions. -/
theorem onePuts_of_wk {P : List (GoString × GoString)} {L : mvcc.Log} (h : watchkv.WkLog P L) :
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
    (hW : γ.W = watchkv.wkW P) (evs : List common.wev) (r : w64) (m : KvMap)
    (hrev : ∀ (i : Nat) (e : common.wev), evs[i]? = some e →
      sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P)
    (hpk : ∀ kv ∈ P, ckPfx <+: kv.1)
    (hr1 : 1 ≤ sint.Z r) (hre : sint.Z r ≤ 1 + evs.length) :
    ⊢ client.kmInv (GF := GF) γ -∗
      (□ ∀ (i : Nat) (e : common.wev), ⌜evs[i]? = some e⌝ -∗
        common.kmRevAt γ (2 + i) e.Key' e.Val') -∗
      isEtcdKvs (EM := client.etcdModelOfKV γ) r ckPfx m ={⊤}=∗
      ∃ s : List EtcdKv, ⌜CheckGetOk evs r s ∧ m.length = s.length ∧
        kvRange ckPfx (prefixRangeEnd ckPfx) m = m⌝ ∗ kvValsAt m s := by
  iintro #Hinv #Hrev Hm
  unfold isEtcdKvs
  icases Hm with ⟨%s, #Hst, %Hk, %Hwf, #Hv⟩
  ihave Hst' : client.kmEtcdState γ r ckPfx s $$ []
  · rw [← client.etcdModelOfKV_etcdState]; iexact Hst
  iunfold client.kmEtcdState at Hst'
  icases Hst' with ⟨%L, #HL, %HLs⟩
  iunfold client.kmLog at HL
  icases HL with ⟨%l, #Hlb, %Hl⟩
  -- the log is a watchkv log: a prefix of the invariant's state's changes
  iunfold client.kmInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %mm, Hσ, Hc, Ht, %Hmm⟩
  ihave %Hp := mono_list_auth_lb_valid γ.ch 1 σ.changes l $$ Hc Hlb
  imod Hclose $$ [Hσ Hc Ht] with -
  · inext; iexists σ, mm; iframe; ipureintro; exact Hmm
  have hwk : watchkv.WkLog P L := watchkv.wkW_prefix (by rw [← hW]; exact Hmm.2) Hp.2 Hl.1
  -- the events' puts are the log's, where it has them
  ihave %Hput : ⌜∀ (i : Nat) (e : common.wev), evs[i]? = some e → 2 + i < L.length →
      L[2 + i]? = some [mvcc.Change.put e.Key' e.Val' (W64 0)]⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %i
    iapply BI.pure_forall.2
    iintro %e
    by_cases hi : evs[i]? = some e
    · ihave Hr := Hrev $$ %i %e %hi
      iunfold common.kmRevAt at Hr
      icases Hr with ⟨%l', #Hlb', %h'⟩
      ihave %Hp' := mono_list_lb_valid γ.ch l l' $$ Hlb Hlb'
      ipureintro
      intro _ hiL
      have hc : ([] :: l : mvcc.Log) <+: [] :: l' ∨ ([] :: l' : mvcc.Log) <+: [] :: l :=
        Hp'.imp client.log_prefix_of client.log_prefix_of
      obtain ⟨t, ht⟩ := Hl.1
      have hrL : 2 + i < ([] :: l : mvcc.Log).length := by
        rw [← ht, List.length_append]; omega
      have hrL' : 2 + i < ([] :: l' : mvcc.Log).length := (List.getElem?_eq_some_iff.mp h').1
      have e1 : L[2 + i]? = ([] :: l : mvcc.Log)[2 + i]? := by
        rw [← ht, List.getElem?_append_left hiL]
      have e2 : ([] :: l : mvcc.Log)[2 + i]? = ([] :: l' : mvcc.Log)[2 + i]? := by
        rcases hc with ⟨t', ht'⟩ | ⟨t', ht'⟩
        · rw [← ht', List.getElem?_append_left hrL]
        · rw [← ht', List.getElem?_append_left hrL']
      rw [e1, e2, h']
    · ipureintro; intro h; exact absurd h hi
  imodintro
  iexists s
  iframe Hv
  ipureintro
  refine ⟨?_, ?_⟩
  · rw [HLs.2.2]
    refine checkGetOk_of' L evs r ckPfx (onePuts_of_wk hwk) hwk.1 (fun i e h => (hrev i e h).1)
      Hput (fun e he => ?_) hr1 HLs.2.1 hre
    obtain ⟨i, hi⟩ := List.getElem?_of_mem he
    exact hpk _ (hrev i e hi).2
  · refine ⟨by have := congrArg List.length Hk; simpa using this, kvRange_prefix m ?_⟩
    intro e he
    have hk : e.1 ∈ s.map EtcdKv.key := by rw [← Hk]; exact List.mem_map_of_mem he
    obtain ⟨v, hv, hve⟩ := List.mem_map.1 hk
    rw [← hve]; exact Hwf.2 v hv

theorem isEtcdKvs_cast [EM : EtcdModel GF] {R R' : w64} {p p' : GoString} {m : KvMap}
    (h1 : R = R') (h2 : p = p') : isEtcdKvs (GF := GF) R p m ⊢ isEtcdKvs R' p' m := by
  subst h1; subst h2; iintro H; iexact H

/-- The answer's key-values hold the state's values (`checkGet`'s premise). -/
theorem kvsHold_of_vals (m : KvMap) (s : List EtcdKv) (h : m.length = s.length) :
    kvValsAt (GF := GF) m s ⊢ kvsHold (m.map Prod.snd) s := by
  unfold kvValsAt kvsHold
  iintro #H
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
    iapply H $$ %i %e %v %he %hv

/-- **The cache's `Get` errors are non-nil**: each is a fixed non-nil error of the cache's or
`rpctypes`' package (their facts), or one the spec says is non-nil. -/
theorem cacheGetErr_ne_nil [EM : EtcdModel GF] [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (cf : CacheFields) (r0 : w64) (s : context.ContextDesc (IProp GF)) (key : GoString)
    (o : OpModel) (err : GoInterface) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 -∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes -∗
      cacheGetErr cf r0 s key o err -∗ ⌜err ≠ GoInterface.nil⌝ := by
  iintro #Hpkg #Hrpc Herr
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨⟨%eNR, #HeNR⟩, -, ⟨%eKR, #HeKR⟩, ⟨%eCT, #HeCT⟩, -⟩
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨⟨%eFR, #HeFR⟩, ⟨%eCP, #HeCP, -⟩, -⟩
  iunfold cacheGetErr at Herr
  icases Herr with (⟨%h, -⟩ | %h | ⟨-, #H⟩ | %h | ⟨-, #H, -⟩ | ⟨-, #H⟩ | ⟨%st, -, #Hse, %Hno⟩)
  · ipureintro; exact h
  · ipureintro; exact h.2
  · icombine H HeKR gives %Heq
    ipureintro; intro hn; subst hn; cases Heq
  · ipureintro; exact h.2
  · icombine H HeFR gives %Heq
    ipureintro; intro hn; subst hn; cases Heq
  · icombine H HeCT gives %Heq
    ipureintro; intro hn; subst hn; cases Heq
  · generalize hres : snapModel st o.rev = res at Hno
    cases res with
    | ok r m => exact absurd rfl (Hno r m)
    | notReady =>
      iunfold snapErr at Hse
      icombine Hse HeNR gives %Heq
      ipureintro; intro hn; subst hn; cases Heq
    | invalid =>
      iunfold snapErr at Hse
      icases Hse with %h
      ipureintro; obtain ⟨e, rfl⟩ := h; simp
    | future =>
      iunfold snapErr at Hse
      icombine Hse HeFR gives %Heq
      ipureintro; intro hn; subst hn; cases Heq
    | compacted =>
      iunfold snapErr at Hse
      icombine Hse HeCP gives %Heq
      ipureintro; intro hn; subst hn; cases Heq

end iris

end cachekv
end EtcdGrove
end Perennial
