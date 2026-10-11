/-
Lemmas of the STM's reads (`stm.fetch`, `stm.Get`, `stm.Rev`, `stmSerializable.Get`,
`stmSerializable.Rev`): the gets of a read (`OpGet(k, getOpts...)` for `ReadOptsOk` options) are
single-key gets, the read set's growth (`readsAdd`), and a choice of the reads of a read
transaction's responses. Lean-first (no Rocq counterpart); see `InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

/-! ## A read's get -/

theorem readOp_fields (k : GoString) (gs : List (OpFull → OpFull)) (h : ReadOptsOk gs) :
    (opGetModel k gs).t = W64 1 ∧ (opGetModel k gs).key = k ∧
    (opGetModel k gs).base.rangeEnd = [] ∧ (opGetModel k gs).effSortOrder = W64 0 ∧
    (opGetModel k gs).base.limit = W64 0 ∧ (opGetModel k gs).base.countOnly = false ∧
    (opGetModel k gs).keysOnly = false ∧ (opGetModel k gs).base.minModRev = W64 0 ∧
    (opGetModel k gs).base.maxModRev = W64 0 ∧ (opGetModel k gs).base.minCreateRev = W64 0 ∧
    (opGetModel k gs).base.maxCreateRev = W64 0 := by
  rcases h with rfl | rfl | ⟨S, rfl⟩ <;>
    simp [opGetModel, opFold, withRevM, withSerializableM, OpFull.getInit, OpFull.newOp,
      OpModel.zero, OpFull.effSortOrder]

theorem readOp_not_panics (gs : List (OpFull → OpFull)) (h : ReadOptsOk gs) :
    ¬ opGetPanics gs := by
  rcases h with rfl | rfl | ⟨S, rfl⟩ <;>
    simp [opGetPanics, opFold, withRevM, withSerializableM, OpFull.newOp, OpModel.zero]

theorem readOp_ok (pfx k : GoString) (gs : List (OpFull → OpFull)) (h : ReadOptsOk gs)
    (hk : pfx <+: k) : readOpOk pfx (opGetModel k gs) := by
  obtain ⟨ht, hkey, he, -⟩ := readOp_fields k gs h
  refine ⟨ht, ?_⟩
  rw [hkey, he]
  exact keyRangeUnder_key pfx k hk

/-- In a state with sorted keys, the key-values of `k` are its `kvAt`. -/
theorem filter_key_kvAt (s : List EtcdKv) (hs : (s.map EtcdKv.key).Pairwise go.GoStringLt)
    (k : GoString) : s.filter (fun v => decide (v.key = k)) = (kvAt s k).toList := by
  unfold kvAt
  induction s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.pairwise_cons] at hs
    by_cases hx : x.key = k
    · rw [List.filter_cons_of_pos (by simpa using hx), List.find?_cons_of_pos (by simpa using hx)]
      simp only [Option.toList_some, List.cons.injEq, true_and]
      rw [List.filter_eq_nil_iff]
      intro w hw hwk
      have := hs.1 w.key (List.mem_map_of_mem hw)
      rw [hx, show w.key = k by simpa using hwk] at this
      exact goStringLt_irrefl _ this
    · rw [List.filter_cons_of_neg (by simpa using hx), List.find?_cons_of_neg (by simpa using hx)]
      exact ih hs.2

/-- **A read's get** answers the key's key-value, if present, and nothing otherwise. -/
theorem readOp_kvs (pfx k : GoString) (gs : List (OpFull → OpFull)) (h : ReadOptsOk gs)
    (s kvs : List EtcdKv) (hwf : EtcdStateWf pfx s)
    (hk : rangeKvsOk (opGetModel k gs) (rangeSel s (opGetModel k gs)) kvs) :
    kvs = (kvAt s k).toList := by
  obtain ⟨-, hkey, he, hso, hl, hc, hko, h1, h2, h3, h4⟩ := readOp_fields k gs h
  have hsel : rangeSel s (opGetModel k gs) = (kvAt s k).toList := by
    unfold rangeSel rangeIn
    rw [← filter_key_kvAt s hwf.1 k, List.filter_filter]
    apply List.filter_congr
    intro v _
    rw [kvFilterOk_zero _ v h1 h2 h3 h4, hkey, he]
    simp [inRange]
  obtain ⟨l, hperm, hl0, -, -, rfl⟩ := hk
  rw [hl0 hso, hsel]
  simp [hc, hl, hko]

/-- `fetch`'s loop fills the operations slice from the front. -/
theorem set_append_replicate {A : Type} (vs : List A) (z a : A) (N : Nat) (h : vs.length < N) :
    (vs ++ List.replicate (N - vs.length) z).set vs.length a =
      (vs ++ [a]) ++ List.replicate (N - (vs ++ [a]).length) z := by
  obtain ⟨m, hm⟩ : ∃ m, N - vs.length = m + 1 := ⟨N - vs.length - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_append_right _ _ (by omega)]
  simp only [Nat.sub_self, List.set_cons_zero, List.length_append, List.length_singleton,
    List.append_assoc, List.singleton_append]
  congr 3
  omega

/-! ## The read set's growth -/

theorem readsAdd_notin (reads : GMap GoString ReadM) (l : List (GoString × ReadM)) (k : GoString)
    (hk : ∀ e, (k, e) ∉ l) : readsAdd reads l !! k = reads !! k := by
  induction l generalizing reads with
  | nil => rfl
  | cons ke l ih =>
    unfold readsAdd at *
    rw [List.foldl_cons, ih _ (fun e he => hk e (List.mem_cons_of_mem _ he))]
    have : ke.1 ≠ k := by
      intro h; exact hk ke.2 (by rw [← h]; exact List.mem_cons_self)
    exact GMap.lookup_insert_ne _ _ this

theorem readsAdd_some (reads : GMap GoString ReadM) (l : List (GoString × ReadM)) (k : GoString)
    (e : ReadM) (h : readsAdd reads l !! k = some e) : reads !! k = some e ∨ (k, e) ∈ l := by
  induction l generalizing reads with
  | nil => exact Or.inl h
  | cons ke l ih =>
    unfold readsAdd at h
    rw [List.foldl_cons] at h
    rcases ih _ h with h' | h'
    · rw [GMap.lookup_insert_eq_iff] at h'
      split at h'
      · rename_i hk; subst hk; cases h'; exact Or.inr List.mem_cons_self
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem readsAdd_mem (reads : GMap GoString ReadM) (l : List (GoString × ReadM)) (k : GoString)
    (e0 : ReadM) (hk : (k, e0) ∈ l) : ∃ e, readsAdd reads l !! k = some e ∧ (k, e) ∈ l := by
  induction l generalizing reads e0 with
  | nil => simp at hk
  | cons ke l ih =>
    unfold readsAdd
    rw [List.foldl_cons]
    by_cases hl : ∃ e, (k, e) ∈ l
    · obtain ⟨e1, he1⟩ := hl
      obtain ⟨e, h1, h2⟩ := ih (GMap.insert ke.1 ke.2 reads) e1 he1
      exact ⟨e, h1, List.mem_cons_of_mem _ h2⟩
    · have hke : ke = (k, e0) := by
        rcases List.mem_cons.1 hk with h | h
        · exact h.symm
        · exact absurd ⟨e0, h⟩ hl
      subst hke
      refine ⟨e0, ?_, List.mem_cons_self⟩
      have := readsAdd_notin (GMap.insert k e0 reads) l k (fun e he => hl ⟨e, he⟩)
      unfold readsAdd at this
      rw [this]
      exact GMap.lookup_insert _ _ _

/-- A read transaction's reads of keys none of which was read grow the reads. -/
theorem readsAdd_grow (reads : GMap GoString ReadM) (ks : List GoString) (es : List ReadM)
    (hnone : ∀ k ∈ ks, reads !! k = none) :
    ReadsGrow reads (readsAdd reads (ks.zip es)) ks := by
  constructor
  · intro k e he
    by_cases hk : ∃ e', (k, e') ∈ ks.zip es
    · obtain ⟨e', he'⟩ := hk
      rw [hnone k (List.of_mem_zip he').1] at he; cases he
    · rw [readsAdd_notin _ _ _ (fun e' he' => hk ⟨e', he'⟩)]; exact he
  · intro k hk
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hk
    rcases readsAdd_some _ _ _ _ he with h | h
    · left; rw [h]; rfl
    · right; exact (List.of_mem_zip h).1

/-! ## `stmSerializable.Get`'s moves of prefetched reads -/

/-- After moving the prefetched reads of the first `n` keys of `ks` (none written): `pre'` and
`reads'` are `pre` and the reads elsewhere, `pre'` has none of those keys, and every read
stays. -/
def MoveInv (st : STMSt) (pre : GMap GoString ReadM) (ks : List GoString) (n : Nat)
    (reads' pre' : GMap GoString ReadM) : Prop :=
  (∀ k, k ∉ ks.take n → pre' !! k = pre !! k ∧ reads' !! k = st.reads !! k) ∧
  (∀ k ∈ ks.take n, pre' !! k = none) ∧
  (∀ k e, st.reads !! k = some e → reads' !! k = some e)

theorem MoveInv_init (st : STMSt) (pre : GMap GoString ReadM) (ks : List GoString) :
    MoveInv st pre ks 0 st.reads pre :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun k hk => by simp at hk, fun _ _ h => h⟩

theorem MoveInv_found (st : STMSt) (pre : GMap GoString ReadM) (ks : List GoString) (n : Nat)
    (reads' pre' : GMap GoString ReadM) (k : GoString) (e : ReadM)
    (hinv : MoveInv st pre ks n reads' pre') (hk : ks[n]? = some k) (he : pre' !! k = some e)
    (hok : PreOk st pre) (hnw : st.writes !! k = none) :
    MoveInv st pre ks (n + 1) (GMap.insert k e reads') (GMap.delete k pre') := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have hkn : k ∉ ks.take n := fun h => by rw [h2 k h] at he; cases he
  have hrk : st.reads !! k = none := by
    cases hr : st.reads !! k with
    | none => rfl
    | some _ =>
      have := hok k (by rw [hr]; rfl) (by rw [← (h1 k hkn).1, he]; rfl)
      rw [hnw] at this; cases this
  have htake : ∀ k', k' ∈ ks.take (n + 1) ↔ k' ∈ ks.take n ∨ k' = k := by
    intro k'; rw [List.take_add_one, hk]; simp
  refine ⟨fun k' hk' => ?_, fun k' hk' => ?_, fun k' e' he' => ?_⟩
  · have hne : k ≠ k' := fun h => hk' ((htake k').2 (Or.inr h.symm))
    rw [GMap.lookup_delete_ne _ hne, GMap.lookup_insert_ne _ _ hne]
    exact h1 k' (fun h => hk' ((htake k').2 (Or.inl h)))
  · rcases (htake k').1 hk' with h | rfl
    · by_cases hne : k = k'
      · subst hne; exact GMap.lookup_delete _ _
      · rw [GMap.lookup_delete_ne _ hne]; exact h2 k' h
    · exact GMap.lookup_delete _ _
  · by_cases hne : k = k'
    · subst hne; rw [hrk] at he'; cases he'
    · rw [GMap.lookup_insert_ne _ _ hne]; exact h3 k' e' he'

theorem MoveInv_notfound (st : STMSt) (pre : GMap GoString ReadM) (ks : List GoString) (n : Nat)
    (reads' pre' : GMap GoString ReadM) (k : GoString)
    (hinv : MoveInv st pre ks n reads' pre') (hk : ks[n]? = some k) (he : pre' !! k = none) :
    MoveInv st pre ks (n + 1) reads' pre' := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have htake : ∀ k', k' ∈ ks.take (n + 1) ↔ k' ∈ ks.take n ∨ k' = k := by
    intro k'; rw [List.take_add_one, hk]; simp
  refine ⟨fun k' hk' => h1 k' (fun h => hk' ((htake k').2 (Or.inl h))), fun k' hk' => ?_, h3⟩
  rcases (htake k').1 hk' with h | rfl
  · exact h2 k' h
  · exact he

/-- After the moves and `fetch`: the reads grow by `ks` and `PreOk` holds. -/
theorem MoveInv_final (st : STMSt) (pre : GMap GoString ReadM) (ks : List GoString)
    (reads' pre' reads'' : GMap GoString ReadM) (hinv : MoveInv st pre ks ks.length reads' pre')
    (hok : PreOk st pre) (hg : ReadsGrow reads' reads'' ks) :
    ReadsGrow st.reads reads'' ks ∧ PreOk { reads := reads'', writes := st.writes } pre' := by
  obtain ⟨h1, h2, h3⟩ := hinv
  rw [List.take_length] at h1 h2
  refine ⟨⟨fun k e he => hg.1 k e (h3 k e he), fun k hk => ?_⟩, fun k hr hp => ?_⟩
  · rcases hg.2 k hk with h | h
    · by_cases hks : k ∈ ks
      · exact Or.inr hks
      · left; rw [← (h1 k hks).2]; exact h
    · exact Or.inr h
  · by_cases hks : k ∈ ks
    · rw [h2 k hks] at hp; cases hp
    · rcases hg.2 k hr with h | h
      · rw [(h1 k hks).2] at h
        rw [(h1 k hks).1] at hp
        exact hok k h hp
      · exact absurd h hks

/-! ## Choosing the reads of a read transaction's responses -/

section choice
variable {GF : BundledGFunctors}

/-- A persistent fact of each element of `l`, holding for some `b`, holds for a list of
them. -/
theorem iChoice {A B : Type} (Q : A → B → IProp GF) (l : List A) :
    (□ ∀ (i : Nat) (a : A), ⌜l[i]? = some a⌝ -∗ ∃ b, Q a b) ⊢
      ∃ bs : List B, ⌜bs.length = l.length⌝ ∗
        □ ∀ (i : Nat) (a : A) (b : B), ⌜l[i]? = some a⌝ -∗ ⌜bs[i]? = some b⌝ -∗ Q a b := by
  induction l with
  | nil =>
    iintro #H
    iexists []
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %a %b %Ha %Hb
    simp at Ha
  | cons a0 l ih =>
    iintro #H
    ihave ⟨%b0, #Hb0⟩ := H $$ %0 %a0 %rfl
    ihave #H' : iprop(□ ∀ (i : Nat) (a : A), ⌜l[i]? = some a⌝ -∗ ∃ b, Q a b) $$ []
    · imodintro
      iintro %i %a %Ha
      iapply H $$ %(i + 1) %a
      ipureintro; simpa using Ha
    ihave ⟨%bs, %Hl, #Hbs⟩ := ih $$ H'
    iexists b0 :: bs
    isplitr
    · ipureintro; simp [Hl]
    imodintro
    iintro %i %a %b %Ha %Hb
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Ha Hb
      subst Ha Hb
      iexact Hb0
    · simp only [List.getElem?_cons_succ] at Ha Hb
      iapply Hbs $$ %i %a %b %Ha %Hb

end choice

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A read transaction's response of a read's get** (on etcd's state `s` at `R`) is a read of
the key at `R`. -/
theorem respOpRead_of (pfx k : GoString) (gs : List (OpFull → OpFull)) (h : ReadOptsOk gs)
    (hk : pfx <+: k) (R : w64) (s : List EtcdKv) (n : Nat) (p : Loc) (hwf : EtcdStateWf pfx s) :
    □ etcdState (GF := GF) R pfx s ∗
      txnOpRespAt p (.get (opGetModel k gs)) (.range (rangeSel s (opGetModel k gs)) n) ⊢
    ∃ e : ReadM, ⌜e.rev = R⌝ ∗ respOpReadAt pfx k p e := by
  iintro ⟨#Hs, Hp⟩
  unfold txnOpRespAt
  icases Hp with ⟨%Hpn, %u, #Hu, %w, %rr, %Huw, #Hw, %Hrrn, #Hrr⟩
  subst Huw
  unfold rangeRespAt
  icases Hrr with ⟨%sl, %ps, %kvs, #HK, #Hps, #Hkv, %Hok, -, %hh, %hr, #Hh, %Hhn, #Hhr⟩
  have Hkvs := readOp_kvs pfx k gs h s kvs hwf Hok
  subst Hkvs
  iexists ({ hdr := hr, rev := R, kv := kvAt s k } : ReadM)
  isplitr
  · ipureintro; rfl
  unfold respOpReadAt
  isplitr
  · ipureintro; exact Hpn
  iexists w, rr
  iframe Hu Hw
  unfold readRespAt
  isplitr
  · ipureintro; exact Hrrn
  isplitr
  · unfold readFact
    iexists s
    iframe Hs
    ipureintro; exact ⟨hwf, rfl, hk⟩
  isplitr
  · iexists hh
    iframe Hh Hhr
    ipureintro; exact Hhn
  iexists sl, ps
  iframe HK Hps Hkv

/-- Two reads of a key at one revision read the same key-value. -/
theorem readFact_agree (pfx k : GoString) (e e' : ReadM) (h : e.rev = e'.rev) :
    readFact (GF := GF) pfx k e ∗ readFact pfx k e' ⊢ ⌜e.kv = e'.kv⌝ := by
  obtain ⟨h1, r, kv1⟩ := e
  obtain ⟨h2, r', kv2⟩ := e'
  simp only at h
  subst h
  unfold readFact
  iintro ⟨⟨%s, #Hs, %Hs1⟩, ⟨%s', #Hs', %Hs2⟩⟩
  ihave %Heq := etcdState_agree _ _ _ _ $$ [Hs Hs']
  · isplitl [Hs]
    · iexact Hs
    · iexact Hs'
  ipureintro
  simp only at Hs1 Hs2 ⊢
  rw [← Hs1.2.1, ← Hs2.2.1, Heq]

theorem respOpRead_fact (pfx k : GoString) (p : Loc) (e : ReadM) :
    respOpReadAt (GF := GF) pfx k p e ⊢ readFact pfx k e := by
  unfold respOpReadAt readRespAt
  iintro ⟨-, %w, %rr, -, -, -, #H, -⟩
  iexact H

theorem readsAt_insert_rd (pfx k : GoString) (rsMap : GMap GoString Loc) (reads : GMap GoString ReadM)
    (p : Loc) (e : ReadM) :
    readsAt (GF := GF) pfx rsMap reads ∗ readRespAt pfx k p e ⊢
      readsAt pfx (GMap.insert k p rsMap) (GMap.insert k e reads) := by
  unfold readsAt
  iintro ⟨⟨%Hdom, #Hall⟩, #He⟩
  isplitr
  · ipureintro; intro k'
    rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]
    split
    · rfl
    · exact Hdom k'
  imodintro
  iintro %k' %p' %e' %Hp %He'
  rw [GMap.lookup_insert_eq_iff] at Hp He'
  split at Hp
  · rename_i h; subst h
    simp only [↓reduceIte, Option.some.injEq] at Hp He'
    subst Hp He'
    iexact He
  · rename_i h
    simp only [h, ↓reduceIte] at He'
    iapply Hall $$ %k' %p' %e' %Hp %He'

theorem readsAt_delete (pfx k : GoString) (rsMap : GMap GoString Loc) (reads : GMap GoString ReadM) :
    readsAt (GF := GF) pfx rsMap reads ⊢
      readsAt pfx (GMap.delete k rsMap) (GMap.delete k reads) := by
  unfold readsAt
  iintro ⟨%Hdom, #Hall⟩
  isplitr
  · ipureintro; intro k'
    rw [GMap.lookup_delete_iff, GMap.lookup_delete_iff]
    split
    · rfl
    · exact Hdom k'
  imodintro
  iintro %k' %p' %e' %Hp %He'
  rw [GMap.lookup_delete_iff] at Hp He'
  split at Hp
  · cases Hp
  · rename_i h
    simp only [h, ↓reduceIte] at He'
    iapply Hall $$ %k' %p' %e' %Hp %He'

end resp

end concurrency
end EtcdGrove
end Perennial
