/- Lean-first (no Rocq counterpart).

# `ReadAll`'s fold gives the restated post (pure; W3/W5 of `notes/wal-fsext-plan.md`)

The records `ReadAll` folds are the WAL's from its `p`-th segment on (`walReadFiles_running`); the
start `s` is the newest valid pair from the read position `cut` (`ReadAll`'s atomic premise). When
the fold succeeds (`readAllFold … = .ok r`), `r` is the read at the fixed base `s` from the position
`k` of segment `p` (`walReadAllOk`): from the first segment by `readAllFold_zero`; from a cut file by
`readAllFold_from` (`walReadFrom`) and `walReadAt_of_from`, `s` being newest from `k` too because the
fold matched a snapshot record of `s`'s index after `k` (`walNewestPair_suffix`). The bound
`k ≤ walOpenPos` (the name bound and the guard) is the caller's (`hpos`), given that record.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalReadAllPost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section ok
variable [GooseExts]

/-- The newest-pair fold's step (`walNewestPair`'s). -/
def npStep (acc : Option (w64 × w64)) (p : w64 × w64) : Option (w64 × w64) :=
  match acc with
  | none => some p
  | some q => if uint.nat q.1 ≤ uint.nat p.1 then some p else some q

theorem walNewestPair_eq (l : List (w64 × w64)) : walNewestPair l = l.foldl npStep none := rfl

theorem npStep_le {c : Option (w64 × w64)} {p : w64 × w64}
    (hc : ∀ q, c = some q → uint.nat q.1 ≤ uint.nat p.1) : npStep c p = some p := by
  cases c with
  | none => rfl
  | some q =>
    show (if uint.nat q.1 ≤ uint.nat p.1 then some p else some q) = some p
    rw [if_pos (hc q rfl)]

theorem npStep_bound {c : Option (w64 × w64)} {p x : w64 × w64} (hpx : uint.nat p.1 ≤ uint.nat x.1)
    (hc : ∀ q, c = some q → uint.nat q.1 ≤ uint.nat x.1) :
    ∀ r, npStep c p = some r → uint.nat r.1 ≤ uint.nat x.1 := by
  intro r hr
  cases c with
  | none => cases hr; exact hpx
  | some q' =>
    have hr' : (if uint.nat q'.1 ≤ uint.nat p.1 then some p else some q') = some r := hr
    by_cases h : uint.nat q'.1 ≤ uint.nat p.1
    · rw [if_pos h] at hr'; cases hr'; exact hpx
    · rw [if_neg h] at hr'; obtain rfl := Option.some.inj hr'; exact hc _ rfl

/-- The newest-pair fold from two accumulators agrees once the list reaches an index at least
both's. -/
theorem newestPair_fold_agree : ∀ (l : List (w64 × w64)) (a b : Option (w64 × w64)) (x : w64 × w64),
    x ∈ l → (∀ q, a = some q → uint.nat q.1 ≤ uint.nat x.1) →
    (∀ q, b = some q → uint.nat q.1 ≤ uint.nat x.1) →
    l.foldl npStep a = l.foldl npStep b
  | [], _, _, _, hx, _, _ => by cases hx
  | p :: l, a, b, x, hx, ha, hb => by
    simp only [List.foldl_cons]
    by_cases hboth : (∀ q, a = some q → uint.nat q.1 ≤ uint.nat p.1) ∧
        (∀ q, b = some q → uint.nat q.1 ≤ uint.nat p.1)
    · rw [npStep_le hboth.1, npStep_le hboth.2]
    · have hpx : uint.nat p.1 < uint.nat x.1 := by
        apply Nat.lt_of_not_le; intro hc
        apply hboth
        exact ⟨fun q hq => by have := ha q hq; omega, fun q hq => by have := hb q hq; omega⟩
      have hxl : x ∈ l := by
        rcases List.mem_cons.1 hx with rfl | h
        · omega
        · exact h
      exact newestPair_fold_agree l _ _ x hxl (npStep_bound (by omega) ha) (npStep_bound (by omega) hb)

/-- **The newest pair of a list, reached again in a suffix**: when the suffix holds a pair of the
newest's index, its newest pair is the list's. -/
theorem walNewestPair_suffix {l1 l2 : List (w64 × w64)} {s x : w64 × w64}
    (h : walNewestPair (l1 ++ l2) = some s) (hx : x ∈ l2) (hxs : x.1 = s.1) :
    walNewestPair l2 = some s := by
  have hmax := walNewestPair_max h
  rw [walNewestPair_eq] at h ⊢
  rw [List.foldl_append] at h
  rw [← h]
  symm
  apply newestPair_fold_agree l2 _ _ x hx
  · intro q hq
    rw [hxs]
    -- The accumulator after `l1` is one of `l1`'s pairs.
    have hm : walNewestPair l1 = some q := by rw [walNewestPair_eq]; exact hq
    exact hmax q (List.mem_append_left _ (walNewestPair_mem hm))
  · intro q hq; cases hq

/-- The valid pairs from a later position are a suffix of those from an earlier one. -/
theorem walValidSnaps_suffix (I : WalHist) {cut k : Nat} (hck : cut ≤ k) (hk : k ≠ 0) :
    ∃ l1, walValidSnaps I cut = l1 ++ walValidSnaps I k := by
  unfold walValidSnaps
  rw [if_neg hk, List.nil_append]
  have e : I.drop cut = (I.drop cut).take (k - cut) ++ I.drop k := by
    conv => lhs; rw [← List.take_append_drop (k - cut) (I.drop cut)]
    rw [List.drop_drop]; congr 2; omega
  rw [e, List.filterMap_append, ← List.append_assoc]
  exact ⟨_, rfl⟩

/-- **From the purged read to the fixed-base read** (the converse of `walReadAt_from_eq`): from a
cut file, with `s` the newest valid pair from there, the two folds agree on the hard state and the
entries. -/
theorem walReadAt_of_from {I : WalHist} {k : Nat} {s : w64 × w64} {σ : StorContents} (hk : k ≠ 0)
    (hs : some s = walNewestPair (walValidSnaps I k)) (h : walReadFrom I k = some σ) :
    ∃ σ', walReadAt I k s = some σ' ∧ σ'.hs = σ.hs ∧ σ'.ents = σ.ents := by
  have hnew := walNewest_eq_newestPair I hk
  rw [← hs] at hnew
  unfold walReadFrom at h
  simp only at h
  cases hN : walNewest ((I.drop k).filter (walKeep (uint.nat (walLastHS I).Commit'))) with
  | none => rw [hN] at hnew; cases hnew
  | some m =>
    rw [hN] at h
    rw [hN, Option.map_some, Option.some.injEq] at hnew
    subst hnew
    obtain ⟨σ', hf, e1, e2, -⟩ := walFoldChkFrom_congr _
      ⟨walLastHS (I.take k), some (SnapshotM.mk [] m), entryID.mk m.Term' m.Index', []⟩
      ⟨walLastHS (I.take k), none, entryID.mk m.Term' m.Index', []⟩ σ rfl rfl rfl h
    exact ⟨σ', hf, e1, e2⟩

theorem cut_le_length {I : WalHist} {b : Nat} (h : walCutPos I b) : b ≤ I.length := by
  rcases h with rfl | ⟨h, es, he, -⟩
  · exact Nat.zero_le _
  · have := (List.getElem?_eq_some_iff.1 he).1; omega

/-- **`ReadAll`'s fold, a success, gives the restated post** (see the file header). `I` the
history, `cuts` its cut positions, the read from segment `p` at position `k` (the first `p`
segments' length; not 0 for a cut file: `hk0`), at or after the read position `cut`. -/
theorem readAll_ok_pure {C : WalCodec} {M : WalMarshal} {U : WalUnmarshal} (hU : U.Ok M)
    (md : List w8) (I : WalHist) (cuts : List Nat) (p cut : Nat) (s : w64 × w64) (stop : WalStop)
    (r : List w8 × HardStateM × List EntryM)
    (hcuts : (∀ b ∈ cuts, walCutPos I b) ∧ cuts.Pairwise (· < ·))
    (hp : p ≤ cuts.length)
    (hcut : cut ≤ ((segsOf I cuts).take p).flatten.length)
    (hk0 : 0 < p → ((segsOf I cuts).take p).flatten ≠ [])
    (hpos : (0 < p → ∃ m, WalOpG.snap m ∈ I.drop ((segsOf I cuts).take p).flatten.length ∧
        m.Index' = s.1) →
      ((segsOf I cuts).take p).flatten.length ≤ walOpenPos I s.1)
    (hs : some s = walNewestPair (walValidSnaps I cut))
    (hok : readAllFold U s true ((recsOfSegs C M md (segsOf I cuts)).drop
      (recsOfSegs C M md ((segsOf I cuts).take p)).length) stop = .ok r) :
    ∃ σ, walReadAllOk I cut s σ ∧ r = (md, σ.hs, σ.ents) := by
  have hflat : (segsOf I cuts).flatten = I :=
    segsOf_flatten I cuts (hcuts.2.imp Nat.le_of_lt) (fun c hc => cut_le_length (hcuts.1 c hc))
  generalize hSs : segsOf I cuts = Ss at *
  have hSsl : Ss.length = cuts.length + 1 := by rw [← hSs]; simp [segsOf]
  generalize hk : (Ss.take p).flatten.length = k at *
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · -- From the first file.
    subst hp0
    simp only [List.take_zero, List.flatten_nil, List.length_nil] at hk
    subst hk
    have hc0 : cut = 0 := by omega
    subst hc0
    simp only [List.take_zero, recsOfSegs, segsDs, List.flatten_nil, chainRecs, List.length_nil,
      List.drop_zero] at hok
    rw [← hflat] at hs
    obtain ⟨σ, hσ, hr⟩ := readAllFold_zero hU md Ss s true stop r hs hok
    rw [hflat] at hσ hs
    exact ⟨σ, ⟨0, Nat.le_refl _, Nat.zero_le _, hs, hσ⟩, hr⟩
  · have hSne : Ss.take p ≠ [] := by
      intro h; rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · rw [h] at hSsl; simp at hSsl
    have hsplit : Ss = Ss.take p ++ Ss.drop p := (List.take_append_drop p Ss).symm
    have hkne : k ≠ 0 := by
      intro h0; rw [← hk] at h0; exact hk0 hp0 (List.eq_nil_of_length_eq_zero h0)
    have hdrop : (Ss.drop p).flatten = I.drop k := by
      have := flatten_append_drop (Spre := Ss.take p) (Ss := Ss.drop p)
      rw [← hsplit] at this
      rw [← hflat, ← hk, this]
    have hok' : readAllFold U s true
        ((recsOfSegs C M md (Ss.take p ++ Ss.drop p)).drop (recsOfSegs C M md (Ss.take p)).length)
        stop = .ok r := by rw [← hsplit]; exact hok
    -- The fold matched a snapshot record of `s`'s index after `k`.
    obtain ⟨hc, hle⟩ := validSnaps_bounds hs
    obtain ⟨st, hfold, hm, -⟩ := readAllFold_ok hok'
    rw [recsOfSegs_drop_map C M md hSne] at hfold
    have hle' : ∀ m, WalOpG.snap m ∈ (Ss.drop p).flatten →
        uint.nat m.Index' ≤ uint.nat (walLastHS I).Commit' → uint.nat m.Index' ≤ uint.nat s.1 := by
      intro m hm hmc
      rw [hdrop] at hm
      apply hle m _ hmc
      have e : I.drop cut = (I.drop cut).take (k - cut) ++ I.drop k := by
        conv => lhs; rw [← List.take_append_drop (k - cut) (I.drop cut)]
        rw [List.drop_drop]; congr 2; omega
      rw [e]; exact List.mem_append_right _ hm
    obtain ⟨σ1, -, -, -, hmatch⟩ := raStep_segs_ok U M hU s md _ hc (Ss.drop p) (Ss.take p).flatten
      raInit st ⟨walLastHS (Ss.take p).flatten, none, entryID.mk s.2 s.1, []⟩
      rfl rfl rfl (Or.inr rfl) (Or.inl rfl) hle' hfold
    rw [hm] at hmatch
    simp only [raInit, Bool.false_or] at hmatch
    obtain ⟨o, ho, hos⟩ := List.any_eq_true.1 hmatch.symm
    cases o with
    | save _ _ => simp [snapAt] at hos
    | snap m =>
      simp only [snapAt, decide_eq_true_eq] at hos
      rw [hdrop] at ho
      -- `s` is the newest valid pair from `k` too.
      have hsk : some s = walNewestPair (walValidSnaps I k) := by
        obtain ⟨l1, hl1⟩ := walValidSnaps_suffix I hcut hkne
        rw [hl1] at hs
        symm
        apply walNewestPair_suffix hs.symm (x := (m.Index', m.Term')) _ hos
        unfold walValidSnaps
        rw [if_neg hkne, List.nil_append]
        apply List.mem_filterMap.2 ⟨WalOpG.snap m, ho, ?_⟩
        simp only
        rw [if_pos (by rw [hos]; exact hc)]
      have hsk' : some s = walNewestPair (walValidSnaps (Ss.take p ++ Ss.drop p).flatten
          (Ss.take p).flatten.length) := by
        rw [← hsplit, hflat, hk]; exact hsk
      obtain ⟨σ, hσ, hr⟩ := readAllFold_from hU md (Ss.take p) (Ss.drop p) (hk0 hp0) s true stop r
        hsk' hok'
      rw [← hsplit, hflat, hk] at hσ
      obtain ⟨σ', hσ', e1, e2⟩ := walReadAt_of_from hkne hsk hσ
      refine ⟨σ', ⟨k, hcut, hpos (fun _ => ⟨m, ho, hos⟩), hsk, hσ'⟩, ?_⟩
      rw [hr, e1, e2]

end ok

end WalFs
end EtcdGrove
end Perennial
