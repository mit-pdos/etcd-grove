/- Lean-first (no Rocq counterpart).

# A purge's removal: the WAL's pure facts after it (unit `locks`, session 8; `notes/wal-units/locks.md`)

Pure. The purge's `os.Remove(dir/bt)` of the first named segment `g0` of the WAL `dir` (not its last) logs,
on the WAL directory's claim `(j, except X, h)`, the unlink at `x`; the claim's names after it are `c` (the
directory without `bt`). The WAL becomes `walPurgeD d lay p` (`pur` raised to `p`, `cut` at the next
segment's start), its layout `purgeLayP lay g0` (`purgeLay`, `g0` among this generation's removed
segments). Here:

* `walNames_delete`, `walInos_delete_first`: the directory without its first `.wal` file's name lists the
  other files;
* `walFullOk_purge`: the full layout's condition (`WalFullOk`) after the removal: the full layout does not
  move (`unpurge_purgeLayP`), its static relation with `pur` raised, its crash condition by
  `crashOkA_purgeF` (from `DirKeysOk`'s, no cut pending), the zeros known past the segments before the last
  (`g0` was one, `hzf0`);
* `crashOkA_purge_other`, `crashOkW_purge_other`: another WAL's crash condition over the logged claim (a
  crash keeping the removal is one of the claims before it, `bt` set back, which neither its directory nor
  its area directory sees).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeStep
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeFull
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommitPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## The layout after the removal -/

/-- **The layout after a purge removed its first named segment `g0`**: `purgeLay`, `g0` appended to the
segments removed this generation. -/
def purgeLayP (lay : WalLay) (g0 : SegG) : WalLay := { purgeLay lay with pg := lay.pg ++ [g0] }

@[simp] theorem purgeLayP_pg (lay : WalLay) (g0 : SegG) : (purgeLayP lay g0).pg = lay.pg ++ [g0] := rfl
@[simp] theorem purgeLayP_segs (lay : WalLay) (g0 : SegG) : (purgeLayP lay g0).segs = lay.segs.tail := rfl
@[simp] theorem purgeLayP_first (lay : WalLay) (g0 : SegG) :
    (purgeLayP lay g0).first = lay.first + 1 := rfl
@[simp] theorem purgeLayP_cuts (lay : WalLay) (g0 : SegG) : (purgeLayP lay g0).cuts = lay.cuts := rfl
@[simp] theorem purgeLayP_j (lay : WalLay) (g0 : SegG) : (purgeLayP lay g0).j = lay.j := rfl
@[simp] theorem purgeLayP_jr (lay : WalLay) (g0 : SegG) : (purgeLayP lay g0).jr = lay.jr := rfl
@[simp] theorem purgeLayP_nm (lay : WalLay) (g0 : SegG) : (purgeLayP lay g0).nm = lay.nm := rfl

/-- **The full layout does not move.** -/
theorem unpurge_purgeLayP {lay : WalLay} {g0 : SegG} {gs : List SegG} (hs : lay.segs = g0 :: gs)
    (hf : lay.pg.length ≤ lay.first) :
    unpurge (purgeLayP lay g0).pg (purgeLayP lay g0) = unpurge lay.pg lay := by
  cases lay
  simp only [unpurge, purgeLayP, purgeLay] at hs hf ⊢
  subst hs
  simp only [List.length_append, List.length_singleton, List.tail_cons, List.append_assoc,
    List.singleton_append, WalLay.mk.injEq, and_true, true_and]
  omega

theorem walFullD_purgeLayP (d : WalDur) (lay : WalLay) (g0 : SegG) (p : Nat)
    (hf : lay.pg.length ≤ lay.first) :
    walFullD (walPurgeD d lay p) (purgeLayP lay g0).pg (purgeLayP lay g0) =
      { walFullD d lay.pg lay with pur := max d.pur p } := by
  simp only [walFullD, walPurgeD, purgeLayP, purgeLay, List.length_append, List.length_singleton]
  congr 2; omega

/-- **The static relation after the removal**, the directory's `.wal` files the other segments'. -/
theorem walAbsD_purgeP {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents ents' : Ents}
    {g0 : SegG} {p : Nat} (h : WalAbsD C Mr d lay ents) (hl : 1 < lay.segs.length)
    (hp : segStart lay.cuts (lay.first + 1) ≤ p) (hn : walInos ents' = lay.segs.tail.map (·.ino)) :
    WalAbsD C Mr (walPurgeD d lay p) (purgeLayP lay g0) ents' :=
  (walAbsD_purge h hl hp hn).setPg (lay.pg ++ [g0])

/-! ## The directory without its first `.wal` name -/

private theorem leS_trans : ∀ a b c : GoString, decide (go.GoStringLt a b ∨ a = b) = true →
    decide (go.GoStringLt b c ∨ b = c) = true → decide (go.GoStringLt a c ∨ a = c) = true := by
  intro a b c h1 h2
  simp only [decide_eq_true_eq] at h1 h2 ⊢
  rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
  · exact Or.inl (go.goStringLt_trans h1 h2)
  · exact Or.inl h1
  · exact Or.inl h2
  · exact Or.inr rfl

private theorem leS_total : ∀ a b : GoString,
    (decide (go.GoStringLt a b ∨ a = b) || decide (go.GoStringLt b a ∨ b = a)) = true := by
  intro a b
  by_cases h1 : go.GoStringLt a b
  · simp [h1]
  by_cases h2 : go.GoStringLt b a
  · simp [h2]
  simp [go.goStringLt_eq_of_not_lt h1 h2]

theorem walNames_sorted (E : Ents) :
    (walNames E).Pairwise (fun a b => decide (go.GoStringLt a b ∨ a = b) = true) :=
  List.pairwise_mergeSort leS_trans leS_total _

theorem mem_walNames_iff {E : Ents} {c : GoString} :
    c ∈ walNames E ↔ walNameP c = true ∧ ∃ e, E !! c = some e := by
  unfold walNames
  rw [List.mem_mergeSort, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨⟨c', v⟩, hm, rfl⟩, hw⟩
    exact ⟨hw, v, (GMap.mem_toList _ _ _).1 hm⟩
  · rintro ⟨hw, v, hv⟩
    exact ⟨⟨(c, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩, hw⟩

/-- **The `.wal` names without one**: the sorted names with it erased. -/
theorem walNames_delete (E : Ents) (b : GoString) :
    walNames (GMap.delete b E) = (walNames E).erase b := by
  refine List.Perm.eq_of_pairwise (le := fun a b => decide (go.GoStringLt a b ∨ a = b) = true) ?_
    (walNames_sorted _) ((walNames_sorted E).sublist (List.erase_sublist ..)) ?_
  · intro a c _ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h2 (go.goStringLt_asymm h1)
      · exact h2.symm
    · exact h1
  · refine (List.perm_ext_iff_of_nodup (walNames_nodup _) ((walNames_nodup E).erase _)).2
      (fun c => ?_)
    rw [(walNames_nodup E).mem_erase_iff, mem_walNames_iff, mem_walNames_iff]
    by_cases hc : c = b
    · subst hc; simp [GMap.lookup_delete]
    · rw [GMap.lookup_delete_ne _ (Ne.symm hc)]; simp [hc]

/-- The file a name of `E` holds, if any. -/
def insOf (E : Ents) (c : GoString) : Option Ino :=
  match E !! c with
  | some (.file i) => some i
  | _ => none

theorem walInos_insOf (E : Ents) : walInos E = (walNames E).filterMap (insOf E) := rfl

/-- Erasing from a list whose file list starts with `i` the name of `i`, nodup: the rest. -/
theorem filterMap_erase_first {f : GoString → Option Ino} {A B : List GoString} {i : Ino}
    {is : List Ino} (hw : A.filterMap f ++ i :: B.filterMap f = i :: is) (hnd : (i :: is).Nodup) :
    A.filterMap f ++ B.filterMap f = is := by
  cases hA : A.filterMap f with
  | nil =>
    rw [hA] at hw
    simp only [List.nil_append, List.cons.injEq] at hw ⊢
    exact hw.2
  | cons a A' =>
    rw [hA] at hw
    simp only [List.cons_append, List.cons.injEq] at hw
    obtain ⟨rfl, hw⟩ := hw
    exfalso
    have : a ∈ is := by rw [← hw]; simp
    exact (List.nodup_cons.1 hnd).1 this

/-- **The directory without its first `.wal` file's name lists the other files.** -/
theorem walInos_delete_first {E : Ents} {b : GoString} {i : Ino} {is : List Ino}
    (hb : walNameP b = true) (he : E !! b = some (.file i)) (hw : walInos E = i :: is)
    (hnd : (i :: is).Nodup) : walInos (GMap.delete b E) = is := by
  have hmem : b ∈ walNames E := mem_walNames hb he
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hmem
  have hndN := walNames_nodup E
  rw [hAB] at hndN
  have hbA : b ∉ A := fun h => by
    have := List.nodup_append.1 hndN
    exact this.2.2 b h b (List.mem_cons_self ..) rfl
  have herase : (A ++ b :: B).erase b = A ++ B := by
    rw [List.erase_append_right _ hbA, List.erase_cons_head]
  rw [walInos_insOf] at hw ⊢
  rw [walNames_delete, hAB, herase]
  rw [filterMap_congr' (g := insOf E) (fun c hc => by
    have hcb : c ≠ b := by
      intro e; subst e
      rcases List.mem_append.1 hc with h | h
      · exact hbA h
      · exact (List.nodup_cons.1 (List.nodup_append.1 hndN).2.1).1 h
    unfold insOf
    rw [GMap.lookup_delete_ne _ (Ne.symm hcb)])]
  have hib : insOf E b = some i := by unfold insOf; rw [he]
  rw [hAB, List.filterMap_append, List.filterMap_cons, hib] at hw
  rw [List.filterMap_append]
  exact filterMap_erase_first hw hnd

/-! ## The full layout's condition after the removal -/

/-- **The full layout's crash condition after the removal** (no alternative: `DirKeysOk`'s, no cut
pending), from the old one (`crashOkA_purgeF`; the premises as `walFullOk_purge`'s). -/
theorem crashOkA_full_purge {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {g0 : SegG} {gs : List SegG} {cl : List Claim} {n : Nat} {X : List GoString} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString} {p : Nat}
    (hok : WalFullOk C Mr d lay cl n)
    (hcr : CrashOkA C Mr (walFullD d lay.pg lay) (unpurge lay.pg lay) none cl n)
    (habs : WalAbsD C Mr d lay h.cur) (hnd : ((lay.pg ++ lay.segs).map (·.ino)).Nodup)
    (hs : lay.segs = g0 :: gs) (hgs : gs ≠ []) (hp : segStart lay.cuts (lay.first + 1) ≤ p)
    (hX : ∀ b ∈ X, walNameP b = false)
    (hcl : (lay.j, NameSet.except X, h) ∈ cl) (hcoh : ClaimCoh h lay.j (.except X))
    (hcoh' : ClaimCoh (h.log x e c) lay.j (.except X)) (hst : h.next ≤ e.start)
    (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, h) → c'.1 = lay.j → ¬ c'.2.1.Mem bt)
    (hcur0 : h.cur !! bt = some (.file g0.ino)) (hwal' : walInos c = gs.map (·.ino)) :
    CrashOkA C Mr (walFullD (walPurgeD d lay p) (purgeLayP lay g0).pg (purgeLayP lay g0))
      (unpurge (purgeLayP lay g0).pg (purgeLayP lay g0)) none
      (replClaim (lay.j, NameSet.except X, h) (lay.j, NameSet.except X, h.log x e c) cl) n := by
  obtain ⟨⟨e0, hF⟩, -, hz⟩ := hok
  have hf := pg_le_first habs hF
  have hdl : lay.segs.dropLast = g0 :: gs.dropLast := by
    rw [hs]
    cases gs with
    | nil => exact absurd rfl hgs
    | cons g1 gs' => rfl
  rw [unpurge_purgeLayP hs hf, walFullD_purgeLayP d lay g0 p hf]
  refine crashOkA_purgeF hC hF (by simpa using hnd) (t := lay.pg.length) (g0 := g0) (gs := gs)
    (by simp [hs]) hgs (hz g0 (by rw [hdl]; simp)) hX hcl hcoh hcoh' hst hbt hothers hcur0
    (by rw [habs.names.1, hs]) hwal' (Nat.le_max_left _ _) ?_ hcr
  have e1 : (unpurge lay.pg lay).first + (lay.pg.length + 1) = lay.first + 1 := by
    simp only [unpurge_first]; omega
  rw [unpurge_cuts, e1]
  exact Nat.le_trans hp (Nat.le_max_right _ _)

/-- **The full layout's condition after the removal** (see the file header): the old condition, the
crash condition without an alternative (`DirKeysOk`'s: no cut pending), the static relation over the
claim's names `h.cur`, `g0` the first named segment and not the last, the removal (the entry `e` at `x`,
writing of the claim's names only `bt`, which held `g0`) leaving names `c` whose `.wal` files are the other
segments', `pur` raised to `p`, past `g0`'s end. -/
theorem walFullOk_purge {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {g0 : SegG} {gs : List SegG} {cl : List Claim} {n : Nat} {X : List GoString} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString} {p : Nat}
    (hok : WalFullOk C Mr d lay cl n)
    (hcr : CrashOkA C Mr (walFullD d lay.pg lay) (unpurge lay.pg lay) none cl n)
    (habs : WalAbsD C Mr d lay h.cur) (hnd : ((lay.pg ++ lay.segs).map (·.ino)).Nodup)
    (hs : lay.segs = g0 :: gs) (hgs : gs ≠ []) (hp : segStart lay.cuts (lay.first + 1) ≤ p)
    (hX : ∀ b ∈ X, walNameP b = false)
    (hcl : (lay.j, NameSet.except X, h) ∈ cl) (hcoh : ClaimCoh h lay.j (.except X))
    (hcoh' : ClaimCoh (h.log x e c) lay.j (.except X)) (hst : h.next ≤ e.start)
    (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, h) → c'.1 = lay.j → ¬ c'.2.1.Mem bt)
    (hcur0 : h.cur !! bt = some (.file g0.ino)) (hwal' : walInos c = gs.map (·.ino)) :
    WalFullOk C Mr (walPurgeD d lay p) (purgeLayP lay g0)
      (replClaim (lay.j, NameSet.except X, h) (lay.j, NameSet.except X, h.log x e c) cl) n := by
  have hcrF := crashOkA_full_purge hC hok hcr habs hnd hs hgs hp hX hcl hcoh hcoh' hst hbt hothers hcur0
    hwal'
  obtain ⟨⟨e0, hF⟩, -, hz⟩ := hok
  have hf := pg_le_first habs hF
  have hdl : lay.segs.dropLast = g0 :: gs.dropLast := by
    rw [hs]
    cases gs with
    | nil => exact absurd rfl hgs
    | cons g1 gs' => rfl
  unfold WalFullOk
  refine ⟨?_, ⟨none, (fun _ h => nomatch h), hcrF⟩, ?_⟩
  · rw [unpurge_purgeLayP hs hf, walFullD_purgeLayP d lay g0 p hf]
    exact ⟨e0, hF.pur_mono (Nat.le_max_left _ _)⟩
  · refine hz.mono (fun g hg => ?_)
    simp only [purgeLayP_pg, purgeLayP_segs, hs, List.tail_cons, List.mem_append,
      List.mem_singleton] at hg
    rw [hdl]
    simp only [List.mem_append, List.mem_cons]
    rcases hg with (hg | hg) | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr hg)

/-! ## Another WAL's crash condition -/

theorem entsOf_treeSetE_ne (m' : Tree) {j j' : Ino} (bt : GoString) (v : Option Fs.Node) (h : j' ≠ j) :
    entsOf (treeSetE m' j bt v) j' = entsOf m' j' := by
  apply GMap.ext; intro b
  rw [entsOf_entry, entsOf_entry, treeSetE_entry]
  simp [h]

/-- **A crash of the claims after a removal**: one of the claims before it, `bt` set back, or not. -/
theorem regionCrashed_purge {cl : List Claim} {n : Nat} {m' : Tree} {j : Ino} {N : NameSet}
    {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hr : RegionCrashed (replClaim (j, N, h) (j, N, h.log x e c) cl) n m')
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    RegionCrashed cl n (treeSetE m' j bt (h.cur !! bt)) ∨ RegionCrashed cl n m' := by
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · exact Or.inl ((regionCrashed_iff _ _ _).2
      ⟨K, (regionCrashedK_keptSet cl n m' K j N h x e c bt hK hx hcl hcoh hs hbt hothers).2⟩)
  · exact Or.inr ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_unlog cl n m' K j N h x e c hK hx⟩)

/-- **Another WAL's crash condition after a removal** (its directory and its area directory not `j`;
its alternative, if any, on the same names). -/
theorem crashOkA_purge_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hok : CrashOkA C Mr d lay alt cl n)
    (halt : ∀ lay0, alt = some lay0 → lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j)
    (hlj : lay.j ≠ j) (hljr : lay.jr ≠ j)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    CrashOkA C Mr d lay alt (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro m' fo hr hf hn hw
  rcases regionCrashed_purge hr hcl hcoh hs hbt hothers with hr' | hr'
  · have hwi : walInos (entsOf (treeSetE m' j bt (h.cur !! bt)) lay.j) = walInos (entsOf m' lay.j) := by
      rw [entsOf_treeSetE_ne m' bt _ hlj]
    have hent : (treeSetE m' j bt (h.cur !! bt)).entry lay.jr lay.nm = m'.entry lay.jr lay.nm := by
      rw [treeSetE_entry]; simp [hljr]
    rcases hok _ fo hr' hf (fun g hg hin => hn g hg (by rw [← hwi]; exact hin))
      (by rw [hwi]; exact hw) with hct | ⟨lay0, h0, hct⟩
    · exact Or.inl (crashTo_congr hent hwi hct)
    · obtain ⟨h1, h2, h3⟩ := halt lay0 h0
      refine Or.inr ⟨lay0, h0, crashTo_congr ?_ (by rw [h3]; exact hwi) hct⟩
      rw [h1, h2]; exact hent
  · exact hok m' fo hr' hf hn hw

theorem crashOkW_purge_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hok : CrashOkW C Mr d lay cl n) (hlj : lay.j ≠ j) (hljr : lay.jr ≠ j)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    CrashOkW C Mr d lay (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  obtain ⟨alt, halt, hA⟩ := hok
  exact ⟨alt, halt, crashOkA_purge_other hA (fun l0 h0 => ⟨(halt l0 h0).2.1, (halt l0 h0).2.2.1,
    (halt l0 h0).2.2.2.1⟩) hlj hljr hcl hcoh hs hbt hothers⟩

theorem walFullOk_purge_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hok : WalFullOk C Mr d lay cl n) (hlj : lay.j ≠ j) (hljr : lay.jr ≠ j)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    WalFullOk C Mr d lay (replClaim (j, N, h) (j, N, h.log x e c) cl) n :=
  ⟨hok.1, crashOkW_purge_other (lay := unpurge lay.pg lay) hok.2.1 hlj hljr hcl hcoh hs hbt hothers,
    hok.2.2⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
