/-
`Cursor.next` of a writer's cursor (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): the pure facts of its loop. A writer path's leaf bounds are ordered (`pathBnd_ord`, over
the logical walk's invariant `bInv`: a branch's keys are sorted within its bounds); the upward scan's
invariant (`scanOK`: every level from `kk` on can not move, a branch at its last index, the leaf at
or past its last entry); the stack truncated at the level found and moved one further is a prefix
(`trunc_prefix`); the descent's new stack is at `wNextTo` (`found`, by `stackPos_nextR`); with no
level found, the stack is at the end (`scan_none`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WGoFirst
public import Proof.go_etcd_io.bbolt.Read.Prev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace WNext

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge WGoFirst

section pure
variable [GooseExts]

/-! ## Ordered bounds -/

/-- Bounds whose upper bound is not below their lower one. -/
def ordB (b : Bnd) : Prop := ∀ L H, b = (some L, some H) → ¬ go.GoStringLt H L

theorem ordB_child (b : Bnd) (ws : List WEntry) (hs : wsPw ws)
    (hin : ∀ w ∈ ws, keyIn b.1 b.2 w.key) (i : Nat) (hi : i < ws.length) (hb : ordB b) :
    ordB (wEntryBnd b ws i) := by
  intro L H h
  rw [wEntryBnd_eq] at h
  simp only [Prod.mk.injEq, childLo, childHi] at h
  obtain ⟨h1, h2⟩ := h
  split at h1 <;> split at h2
  · rename_i hi1
    cases h2
    exact (hin _ (getD_mem ws (i + 1) hi1)).1 L h1
  · exact hb L H (Prod.ext h1 h2)
  · rename_i hi1
    cases h1; cases h2
    exact go.goStringLt_asymm (wsPw_get ws hs i (i + 1) (by omega) hi1)
  · cases h1
    exact go.goStringLt_asymm ((hin _ (getD_mem ws i hi)).2 H h2)

theorem lPathFrom_ord (X : WX) (bl : Loc) (B : BRec) (bnd : Loc → Bnd) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hbk : bktKeysB X.v B bnd) :
    ∀ (els : List elemRef) (ps : List w64) (p : w64) (b : Bnd),
    lPathFrom X bl p els ps → bInv X bl B bnd p b → ordB b →
    ordB (pathBndFrom X.v b (ps.map (·.toNat)) els)
  | [], _, _, _, h, _, _ => absurd rfl h.1
  | [e], ps, p, b, h, _, hb => by
    obtain ⟨rfl, -⟩ := lPathFrom_one X bl p e ps h
    simpa [pathBndFrom] using hb
  | e :: e' :: es, ps, p, b, h, hI, hb => by
    obtain ⟨ws, w, ps', rfl, -, hL, hw, ht⟩ := lPathFrom_tail X bl p e e' es ps h
    have hne : ps' ≠ [] := by
      intro h0; subst h0; obtain ⟨-, hlen, -⟩ := ht; simp at hlen
    obtain ⟨p', ps'', rfl⟩ : ∃ p' ps'', ps' = p' :: ps'' := by
      cases ps' with
      | nil => exact absurd rfl hne
      | cons a t => exact ⟨a, t, rfl⟩
    obtain ⟨hpw, hin, hch⟩ := bInv_branch X bl B bnd hok hB hbk p b hI ws hL
    have hi : e.index'.toNat < ws.length := (List.getElem?_eq_some_iff.1 hw).1
    have hgd : ws.getD e.index'.toNat default = w := by
      rw [List.getD_eq_getElem?_getD, hw]; rfl
    have hkeys := ltree_branch_keys X bl B hok hB p ws hL
    have := lPathFrom_ord X bl B bnd hok hB hbk (e' :: es) (p' :: ps'') w.pgid
      (wEntryBnd b ws e.index'.toNat) ht (by rw [← hgd]; exact hch _ hi)
      (ordB_child b ws hpw hin _ hi hb)
    simp only [List.map_cons, pathBndFrom]
    unfold wEntryBnd at this
    rw [hkeys] at this
    simpa using this

/-- **A writer path's leaf bounds are ordered.** -/
theorem pathBnd_ord (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (nl : Loc → Option (Loc × Nat))
    (els : List elemRef) (pids : List Nat) (hp : sPathR nl X.v bl rt els pids) :
    ordB (pathBnd X.v pids els) := by
  obtain ⟨hlp, hlt⟩ := sPathR_lPath X n bl rt B hc hB nl els pids hp
  have hlen : pids.length = els.length := hp.2.1
  obtain ⟨-, -, hbnd, -⟩ := curRefs_index X B pids els hlen
  have hrt : (pids.map fun (p : Nat) => W64 (p : Int)).map (·.toNat) = pids := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id pids]
    apply List.map_congr_left
    intro p hp'
    have := hlt p hp'
    simp only [Function.comp, id]
    simp; omega
  obtain ⟨bnd, hbk⟩ := (hc.1.2.1 bl B hB).1
  have := lPathFrom_ord X bl B bnd hc.1 hB hbk _ _ _ _ hlp (bInv_root X bl B bnd hc.1 hB hbk)
    (by intro L H h; cases h)
  rw [hrt] at this
  rw [← hbnd]; exact this

/-! ## Bounds and positions -/

theorem pathBndFrom_snoc (v : View) :
    ∀ (E : List elemRef) (pids : List Nat) (b : Bnd) (x y : elemRef),
    pids.length = E.length + 1 → pathBndFrom v b pids (E ++ [x]) = pathBndFrom v b pids (E ++ [y])
  | [], [_], _, _, _, _ => by simp [pathBndFrom]
  | [], [], _, _, _, h => by simp at h
  | [], _ :: _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | _ :: _, [_], _, _, _, h => by simp at h
  | e :: E, p :: p' :: ps, b, x, y, h => by
    simp only [List.cons_append, pathBndFrom]
    exact pathBndFrom_snoc v E (p' :: ps) _ x y (by simpa using h)

theorem pathBnd_snoc (v : View) (E : List elemRef) (pids : List Nat) (x y : elemRef)
    (h : pids.length = E.length + 1) : pathBnd v pids (E ++ [x]) = pathBnd v pids (E ++ [y]) :=
  pathBndFrom_snoc v E pids _ x y h

open Classical in
/-- **A path at every branch's last index reaches the end**: the entries below its leaf and its
leaf's are all of `es`. -/
theorem brLast_cnt (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (hl : pids.length = els.length) (hb : sBrLast v pids els) :
    (es.filter fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1)).length +
      leafCnt v es pids els = es.length := by
  have h2 : (pathBnd v pids els).2 = none := Prev.pathBndFrom_last v els pids (none, none) hl hb
  unfold leafCnt entsIn
  generalize pathBnd v pids els = bd at h2 ⊢
  obtain ⟨lo, hi⟩ := bd
  simp only at h2 ⊢
  subst h2
  have := Prev.len_filter_sum es (fun e => decide (¬ keyGe lo e.1))
    (fun e => decide (keyIn lo none e.1)) (fun _ => true)
    (by intro e _; by_cases h : keyGe lo e.1 <;> simp [h, keyIn, keyLt])
  rw [show (es.filter fun _ => true) = es from List.filter_eq_self.2 (by simp)] at this
  simpa using this

/-! ## The upward scan -/

/-- **`next`'s upward scan from level `kk`**: no level from `kk` on can move (a branch at its last
index, the leaf at or past its last entry). -/
def scanOK (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (kk : Nat) : Prop :=
  ∀ j e pid, kk ≤ j → els[j]? = some e → pids[j]? = some pid →
    (j + 1 < els.length → e.index'.toNat + 1 = (pidKeys v pid).length) ∧
    (j + 1 = els.length → leafCnt v es pids els ≤ e.index'.toNat + 1)

theorem scanOK_start (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) :
    scanOK v es pids els els.length := by
  intro j e pid hj he _
  have := (List.getElem?_eq_some_iff.1 he).1; omega

theorem scanOK_br (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (hp : sPathR nl v b rt els pids)
    (k : Nat) (hk : k + 1 < els.length) (hs : scanOK v es pids els (k + 1)) (e : elemRef)
    (pid : Nat) (pg : List w8) (he : els[k]? = some e) (hpid : pids[k]? = some pid)
    (hpg : v.pages !! pid = some pg) (hge : pageCount pg ≤ e.index'.toNat + 1) :
    scanOK v es pids els k := by
  intro j x q hj hx hq
  rcases Nat.lt_or_ge k j with h | h
  · exact hs j x q h hx hq
  · have hjk : j = k := by omega
    subst hjk
    rw [he] at hx; cases hx; rw [hpid] at hq; cases hq
    obtain ⟨pg', hpg', -, hlt, -⟩ := (hp.2.2.2 j e pid he hpid).2.2.1 hk
    rw [hpg] at hpg'; cases hpg'
    refine ⟨fun _ => ?_, fun h => by omega⟩
    rw [Prev.pidKeys_length v pid pg hpg]; omega

theorem scanOK_leaf (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (k : Nat)
    (hk : k + 1 = els.length) (e : elemRef) (he : els[k]? = some e)
    (hge : leafCnt v es pids els ≤ e.index'.toNat + 1) : scanOK v es pids els k := by
  intro j x q hj hx hq
  have hjl := (List.getElem?_eq_some_iff.1 hx).1
  have hjk : j = k := by omega
  subst hjk; rw [he] at hx; cases hx
  exact ⟨fun h => by omega, fun _ => hge⟩

theorem getLast_some {α : Type} (l : List α) (h : l ≠ []) : ∃ x, l.getLast? = some x := by
  cases hl : l.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; exact absurd hl h
  | some x => exact ⟨x, rfl⟩

theorem leafIdx_of (els : List elemRef) (x : elemRef) (h : els.getLast? = some x) :
    leafIdx els = x.index'.toNat := by
  unfold leafIdx; rw [h]; rfl

/-- The scan past the leaf: the leaf at or past its last entry. -/
theorem scanOK_leafIdx (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (kk : Nat) (hl : pids.length = els.length) (hk : kk < els.length) (hs : scanOK v es pids els kk) :
    leafCnt v es pids els ≤ leafIdx els + 1 := by
  obtain ⟨x, hx⟩ := getLast_some els (by intro h; subst h; simp at hk)
  have hxj := getLast_idx els x hx
  obtain ⟨q, hq⟩ : ∃ q, pids[els.length - 1]? = some q :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have := (hs _ x q (by omega) hxj hq).2 (by omega)
  rw [leafIdx_of els x hx]; exact this

open Classical in
/-- **No level moves**: the path is at the end (every branch last), so `next`'s target is past the
last entry; off an entry of its leaf, it is `wEndAt`. -/
theorem scan_none (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (hl : pids.length = els.length) (hne : els ≠ []) (hs : scanOK v es pids els 0)
    (hle : leafIdx els ≤ leafCnt v es pids els) :
    es.length ≤ wNextTo v es pids els ∧
    (¬ leafIdx els < leafCnt v es pids els → wEndAt v es pids els) := by
  have hb : sBrLast v pids els := fun j pid e hpj hej hj => (hs j e pid (Nat.zero_le _) hej hpj).1 hj
  have hc := scanOK_leafIdx v es pids els 0 hl (List.length_pos_iff.2 hne) hs
  have hcnt := brLast_cnt v es pids els hl hb
  refine ⟨?_, fun hn => ⟨hb, ?_⟩⟩
  · unfold wNextTo stackPos; split <;> omega
  · obtain ⟨x, hx⟩ := getLast_some els hne
    refine ⟨x, hx, Or.inl ?_⟩
    have hli := leafIdx_of els x hx
    have heq : leafCnt v es pids els = x.index'.toNat := by omega
    rw [heq]; exact (w64_cast_toNat x.index').symm

/-! ## The level found -/

theorem pids_snoc_get (P U : List Nat) (p : Nat) (k : Nat) (hk : k ≤ P.length) :
    (P ++ [p])[k]? = (P ++ p :: U)[k]? := by
  rcases Nat.lt_or_ge k P.length with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · have : k = P.length := by omega
    subst this; simp

/-- A branch page is at a view page, not position `0`. -/
theorem leaf_not_branch (v : View) (hv : viewWF v) (p : Nat) (pg : List w8)
    (hpg : v.pages !! p = some pg) (hb : pageFlags pg = branchPageFlag)
    (h : p = 0 ∨ ∃ pg, v.pages !! p = some pg ∧ pageFlags pg = leafPageFlag) : False := by
  rcases h with h0 | ⟨pg', hpg', hf⟩
  · subst h0; have := (Read.viewWF_page v hv 0 pg hpg).1; omega
  · rw [hpg] at hpg'; cases hpg'; exact flag_ne hb hf

/-- **The stack truncated at the level found, moved one further, is a prefix** (and a path only if
the level is the leaf). -/
theorem trunc_prefix (nl : Loc → Option (Loc × Nat)) (v : View) (hv : viewWF v) (b : Loc)
    (rt : Nat) (E T : List elemRef) (e e' : elemRef) (P U : List Nat) (p : Nat)
    (hPE : P.length = E.length) (hp : sPathR nl v b rt (E ++ e :: T) (P ++ p :: U))
    (hpg : e'.page' = e.page') (hnd : e'.node' = e.node')
    (hlt : T ≠ [] → ∀ pg, v.pages !! p = some pg → e'.index'.toNat < pageCount pg) :
    sPrefix nl v b rt (E ++ [e']) (P ++ [p]) ∧
    (sPathR nl v b rt (E ++ [e']) (P ++ [p]) → T = [] ∧ U = []) := by
  obtain ⟨-, hlen, hhd, hall⟩ := hp
  simp only [List.length_append, List.length_cons] at hlen
  have hUT : U.length = T.length := by omega
  have hE : (E ++ e :: T)[E.length]? = some e := by simp
  have hP : (P ++ p :: U)[E.length]? = some p := by rw [← hPE]; simp
  obtain ⟨a1, a2, a3, a4⟩ := hall E.length e p hE hP
  have hhd' : (P ++ [p]).head? = some rt := by
    cases P with
    | nil => simpa using hhd
    | cons a t => simpa using hhd
  refine ⟨⟨by simp, by simp [hPE], hhd', fun j x q hx hq => ?_⟩, fun hp2 => ?_⟩
  · have hjl : j < E.length + 1 := by have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
    rcases Nat.lt_or_ge j E.length with hj | hj
    · rw [List.getElem?_append_left hj] at hx
      rw [List.getElem?_append_left (by omega)] at hq
      have hx' : (E ++ e :: T)[j]? = some x := by rw [List.getElem?_append_left hj]; exact hx
      have hq' : (P ++ p :: U)[j]? = some q := by rw [List.getElem?_append_left (by omega)]; exact hq
      obtain ⟨b1, b2, b3, -⟩ := hall j x q hx' hq'
      refine ⟨b1, b2, fun hj1 => ?_, fun hj1 => by simp at hj1; omega⟩
      obtain ⟨pg, hpg, hf, hl, hnx⟩ := b3 (by simp; omega)
      refine ⟨pg, hpg, hf, hl, ?_⟩
      rw [pids_snoc_get P U p (j + 1) (by simp at hj1; omega)]; exact hnx
    · have hjE : j = E.length := by omega
      subst hjE
      simp at hx; subst hx
      rw [← hPE] at hq; simp at hq; subst hq
      refine ⟨fun h => by rw [hnd] at h ⊢; exact a1 h, fun h => by rw [hnd] at h; rw [hpg]; exact a2 h,
        fun h => by simp at h, fun _ => ?_⟩
      by_cases hT : T = []
      · subst hT
        rcases a4 (by simp) with h | ⟨pg, hpg', hf⟩
        · exact Or.inl h
        · exact Or.inr ⟨pg, hpg', Or.inl hf⟩
      · obtain ⟨pg, hpg', hf, -, -⟩ := a3 (by cases T with | nil => exact absurd rfl hT | cons _ _ => simp)
        exact Or.inr ⟨pg, hpg', Or.inr ⟨hf, hlt hT pg hpg'⟩⟩
  · have hT : T = [] := by
      refine Classical.byContradiction fun hT => ?_
      obtain ⟨pg, hpg', hf, -, -⟩ := a3 (by cases T with | nil => exact absurd rfl hT | cons _ _ => simp)
      obtain ⟨-, -, -, c4⟩ := hp2.2.2.2 E.length e' p (by simp) (by rw [← hPE]; simp)
      exact leaf_not_branch v hv p pg hpg' hf (c4 (by simp))
    subst hT
    exact ⟨rfl, List.eq_nil_of_length_eq_zero (by simpa using hUT)⟩

/-! ## A level's count -/

/-- **`count()` of level `j` of a stack**: its branch page's count, or the leaf's entries. -/
def cntAt (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (j : Nat) : Nat :=
  if j + 1 < els.length then ((v.pages !! pids.getD j 0).map pageCount).getD 0
  else leafCnt v es pids els

theorem cntAt_br (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (j : Nat)
    (pid : Nat) (pg : List w8) (hj : j + 1 < els.length) (hpid : pids[j]? = some pid)
    (hpg : v.pages !! pid = some pg) : cntAt v es pids els j = pageCount pg := by
  unfold cntAt; rw [if_pos hj, List.getD_eq_getElem?_getD, hpid]; simp [hpg]

theorem cntAt_leaf (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (j : Nat)
    (hj : j + 1 = els.length) : cntAt v es pids els j = leafCnt v es pids els := by
  unfold cntAt; rw [if_neg (by omega)]

/-- A branch level's page. -/
theorem sPathR_br (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (pids : List Nat) (els : List elemRef) (hp : sPathR nl v b rt els pids) (j : Nat)
    (hj : j + 1 < els.length) (e : elemRef) (he : els[j]? = some e) :
    ∃ pid pg, pids[j]? = some pid ∧ v.pages !! pid = some pg ∧ pageFlags pg = branchPageFlag ∧
      e.index'.toNat < pageCount pg := by
  obtain ⟨pid, hpid⟩ : ∃ pid, pids[j]? = some pid :=
    ⟨_, List.getElem?_eq_getElem (by have := hp.2.1; omega)⟩
  obtain ⟨pg, hpg, hf, hlt, -⟩ := (hp.2.2.2 j e pid he hpid).2.2.1 hj
  exact ⟨pid, pg, hpid, hpg, hf, hlt⟩

/-- The scan's step at a level that can not move. -/
theorem scanOK_step (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (hp : sPathR nl v b rt els pids)
    (k : Nat) (hk : k < els.length) (hs : scanOK v es pids els (k + 1)) (e : elemRef)
    (he : els[k]? = some e) (hge : cntAt v es pids els k ≤ e.index'.toNat + 1) :
    scanOK v es pids els k := by
  by_cases hk1 : k + 1 < els.length
  · obtain ⟨pid, pg, hpid, hpg, -, -⟩ := sPathR_br nl v b rt pids els hp k hk1 e he
    rw [cntAt_br v es pids els k pid pg hk1 hpid hpg] at hge
    exact scanOK_br nl v b rt es pids els hp k hk1 hs e pid pg he hpid hpg hge
  · rw [cntAt_leaf v es pids els k (by omega)] at hge
    exact scanOK_leaf v es pids els k (by omega) e he hge

/-- A level's index is at most its count. -/
theorem cntAt_idx (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc)
    (rt : Nat) (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hw : wStk nl v es b rt ipg els pids) (k : Nat) (hk : k < els.length) (e : elemRef)
    (he : els[k]? = some e) : e.index'.toNat ≤ cntAt v es pids els k := by
  by_cases hk1 : k + 1 < els.length
  · obtain ⟨pid, pg, hpid, hpg, -, hlt⟩ := sPathR_br nl v b rt pids els hw.1 k hk1 e he
    rw [cntAt_br v es pids els k pid pg hk1 hpid hpg]; omega
  · rw [cntAt_leaf v es pids els k (by omega)]
    have hl : els.getLast? = some e := by
      rw [List.getLast?_eq_getElem?, show els.length - 1 = k by omega]; exact he
    have := hw.2.2
    rw [leafIdx_of els e hl] at this
    exact this

/-- A leaf page's entries do not depend on the leaf index. -/
theorem sLeafOK_snoc (v : View) (ipg : List w8) (es : List BoltEnt) (E : List elemRef)
    (pids : List Nat) (e e' : elemRef) (hl : pids.length = E.length + 1) (hnd : e'.node' = e.node')
    (h : sLeafOK v ipg es pids (E ++ [e])) : sLeafOK v ipg es pids (E ++ [e']) := by
  intro x pid hx hpid hn
  simp at hx; subst hx
  rw [pathBnd_snoc v E pids e' e hl]
  exact h e pid (by simp) hpid (by rw [← hnd]; exact hn)

open Classical in
/-- **The descent's new stack is at `next`'s target** (`stackPos_nextR`), on an entry of its leaf
or in an empty leaf at index `0`. -/
theorem found (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec) (hc : wCurCtx X n bl rt)
    (hB : X.t.bs !! bl = some B) (es : List BoltEnt) (nl : Loc → Option (Loc × Nat))
    (E T : List elemRef) (e e' : elemRef) (P U : List Nat) (p : Nat) (hPE : P.length = E.length)
    (hp : sPathR nl X.v bl rt (E ++ e :: T) (P ++ p :: U))
    (hle : leafIdx (E ++ e :: T) ≤ leafCnt X.v es (P ++ p :: U) (E ++ e :: T))
    (hs : scanOK X.v es (P ++ p :: U) (E ++ e :: T) (E.length + 1))
    (hidx : e'.index'.toNat = e.index'.toNat + 1)
    (hlt : T = [] → e.index'.toNat + 1 < leafCnt X.v es (P ++ p :: U) (E ++ e :: T))
    (R : List elemRef) (Q : List Nat) (hR : sAllFirst R)
    (hp2 : sPathR nl X.v bl rt (E ++ [e'] ++ R) (P ++ [p] ++ Q)) :
    stackPos X.v es (P ++ [p] ++ Q) (E ++ [e'] ++ R) = wNextTo X.v es (P ++ p :: U) (E ++ e :: T) ∧
    (leafIdx (E ++ [e'] ++ R) < leafCnt X.v es (P ++ [p] ++ Q) (E ++ [e'] ++ R) ∨
     (leafIdx (E ++ [e'] ++ R) = 0 ∧ leafCnt X.v es (P ++ [p] ++ Q) (E ++ [e'] ++ R) = 0)) := by
  have hv : viewWF X.v := hc.1.2.2.2.2.2.2.2
  have hE : (E ++ e :: T)[E.length]? = some e := by simp
  have hP : (P ++ p :: U)[E.length]? = some p := by rw [← hPE]; simp
  have hE2 : (E ++ [e'] ++ R)[E.length]? = some e' := by simp
  have hP2 : (P ++ [p] ++ Q)[E.length]? = some p := by rw [← hPE]; simp
  obtain ⟨-, -, a3, a4⟩ := hp.2.2.2 E.length e p hE hP
  obtain ⟨-, -, c3, c4⟩ := hp2.2.2.2 E.length e' p hE2 hP2
  have hl1 := hp.2.1
  have hl2 := hp2.2.1
  simp only [List.length_append, List.length_cons, List.length_singleton] at hl1 hl2
  have hTR : T ≠ [] ↔ R ≠ [] := by
    constructor
    · intro hT hR0
      subst hR0
      obtain ⟨pg, hpg, hf, -, -⟩ := a3 (by cases T with | nil => exact absurd rfl hT | cons _ _ => simp)
      exact leaf_not_branch X.v hv p pg hpg hf (c4 (by simp))
    · intro hR0 hT
      subst hT
      obtain ⟨pg, hpg, hf, -, -⟩ := c3 (by cases R with | nil => exact absurd rfl hR0 | cons _ _ => simp)
      exact leaf_not_branch X.v hv p pg hpg hf (a4 (by simp))
  have hsucc : sSucc E.length (E ++ e :: T) (E ++ [e'] ++ R) :=
    ⟨e, e', R, hE, by simp, hidx, fun x hx => by rw [hR x hx]; rfl⟩
  have hlenI : E.length + 1 < (E ++ e :: T).length ↔ E.length + 1 < (E ++ [e'] ++ R).length := by
    simp only [List.length_append, List.length_cons, List.length_singleton]
    constructor
    · intro h; have : T ≠ [] := fun h0 => by subst h0; simp at h
      have := hTR.1 this; cases R with | nil => exact absurd rfl this | cons _ _ => simp
    · intro h; have : R ≠ [] := fun h0 => by subst h0; simp at h
      have := hTR.2 this; cases T with | nil => exact absurd rfl this | cons _ _ => simp
  have hend : E.length + 1 < (E ++ e :: T).length →
      sEndBelow X.v es (P ++ p :: U) (E ++ e :: T) E.length :=
    fun _ => ⟨fun j pid x hpj hx hdj hj => (hs j x pid (by omega) hx hpj).1 hj, hle,
      pathBnd_ord X n bl rt B hc hB nl _ _ hp⟩
  obtain ⟨h1, h2⟩ := stackPos_nextR nl X.v es bl rt _ _ _ _ E.length hp hp2 hsucc hlenI hend
  by_cases hT : T = []
  · subst hT
    have hR0 : R = [] := by
      exact Classical.byContradiction fun h => (hTR.2 h) rfl
    subst hR0
    have hQ : Q = [] := List.eq_nil_of_length_eq_zero (by simp at hl2; omega)
    subst hQ
    have hU : U = [] := List.eq_nil_of_length_eq_zero (by simp at hl1; omega)
    subst hU
    simp only [List.append_nil] at h1 ⊢
    have hpos := h1 (by simp)
    have hli : leafIdx (E ++ [e]) = e.index'.toNat := leafIdx_of _ e (by simp)
    have hli' : leafIdx (E ++ [e']) = e'.index'.toNat := leafIdx_of _ e' (by simp)
    have hcnt : leafCnt X.v es (P ++ [p]) (E ++ [e']) = leafCnt X.v es (P ++ [p]) (E ++ [e]) := by
      unfold leafCnt; rw [pathBnd_snoc X.v E (P ++ [p]) e' e (by simp [hPE])]
    have hlt' := hlt rfl
    refine ⟨?_, Or.inl (by rw [hli', hcnt]; omega)⟩
    rw [hpos]; unfold wNextTo; rw [if_pos (by rw [hli]; omega)]
  · have hRne := hTR.1 hT
    obtain ⟨x, hx⟩ := getLast_some R hRne
    have hli2 : leafIdx (E ++ [e'] ++ R) = 0 := by
      rw [Prev.leafIdx_append _ _ hRne, leafIdx_of R x hx, hR x (List.mem_of_getLast? hx)]; rfl
    have hpos := h2 (by simp; cases T with | nil => exact absurd rfl hT | cons _ _ => simp)
    rw [hli2]
    have hsc := scanOK_leafIdx X.v es _ _ (E.length + 1) (by simp; omega)
      (by simp; cases T with | nil => exact absurd rfl hT | cons _ _ => simp) hs
    unfold leafCnt at hle hsc
    refine ⟨?_, ?_⟩
    · unfold wNextTo leafCnt; split <;> omega
    · by_cases h0 : leafCnt X.v es (P ++ [p] ++ Q) (E ++ [e'] ++ R) = 0
      · exact Or.inr ⟨rfl, h0⟩
      · exact Or.inl (by omega)

end pure

end WNext

end bbolt
end EtcdGrove
end Perennial
