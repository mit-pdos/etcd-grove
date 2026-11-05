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

end pure

end WNext

end bbolt
end EtcdGrove
end Perennial
