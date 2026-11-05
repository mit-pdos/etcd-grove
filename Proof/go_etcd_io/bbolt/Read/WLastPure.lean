/-
`last` of a writer's cursor (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a fraction"), pure:
the reference `pageNode` returns for a branch's child (a live node of the bucket, or the view page
at its location), and pushing it at its last index (`count - 1`) keeps `last`'s loop invariant: a
prefix (`sPrefix`) over the writer's registry, every branch at its last index (`sBrLast`), the top
at its last (`sTopLast`), its leaf page, once a path, holding its bounds' entries.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WGoFirst

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WLast

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge WGoFirst

section pure
variable [GooseExts]

theorem pidKeys_length (v : View) (pid : Nat) (pg : List w8) (h : v.pages !! pid = some pg) :
    (pidKeys v pid).length = pageCount pg := by
  unfold pidKeys; rw [h]; simp

/-- **The reference `pageNode` returns for a branch's child `c`** (a view page; the bucket has a
root page): its logical entries `ws`; a node reference is a live node of the bucket with them, a page
reference the view page at its location; a branch is not empty. -/
theorem child_ref (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (h0 : B.ib.root' ≠ W64 0) (c : Nat) (pgc0 : List w8) (hpgc0 : X.v.pages !! c = some pgc0)
    (hclt : c < 2 ^ 64) (p' n' : Loc)
    (hpn : match resolve B (W64 (c : Int)) with
      | some l => p' = null ∧ n' = l
      | none => n' = null ∧ ∃ pg2, wpageAt X.v B (W64 (c : Int)) = some (p', pg2)) :
    ∃ lf ws, ltree X bl (W64 (c : Int)) = some (lf, ws) ∧
      (∀ i, refAt X bl (W64 (c : Int)) ⟨p', n', i⟩) ∧
      (n' ≠ null → ∃ rn, B.ns !! n' = some rn ∧ n' ∈ X.live ∧ rn.ws = ws) ∧
      (n' ≠ null → X.nloc !! n' = some (bl, c)) ∧
      (n' = null → p' = pageLoc X.v c ∧ X.v.pages !! c = some pgc0 ∧ ws = pageWs pgc0 ∧
        16 ≤ pgc0.length) ∧
      (lf = false → ∃ pg, X.v.pages !! c = some pg ∧ pageFlags pg = branchPageFlag ∧
        ws.length = pageCount pg ∧ 0 < pageCount pg) := by
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := wOK_bktClean X hok bl B hB
  have hc2 : 2 ≤ c := (Read.viewWF_page _ hv _ _ hpgc0).1
  have hC : (W64 (c : Int)).toNat = c := W64_toNat_lt c hclt
  obtain ⟨lf, ws, hra, hL, hnode⟩ : ∃ lf ws, (∀ i, refAt X bl (W64 (c : Int)) ⟨p', n', i⟩) ∧
      ltree X bl (W64 (c : Int)) = some (lf, ws) ∧
      (n' ≠ null → ∃ rn, B.ns !! n' = some rn ∧ n' ∈ X.live ∧ rn.ws = ws) := by
    cases hr : resolve B (W64 (c : Int)) with
    | some l =>
      rw [hr] at hpn
      obtain ⟨-, r, hr', -⟩ := hcl.2.2.2.2.1 _ l (by rw [← resolve_tree B _ h0]; exact hr)
      refine ⟨r.nv.isLeaf', r.ws, fun i => refAt_node X bl B _ l _ hB hr hpn.2,
        ltree_node X bl B _ l r hB hr hr', fun _ => ⟨r, by rw [hpn.2]; exact hr', ?_, rfl⟩⟩
      rw [hpn.2]; exact wOK_nsLive X hok bl B _ r hB hr'
    | none =>
      rw [hr] at hpn
      obtain ⟨hnn, pg', hw⟩ := hpn
      exact ⟨_, _, fun i => refAt_page X bl B (W64 (c : Int)) pg' _ hB hr hnn hw,
        ltree_page X bl B (W64 (c : Int)) _ pg' hB hr hw, fun h => absurd hnn h⟩
  obtain ⟨P1, P2, P3, -, P5⟩ := pos_facts X bl B hok hB hc.2.2.1 hbase _ ⟨p', n', W64 0⟩ lf ws
    (hra _) hL (fun h => absurd h h0)
  rw [hC] at P1 P2 P3 P5
  refine ⟨lf, ws, hL, hra, hnode, P1, fun hnn => ?_, fun hlf => ?_⟩
  · obtain ⟨-, hpl⟩ := P2 hnn
    obtain ⟨pg', hlp, hws, -⟩ := P5 hnn
    unfold leafPgAt at hlp; rw [if_neg (by omega), hpgc0] at hlp
    cases hlp
    exact ⟨hpl (by omega), hpgc0, hws, by have := (Read.viewWF_page _ hv _ _ hpgc0).2.2.1; omega⟩
  · obtain ⟨pg', hpg', hb', hwl, -⟩ := P3 hlf
    obtain ⟨_, hbw⟩ := viewWF_branchWF _ hv _ _ hpg' hb'
    exact ⟨pg', hpg', hb', hwl, hbw.1⟩

/-- **A branch top is at its page's last entry** (`sTopLast`). -/
theorem top_branch_last (v : View) (hv : viewWF v) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (htl : sTopLast v es pids els) (e : elemRef) (p : Nat)
    (he : els.getLast? = some e) (hpl : pids.getLast? = some p) (pg : List w8)
    (hpg : v.pages !! p = some pg) (hf : pageFlags pg = branchPageFlag) :
    e.index'.toNat + 1 = pageCount pg := by
  rcases htl e p he hpl with ⟨pg', hpg', -, h⟩ | ⟨h0 | ⟨pg', hpg', hl⟩, -⟩
  · rw [hpg] at hpg'; cases hpg'; exact h
  · subst h0; have := (Read.viewWF_page _ hv _ _ hpg).1; omega
  · rw [hpg] at hpg'; cases hpg'; exact (flag_ne hf hl).elim

/-- **Pushing the last child**: from a branch top at view page `pg` on an entry, the reference
`pageNode` returns for its child `c`, at index `count - 1` (`ws` its entries), keeps `last`'s loop
invariant: a prefix, its top at its last index, its leaf page's entries; the levels from `k` on at
their last index if they were and the old top is (when at least `k` deep). -/
theorem push_last (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (ipg : List w8) (els : List elemRef) (pids : List Nat)
    (hp : sPrefix (nlX X) X.v bl rt els pids) (k : Nat)
    (hbl : ∀ j pid e0, pids[j]? = some pid → els[j]? = some e0 → k ≤ j → j + 1 < els.length →
      e0.index'.toNat + 1 = (pidKeys X.v pid).length)
    (e : elemRef) (p : Nat)
    (he : els.getLast? = some e) (hpl : pids.getLast? = some p) (pg : List w8)
    (hpg : X.v.pages !! p = some pg) (hf : pageFlags pg = branchPageFlag)
    (hi : e.index'.toNat < pageCount pg)
    (hil : k ≤ els.length - 1 → e.index'.toNat + 1 = pageCount pg) (h0 : B.ib.root' ≠ W64 0) (p' n' : Loc)
    (lf : Bool) (ws : List WEntry)
    (hL : ltree X bl (W64 (branchPgid pg e.index'.toNat : Int)) = some (lf, ws))
    (hra : ∀ i, refAt X bl (W64 (branchPgid pg e.index'.toNat : Int)) ⟨p', n', i⟩)
    (hbr : lf = false → ∃ pgx, X.v.pages !! (branchPgid pg e.index'.toNat) = some pgx ∧
        pageFlags pgx = branchPageFlag ∧ ws.length = pageCount pgx ∧ 0 < pageCount pgx)
    (hwl : ws.length < 2 ^ 63) :
    let e' : elemRef := ⟨p', n', W64 ((ws.length : Int) - 1)⟩
    let c := branchPgid pg e.index'.toNat
    sPrefix (nlX X) X.v bl rt (els ++ [e']) (pids ++ [c]) ∧
    (∀ j pid e0, (pids ++ [c])[j]? = some pid → (els ++ [e'])[j]? = some e0 → k ≤ j →
      j + 1 < (els ++ [e']).length → e0.index'.toNat + 1 = (pidKeys X.v pid).length) ∧
    sTopLast X.v (wEs X n) (pids ++ [c]) (els ++ [e']) ∧
    (sPathR (nlX X) X.v bl rt (els ++ [e']) (pids ++ [c]) →
      sLeafOK X.v ipg (wEs X n) (pids ++ [c]) (els ++ [e'])) := by
  intro e' c
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hlen : pids.length = els.length := hp.2.1
  have hpos : 0 < els.length := List.length_pos_iff.2 hp.1
  obtain ⟨pgc, hpgc⟩ : ∃ pgc, X.v.pages !! c = some pgc := viewWF_child _ hv _ _ hpg hf _ hi
  have hc2 : 2 ≤ c := (Read.viewWF_page _ hv _ _ hpgc).1
  have hclt : c < 2 ^ 64 := branchPgid_lt _ _
  have hC : (W64 (c : Int)).toNat = c := W64_toNat_lt c hclt
  obtain ⟨P1, P2, P3, P4, P5⟩ := pos_facts X bl B hok hB hc.2.2.1 hbase _ e' lf ws (hra _) hL
    (fun h => absurd h h0)
  rw [hC] at P1 P2 P3 P4 P5
  have hget : ∀ j e0 p0, (els ++ [e'])[j]? = some e0 → (pids ++ [c])[j]? = some p0 →
      (j < els.length ∧ els[j]? = some e0 ∧ pids[j]? = some p0) ∨
      (j = els.length ∧ e0 = e' ∧ p0 = c) := by
    intro j e0 p0 h1 h2
    by_cases hj : j < els.length
    · left
      rw [List.getElem?_append_left hj] at h1
      rw [List.getElem?_append_left (by omega)] at h2
      exact ⟨hj, h1, h2⟩
    · right
      rw [List.getElem?_append_right (by omega)] at h1
      rw [List.getElem?_append_right (by omega)] at h2
      have hj' : j - els.length = 0 := by
        rcases Nat.eq_zero_or_pos (j - els.length) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by simp; omega)] at h1; cases h1
      rw [hj'] at h1
      rw [hlen, hj'] at h2
      simp at h1 h2
      exact ⟨by omega, h1.symm, h2.symm⟩
  have hlast : (els ++ [e']).getLast? = some e' := by simp
  have hplast : (pids ++ [c]).getLast? = some c := by simp
  have hidx : ∀ k : Nat, k ≠ 0 → k < 2 ^ 63 → (W64 ((k : Int) - 1)).toNat + 1 = k := by
    intro k hk hk'
    have : (W64 ((k : Int) - 1)).toNat = k - 1 := by
      rw [show ((k : Int) - 1) = ((k - 1 : Nat) : Int) by omega]
      exact W64_toNat_lt _ (by omega)
    omega
  have hpre : sPrefix (nlX X) X.v bl rt (els ++ [e']) (pids ++ [c]) := by
    refine ⟨by simp, by simp [hlen], ?_, fun j e0 p0 h1 h2 => ?_⟩
    · cases pids with
      | nil => simp at hlen; omega
      | cons a t => simpa using hp.2.2.1
    · rcases hget j e0 p0 h1 h2 with ⟨hj, h1', h2'⟩ | ⟨rfl, rfl, rfl⟩
      · obtain ⟨a1, a2, a3, -⟩ := hp.2.2.2 j e0 p0 h1' h2'
        refine ⟨a1, a2, fun hj1 => ?_, fun hj1 => by simp at hj1; omega⟩
        by_cases hj2 : j + 1 < els.length
        · obtain ⟨pg', h1, h2, h3, h4⟩ := a3 hj2
          exact ⟨pg', h1, h2, h3, by rw [List.getElem?_append_left (by omega)]; exact h4⟩
        · have hjl : j = els.length - 1 := by omega
          subst hjl
          rw [getLast_idx els e he] at h1'; cases h1'
          rw [← hlen, getLast_idx pids p hpl] at h2'; cases h2'
          refine ⟨pg, hpg, hf, hi, ?_⟩
          rw [show els.length - 1 + 1 = pids.length by omega]
          simp [c]
      · refine ⟨P1, P2, fun hj1 => by simp at hj1, fun _ => Or.inr ?_⟩
        cases lf with
        | false =>
          obtain ⟨pg', hpg', hb', hwl', hcnt⟩ := hbr rfl
          refine ⟨pg', hpg', Or.inr ⟨hb', ?_⟩⟩
          have := hidx ws.length (by omega) hwl
          show (W64 ((ws.length : Int) - 1)).toNat < pageCount pg'
          omega
        | true =>
          rcases P4 rfl with h | ⟨pg', hpg', hl'⟩
          · omega
          · exact ⟨pg', hpg', Or.inl hl'⟩
  have hleafOK : sPathR (nlX X) X.v bl rt (els ++ [e']) (pids ++ [c]) →
      sLeafOK X.v ipg (wEs X n) (pids ++ [c]) (els ++ [e']) := by
    intro hpath e0 p0 h1 h2 hnull
    rw [hlast] at h1; cases h1
    rw [hplast] at h2; cases h2
    obtain ⟨ws0, hL0, hents, -, hplain, -⟩ :=
      wStk_top X n bl rt B hc hB hbase (nlX X) _ _ hpath (fun _ _ _ => rfl) e' c hlast hplast
    rw [hL] at hL0
    simp only [Option.some.injEq, Prod.mk.injEq] at hL0
    obtain ⟨-, rfl⟩ := hL0
    obtain ⟨pg', hlp, hws, -⟩ := P5 hnull
    refine ⟨pg', ?_, by rw [← hws]; exact hplain, ?_, fun h => by omega⟩
    · unfold leafPgAt at hlp ⊢; rw [if_neg (by omega)] at hlp ⊢; exact hlp
    · unfold pgEnts; rw [← hws]; exact hents
  refine ⟨hpre, fun j pid0 e0 h1 h2 hk hj => ?_, fun e0 p0 h1 h2 => ?_, hleafOK⟩
  · rcases hget j e0 pid0 h2 h1 with ⟨hj', h2', h1'⟩ | ⟨rfl, -, -⟩
    · by_cases hj2 : j + 1 < els.length
      · exact hbl j pid0 e0 h1' h2' hk hj2
      · have hjl : j = els.length - 1 := by omega
        subst hjl
        rw [getLast_idx els e he] at h2'; cases h2'
        rw [← hlen, getLast_idx pids p hpl] at h1'; cases h1'
        rw [pidKeys_length X.v _ pg hpg]; exact hil (by omega)
    · simp at hj
  · rw [hlast] at h1; cases h1
    rw [hplast] at h2; cases h2
    cases lf with
    | false =>
      obtain ⟨pg', hpg', hb', hwl', hcnt⟩ := hbr rfl
      left
      refine ⟨pg', hpg', hb', ?_⟩
      have := hidx ws.length (by omega) hwl
      show (W64 ((ws.length : Int) - 1)).toNat + 1 = pageCount pg'
      omega
    | true =>
      right
      have hpath : sPathR (nlX X) X.v bl rt (els ++ [e']) (pids ++ [c]) :=
        sPrefix_sPathR _ _ _ _ _ _ hpre (fun e1 p1 h1 h2 => by
          rw [hplast] at h2; cases h2
          rcases P4 rfl with h | h
          · exact Or.inl h
          · exact Or.inr h)
      obtain ⟨ws0, hL0, -, hcnt0, -, -⟩ :=
        wStk_top X n bl rt B hc hB hbase (nlX X) _ _ hpath (fun _ _ _ => rfl) e' c hlast hplast
      rw [hL] at hL0
      simp only [Option.some.injEq, Prod.mk.injEq] at hL0
      obtain ⟨-, rfl⟩ := hL0
      refine ⟨?_, ?_⟩
      · rcases P4 rfl with h | h
        · exact Or.inl h
        · exact Or.inr h
      · show W64 ((ws.length : Int) - 1) = _
        rw [hcnt0]

end pure

end WLast

end bbolt
end EtcdGrove
end Perennial
