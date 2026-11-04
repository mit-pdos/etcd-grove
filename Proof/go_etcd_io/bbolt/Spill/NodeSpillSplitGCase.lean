/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`; pure): **`spG` across the split**, the
records `splitRel_top` and `splitRel_child` put (`spG_top`, `spG_child`; unsplit, the records are
`X1`'s: `splitX_one_eq`). A top node's split needs `n` to be the root of its bucket's root node
(`b.rootNode` is `n` when `n` has no parent).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitRecs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitG

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section gcase
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
variable {X1 : WX} {bl n : Loc} {rN : NRec} {B : BRec}

theorem pieceRecs_mem_inv {one : Bool} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {b : Bool} {p : Loc × NRec} (hp : p ∈ pieceRecs rN one xs wss b) :
    ∃ i x w, xs[i]? = some x ∧ wss[i]? = some w ∧ p = (x.1, splitRec rN x w (b && decide (i = 0)) one) := by
  induction xs generalizing wss b with
  | nil => cases wss <;> simp [pieceRecs] at hp
  | cons y xs ih =>
    cases wss with
    | nil => simp [pieceRecs] at hp
    | cons v wss =>
      simp only [pieceRecs, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨0, y, v, rfl, rfl, by simp⟩
      · obtain ⟨i, x, w, hx, hw, rfl⟩ := ih hp
        exact ⟨i + 1, x, w, hx, hw, by simp⟩

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem cutWs_mem {α : Type} (ps : List (List α)) (ws : List WEntry) (i : Nat) (w : List WEntry)
    (hw : (cutWs ps ws)[i]? = some w) (e : WEntry) (he : e ∈ w) : e ∈ ws := by
  induction ps generalizing ws i with
  | nil => simp [cutWs] at hw
  | cons a ps ih =>
    cases i with
    | zero =>
      simp only [cutWs, List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw; exact List.mem_of_mem_take he
    | succ i =>
      simp only [cutWs, List.getElem?_cons_succ] at hw
      exact List.mem_of_mem_drop (ih _ i hw)

/-- **A piece's record**: entries among `n`'s, its bucket's, under `pl`; `n`'s (its children and
key) or a fresh one (none). -/
theorem piece_rec_facts {ps : Nat} {pl : Loc} {xs : List (Loc × node × List Inode)}
    (hsh : piecesShape ps n rN.nv pl xs) (p : Loc × NRec)
    (hp : p ∈ pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true) :
    (∀ w ∈ p.2.ws, w ∈ rN.ws) ∧ p.2.nv.bucket' = rN.nv.bucket' ∧ p.2.nv.parent' = pl ∧
    ((p.1 = n ∧ p.2.cs = rN.cs ∧ p.2.key = rN.key ∧ p.2.ksrc = rN.ksrc ∧
        p.2.nv.key' = rN.nv.key') ∨
      (p.1 ∈ (xs.drop 1).map (·.1) ∧ p.2.cs = [] ∧ p.2.nv.key' = slice.nil)) := by
  obtain ⟨i, x, w, hx, hw, rfl⟩ := pieceRecs_mem_inv hp
  obtain ⟨fb, -, -, -, fpa, -, fk, f0⟩ := piece_fields hsh i x hx
  have hws : ∀ e ∈ w, e ∈ rN.ws := cutWs_mem _ _ i w hw
  by_cases hi : i = 0
  · subst hi
    simp only [decide_true, Bool.true_and, splitRec, ↓reduceIte]
    refine ⟨hws, fb, fpa, Or.inl ⟨f0 rfl, ?_, ?_, ?_, by simpa using fk⟩⟩ <;> first | rfl | trivial
  · simp only [hi, decide_false, Bool.and_false, splitRec, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hws, fb, fpa, Or.inr ⟨List.mem_map.2 ⟨x, mem_drop_one_of hx hi, rfl⟩, ?_, ?_⟩⟩
    · first | rfl | trivial
    · simpa [hi] using fk

/-- `n`'s facts in `spG X1`. -/
theorem spG_node {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X1 txid ml fl)
    (hb : X1.t.bs !! bl = some B) (hrn : B.ns !! n = some rN) (hlv : n ∈ X1.live) :
    (∀ w ∈ rN.ws, 0 < w.key.length) ∧ (rN.nv.key' = slice.nil ∨ 0 < rN.key.length) ∧
    (∀ c ∈ rN.cs, c ∈ X1.live ∧ (B.ns !! c).isSome) ∧ wsLive rN.ws ∧
    (rN.nv.key' ≠ slice.nil → rN.ksrc ≠ Src.stale) := by
  obtain ⟨-, -, ⟨dA, -⟩, hF, -⟩ := hG
  obtain ⟨-, a, b, c⟩ := dA bl B n rN hb hrn hlv
  obtain ⟨d, e⟩ := hF bl B n rN hb hrn hlv
  exact ⟨a, b, c, d, e⟩

/-- **`spG` across the split of a top node** (`n` the root of the bucket's root node). -/
theorem spG_top {ps : Nat} {pl : Loc} {xs : List (Loc × node × List Inode)} {pv' : node}
    (hb : X1.t.bs !! bl = some B) (hrn : B.ns !! n = some rN) (hlv : n ∈ X1.live)
    (hbl : rN.nv.bucket' = bl) (h0 : rN.nv.parent' = null) (hsh : piecesShape ps n rN.nv pl xs)
    (hpl : pl ≠ null) (hpv : pv' = newParent rN.nv pv'.children')
    (hnd : (((pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).take 1 ++
      ((pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).drop 1 ++
        [(pl, newParRec pv' (xs.map (·.1)))])).map (·.1)).Nodup)
    (hfresh : ∀ x ∈ xs.drop 1, X1.t.objs !! x.1 = none) (hplf : X1.t.objs !! pl = none)
    (hrt : ∀ rt, nodeRootIn B B.bv.rootNode' rt → rt = n)
    {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X1 txid ml fl) :
    spG (splitX X1 bl B ((pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).take 1)
      ((pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).drop 1 ++
        [(pl, newParRec pv' (xs.map (·.1)))])) txid ml fl := by
  have hfacts := fun q hq => piece_rec_facts hsh q hq
  have hnn : ∀ x ∈ xs.drop 1, x.1 ≠ null := by
    obtain ⟨-, x0', rest', hd', -, -, hrest⟩ := hsh
    rw [hd']; intro x hx; exact (hrest x hx).1
  have hlen : (cutWs (xs.map (·.2.2)) rN.ws).length = xs.length := by simp [cutWs_length]
  have hfst : (pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).map (·.1) = xs.map (·.1) :=
    pieceRecs_fst rN false xs _ true hlen
  have hdrop := pieceRecs_drop_fst rN xs
  obtain ⟨x0, rest, hd, hx0n⟩ : ∃ x0 rest, xs = x0 :: rest ∧ x0.1 = n := by
    obtain ⟨-, x0, rest, hd, h, -⟩ := hsh; exact ⟨x0, rest, hd, h⟩
  have hhead : (n, splitRec rN x0 ((cutWs (xs.map (·.2.2)) rN.ws).headD []) true false) ∈
      pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true := by
    rw [hd]; simp [pieceRecs, cutWs, hx0n]
  have hpar0 : (newParRec pv' (xs.map (·.1))).nv.parent' = null := by
    simp only [newParRec]; rw [hpv]; rfl
  have hparb : (newParRec pv' (xs.map (·.1))).nv.bucket' = rN.nv.bucket' := by
    simp only [newParRec]; rw [hpv]; rfl
  have hpark : (newParRec pv' (xs.map (·.1))).nv.key' = slice.nil := by
    simp only [newParRec]; rw [hpv]; rfl
  have hparc : (newParRec pv' (xs.map (·.1))).cs = xs.map (·.1) := rfl
  have hparw : (newParRec pv' (xs.map (·.1))).ws = [] := rfl
  generalize pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true = recs at hfacts hfst hdrop hhead hnd ⊢
  generalize hpar : (pl, newParRec pv' (xs.map (·.1))) = par at hnd ⊢
  generalize newParRec pv' (xs.map (·.1)) = rq at hpar hpar0 hparb hpark hparc hparw
  subst hpar
  have happ : recs.take 1 ++ (recs.drop 1 ++ [(pl, rq)]) = recs ++ [(pl, rq)] := by
    rw [← List.append_assoc, List.take_append_drop]
  have htake : (recs.take 1).map (·.1) = [n] := by
    rw [List.map_take, hfst, hd]; simp [hx0n]
  obtain ⟨nk, nkey, ncs, nwl, nks⟩ := spG_node hG hb hrn hlv
  let B2ns := nsIns B.ns (recs.take 1 ++ (recs.drop 1 ++ [(pl, rq)]))
  have hin : ∀ q ∈ recs ++ [(pl, rq)], B2ns !! q.1 = some q.2 := by
    intro q hq; rw [← happ] at hq; exact nsIns_in _ _ hnd q hq
  have hmemL : ∀ l, l ∈ (recs.take 1 ++ (recs.drop 1 ++ [(pl, rq)])).map (·.1) ↔
      l ∈ xs.map (·.1) ∨ l = pl := by
    intro l; rw [happ, List.map_append, hfst]; simp
  -- the fresh nodes
  have hnewL : ∀ l, l ∈ (recs.drop 1 ++ [(pl, rq)]).map (·.1) ↔ l ∈ (xs.drop 1).map (·.1) ∨ l = pl := by
    intro l; rw [List.map_append, hdrop]; simp
  have hnewF : ∀ l, l ∈ (xs.drop 1).map (·.1) → X1.t.objs !! l = none := by
    intro l hl; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl; exact hfresh x hx
  -- every node of `B` but `n` untouched
  have hB0 : ∀ x r, B.ns !! x = some r → x ≠ n → B2ns !! x = some r := by
    intro x r hx hxn
    rw [show B2ns = nsIns B.ns (recs.take 1 ++ (recs.drop 1 ++ [(pl, rq)])) from rfl, nsIns_out]
    · exact hx
    · intro hm
      rcases (hmemL x).1 hm with hm | rfl
      · rw [hd] at hm
        simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with e | hm
        · exact hxn (e.trans hx0n)
        · have := Write.objs_none X1.t x (hnewF x (by rw [hd]; exact hm)) bl B hb
          rw [hx] at this; cases this
      · have := Write.objs_none X1.t x hplf bl B hb
        rw [hx] at this; cases this
  have hn2 := hin _ (List.mem_append_left _ hhead)
  have hpar2 := hin (pl, rq) (List.mem_append_right _ (List.mem_singleton_self _))
  have hx0p : (splitRec rN x0 ((cutWs (xs.map (·.2.2)) rN.ws).headD []) true false).nv.parent' = pl := by
    have := (piece_fields hsh 0 x0 (by rw [hd]; rfl)).2.2.2.2.1
    simp only [splitRec, ↓reduceIte]; exact this
  have hroot2 : ∀ rt, nodeRootIn B B.bv.rootNode' rt →
      nodeRootIn { B with ns := B2ns } B.bv.rootNode' pl := by
    intro rt h
    have e := hrt rt h
    have := nodeRootIn_tr_top (B2 := { B with ns := B2ns }) (n := n) (pl := pl)
      (fun x r hx hxn => ⟨r, hB0 x r hx hxn, rfl⟩) hrn h0 hn2 hx0p hpl hpar2 hpar0 h
    rw [if_pos e] at this; exact this
  -- the children of the put records grow
  have hcs : ∀ x r, B.ns !! x = some r → ∃ r', B2ns !! x = some r' ∧ ∀ c ∈ r.cs, c ∈ r'.cs := by
    intro x r hx
    by_cases hxn : x = n
    · subst hxn; rw [hrn] at hx; cases hx
      refine ⟨_, hn2, fun c hc => ?_⟩
      simp only [splitRec, ↓reduceIte]; exact hc
    · exact ⟨r, hB0 x r hx hxn, fun c hc => hc⟩
  have hparcs : ∀ x ∈ xs, descIn { B with ns := B2ns } pl x.1 := fun x hx =>
    descIn.child pl x.1 x.1 _ hpar2 (by rw [hparc]; exact List.mem_map.2 ⟨x, hx, rfl⟩)
      (descIn.self _)
  refine spG_splitX hb hnd ?_ ?_ ?_ ?_ ?_ hG
  · intro q hq
    have : q.1 ∈ (recs.take 1).map (·.1) := List.mem_map.2 ⟨q, hq, rfl⟩
    rw [htake, List.mem_singleton] at this
    rw [this, hrn]; rfl
  · intro q hq
    have hm := (hnewL q.1).1 (List.mem_map.2 ⟨q, hq, rfl⟩)
    rcases hm with hm | e
    · refine ⟨hnewF _ hm, ?_⟩
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
      rw [← e]; exact hnn x hx
    · rw [e]; exact ⟨hplf, hpl⟩
  · intro q hq
    rw [happ] at hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨hws, hbk, -, hcase⟩ := hfacts q hq
      refine ⟨hbk.trans hbl, fun w hw => nk w (hws w hw), ?_, ?_, fun w hw => nwl w (hws w hw), ?_⟩
      · rcases hcase with ⟨-, -, hk, -, hk'⟩ | ⟨-, -, hk'⟩
        · rw [hk, hk']; exact nkey
        · exact Or.inl hk'
      · intro c hc
        rcases hcase with ⟨-, hc', -⟩ | ⟨-, hc', -⟩
        · rw [hc'] at hc
          exact ⟨Or.inl (ncs c hc).1, by
            by_cases hcn : c = n
            · rw [hcn, hn2]; rfl
            · obtain ⟨rc, hrc⟩ := Option.isSome_iff_exists.1 (ncs c hc).2
              rw [hB0 c rc hrc hcn]; rfl⟩
        · rw [hc'] at hc; cases hc
      · rcases hcase with ⟨-, -, -, hks, hk'⟩ | ⟨-, -, hk'⟩
        · rw [hks, hk']; exact nks
        · intro h; exact absurd hk' h
    · simp only [List.mem_singleton] at hq; subst hq
      refine ⟨hparb.trans hbl, by simp [hparw], Or.inl hpark, fun c hc => ?_, by simp [hparw, wsLive],
        fun h => absurd hpark h⟩
      · rw [hparc] at hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
        refine ⟨?_, ?_⟩
        · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
          by_cases h0i : i = 0
          · subst h0i; rw [hd] at hi; simp at hi; subst hi; rw [hx0n]; exact Or.inl hlv
          · right; exact (hnewL _).2 (Or.inl (List.mem_map.2 ⟨x, mem_drop_one_of hi h0i, rfl⟩))
        · have : x.1 ∈ recs.map (·.1) := by rw [hfst]; exact List.mem_map.2 ⟨x, hx, rfl⟩
          obtain ⟨q, hq, e⟩ := List.mem_map.1 this
          rw [← e, hin q (List.mem_append_left _ hq)]; rfl
  · intro _ hrn0
    obtain ⟨-, -, -, -, ⟨-, rN''⟩, -⟩ := hG
    obtain ⟨rt, h, -⟩ := rN'' bl B n rN hb hrn hlv
    exact ⟨pl, hroot2 rt h, Or.inr ((hnewL pl).2 (Or.inr rfl))⟩
  · intro l r hl hlv'
    obtain ⟨-, -, -, -, ⟨-, rN''⟩, -⟩ := hG
    obtain ⟨rt0, h0', -⟩ := rN'' bl B n rN hb hrn hlv
    refine ⟨pl, hroot2 rt0 h0', ?_⟩
    rcases hlv' with hlv' | hnew
    · -- a node live before: below `n`, or `n` itself
      by_cases hm : l ∈ (recs.take 1 ++ (recs.drop 1 ++ [(pl, rq)])).map (·.1)
      · rcases (hmemL l).1 hm with hm | rfl
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm; exact hparcs x hx
        · exact descIn.self _
      · rw [nsIns_out _ _ _ hm] at hl
        obtain ⟨rt, h, hdsc⟩ := rN'' bl B l r hb hl hlv'
        rw [hrt rt h] at hdsc
        have := descIn_tr (B2 := { B with ns := B2ns }) hcs hdsc
        exact descIn.child pl n l _ hpar2
          (by rw [hparc, hd]; simp [hx0n]) this
    · rcases (hnewL l).1 hnew with hm | rfl
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
        exact hparcs x (List.mem_of_mem_drop hx)
      · exact descIn.self _

end gcase

end Spill

end bbolt
end EtcdGrove
end Perennial
