/-
`node.spill` after its children's loop (U9w2, `notes/bbolt-proof-plan.md`; pure): **the pieces'
entries at the loop's start** (`tail_init_ents`, `pcInv_init`'s `Es`, `Ds`, `pcEnts` and slots'
bookkeeping): `n`'s global families (`tail_glob`) cut at the pieces' lengths (`cutF`), each
piece's bound of its entries the global one (`childHi_cut`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitGlob
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitCut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section ents

/-- **Piece `k`'s part, for every family** (`cutF_get` with one offset for all families). -/
theorem cutF_get_all {α : Type} (wss : List (List α)) (k : Nat) (ws : List α)
    (h : wss[k]? = some ws) :
    ∃ o, (∀ (β : Type) (f : Nat → List β), (cutF (wss.map List.length) f)[k]? =
        some ((List.range ws.length).flatMap (fun m => f (o + m)))) ∧
      (∀ m, m < ws.length → wss.flatten[o + m]? = ws[m]?) ∧
      wss.flatten.drop (o + ws.length) = (wss.drop (k + 1)).flatten := by
  induction wss generalizing k with
  | nil => simp at h
  | cons a rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      refine ⟨0, fun β f => ?_, ?_, ?_⟩
      · simp [cutF]
      · intro m hm
        simp only [Nat.zero_add, List.flatten_cons]
        rw [List.getElem?_append_left hm]
      · simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨o, h1, h2, h3⟩ := ih k h
      refine ⟨a.length + o, fun β f => ?_, ?_, ?_⟩
      · simp only [List.map_cons, cutF, List.getElem?_cons_succ, h1 β (fun g => f (a.length + g)),
          Nat.add_assoc]
      · intro m hm
        rw [List.flatten_cons, show a.length + o + m = a.length + (o + m) by omega,
          List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        exact h2 m hm
      · rw [List.flatten_cons, show a.length + o + ws.length = a.length + (o + ws.length) by omega,
          List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          Nat.add_sub_cancel_left, h3, List.drop_succ_cons]

variable [GooseExts] [GoGlobalContext]

/-- **The pieces' entries at the loop's start** (see the module doc). -/
theorem tail_init_ents {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp' : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp') :
    ∃ (Es : List (List El)) (Ds : List (List Nat)),
      Es.length = xs.length ∧ Ds.length = xs.length ∧ Es.flatten = E ∧
      pcEnts (spP X') X'.t.mv.pgid'.toNat r'.nv.isLeaf' hi (h - 1) wss Es Ds ∧
      (∀ s ∈ D, s ∈ ownSl X'.v r'.nv.pgid' ++ Ds.flatten ∨ s ∈ pendSlots w'.fl) ∧
      (∀ s ∈ ownSl X'.v r'.nv.pgid' ++ Ds.flatten, s ∈ D ∨ newSlot st X.t.mv.pgid'.toNat s) ∧
      (∀ x, spP X' !! x ≠ spP X !! x → x ∉ D) ∧
      slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ (ownSl X'.v r'.nv.pgid' ++ Ds.flatten)) := by
  obtain ⟨Sb, Eb, hE, hDk, hDn, hPd, hsl, hent⟩ := tail_glob hpre hsp hend
  have hws : wss.flatten = r'.ws := hsr.ws
  have hsum : (wss.map List.length).sum = r'.ws.length := by
    rw [← hws, List.length_flatten]
  let fE : Nat → List El := fun m =>
    if r'.nv.isLeaf' = true then (r'.ws[m]?).toList.map wEl else Eb m
  let fD : Nat → List Nat := fun m => pgSlots (spP X') (Sb m)
  have hDf : (cutF (wss.map List.length) fD).flatten =
      (List.range r'.ws.length).flatMap fD := by rw [cutF_flatten, hsum]
  have hne : ∀ (k' : Nat) (ws' : List WEntry), wss[k']? = some ws' → 2 ≤ wss.length →
      0 < ws'.length := by
    intro k' ws' hk' h2
    have hlt : k' < xs.length := by rw [← hsr.len]; exact (List.getElem?_eq_some_iff.1 hk').1
    exact (hsr.plen k' _ ws' (List.getElem?_eq_getElem hlt) hk').2 (by rw [← hsr.len]; exact h2)
  refine ⟨cutF (wss.map List.length) fE, cutF (wss.map List.length) fD,
    by rw [cutF_length, List.length_map, hsr.len], by rw [cutF_length, List.length_map, hsr.len],
    by rw [cutF_flatten, hsum, hE], ?_, by rw [hDf]; exact hDk, by rw [hDf]; exact hDn, hPd,
    by rw [hDf]; exact hsl⟩
  intro k ws hk
  obtain ⟨o, hgf, hg, hdrop⟩ := cutF_get_all wss k ws hk
  have hge : ∀ m e, ws[m]? = some e → r'.ws[o + m]? = some e := by
    intro m e he
    have hm : m < ws.length := (List.getElem?_eq_some_iff.1 he).1
    rw [← hws, hg m hm, he]
  refine ⟨fun m => Sb (o + m), fun m => Eb (o + m), ?_, ?_, fun m e he => ?_⟩
  · rw [List.getD_eq_getElem?_getD, hgf Nat fD]; rfl
  · rw [List.getD_eq_getElem?_getD, hgf El fE]
    simp only [Option.getD_some]
    by_cases hlf : r'.nv.isLeaf' = true
    · rw [if_pos hlf, map_eq_range ws wEl]
      refine flatMap_congr_mem fun m hm => ?_
      have hm' : m < ws.length := List.mem_range.1 hm
      show (if r'.nv.isLeaf' = true then _ else _) = _
      rw [if_pos hlf, hge m _ (List.getElem?_eq_getElem hm'), List.getElem?_eq_getElem hm']
    · rw [if_neg hlf]
      refine flatMap_congr_mem fun m _ => ?_
      show (if r'.nv.isLeaf' = true then _ else _) = _
      rw [if_neg hlf]
  · have hm : m < ws.length := (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨h1, h2⟩ := hent (o + m) e (hge m e he)
    refine ⟨h1, fun hl => ?_⟩
    have := h2 hl
    rw [← hws] at this
    rw [childHi_cut hk hdrop hg hne hm] at this
    exact this

end ents

end Spill

end bbolt
end EtcdGrove
end Perennial
