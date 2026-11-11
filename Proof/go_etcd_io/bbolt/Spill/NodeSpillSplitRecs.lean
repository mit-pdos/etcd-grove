/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`; pure): **the records after the split**.
The entries cut at the pieces (`cutWs`), the pieces' records (`pieceRecs`, `splitRec`'s), and
`splitRel` for the records put by `splitX`: unsplit (`splitRel_one`), split under a new parent
(`splitRel_top`) or under `n`'s parent (`splitRel_child`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitPut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section cut
variable [GooseExts]

/-- **The entries cut at the pieces' inode counts** (`ps` the pieces' inodes). -/
def cutWs {α : Type} : List (List α) → List WEntry → List (List WEntry)
  | [], _ => []
  | a :: ps, ws => ws.take a.length :: cutWs ps (ws.drop a.length)

omit [GooseExts] in
theorem cutWs_length {α : Type} (ps : List (List α)) (ws : List WEntry) :
    (cutWs ps ws).length = ps.length := by
  induction ps generalizing ws with
  | nil => rfl
  | cons a ps ih => simp [cutWs, ih]

omit [GooseExts] in
theorem cutWs_flatten {α : Type} (ps : List (List α)) (ws : List WEntry)
    (h : ps.flatten.length = ws.length) : (cutWs ps ws).flatten = ws := by
  induction ps generalizing ws with
  | nil => simp at h; simp [cutWs, List.length_eq_zero_iff.1 h.symm]
  | cons a ps ih =>
    simp only [cutWs, List.flatten_cons]
    simp only [List.flatten_cons, List.length_append] at h
    rw [ih (ws.drop a.length) (by simp only [List.length_drop]; omega), List.take_append_drop]

omit [GooseExts] in
theorem cutWs_get {α : Type} (ps : List (List α)) (ws : List WEntry)
    (h : ps.flatten.length = ws.length) (i : Nat) (a : List α) (w : List WEntry)
    (ha : ps[i]? = some a) (hw : (cutWs ps ws)[i]? = some w) : w.length = a.length := by
  induction ps generalizing ws i with
  | nil => simp at ha
  | cons b ps ih =>
    simp only [List.flatten_cons, List.length_append] at h
    cases i with
    | zero =>
      simp only [cutWs, List.getElem?_cons_zero, Option.some.injEq] at ha hw
      subst ha hw; simp; omega
    | succ i =>
      simp only [cutWs, List.getElem?_cons_succ] at ha hw
      exact ih (ws.drop b.length) (by simp only [List.length_drop]; omega) i ha hw

end cut

section recs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The pieces' records** (the first `b`), `splitRec`'s. -/
def pieceRecs (rN : NRec) (one : Bool) :
    List (Loc × node × List Inode) → List (List WEntry) → Bool → List (Loc × NRec)
  | x :: xs, w :: ws, b => (x.1, splitRec rN x w b one) :: pieceRecs rN one xs ws false
  | _, _, _ => []

theorem pieceRecs_fst (rN : NRec) (one : Bool) (xs : List (Loc × node × List Inode))
    (ws : List (List WEntry)) (b : Bool) (h : ws.length = xs.length) :
    (pieceRecs rN one xs ws b).map (·.1) = xs.map (·.1) := by
  induction xs generalizing ws b with
  | nil => cases ws <;> rfl
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      simp only [pieceRecs, List.map_cons]
      rw [ih ws false (by simpa using h)]

theorem pieceRecs_mem (rN : NRec) (one : Bool) (xs : List (Loc × node × List Inode))
    (ws : List (List WEntry)) (b : Bool) (i : Nat) (x : Loc × node × List Inode)
    (w : List WEntry) (hx : xs[i]? = some x) (hw : ws[i]? = some w) :
    (x.1, splitRec rN x w (b && decide (i = 0)) one) ∈ pieceRecs rN one xs ws b := by
  induction xs generalizing ws b i with
  | nil => simp at hx
  | cons y xs ih =>
    cases ws with
    | nil => simp at hw
    | cons v ws =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hw
        subst hx hw
        simp [pieceRecs]
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx hw
        have := ih ws false i hx hw
        simp only [Bool.false_and] at this
        simp only [pieceRecs, List.mem_cons]
        right
        simpa using this

/-- The struct of a piece after the first. -/
theorem pieceStruct_fields (nv : node) (pl : Loc) (s : GoSlice) :
    (pieceStruct nv pl s).bucket' = nv.bucket' ∧ (pieceStruct nv pl s).isLeaf' = nv.isLeaf' ∧
    (pieceStruct nv pl s).spilled' = false ∧ (pieceStruct nv pl s).pgid' = W64 0 ∧
    (pieceStruct nv pl s).parent' = pl ∧ (pieceStruct nv pl s).children' = slice.nil ∧
    (pieceStruct nv pl s).key' = slice.nil :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An unsplit node's record. -/
theorem splitRec_self (rN : NRec) (n : Loc) (hcap : rN.capOwn = true) :
    splitRec rN (n, rN.nv, rN.ins) rN.ws true true = rN := by
  cases rN; simp only at hcap; subst hcap; rfl

section rel
variable {X1 : WX} {bl n : Loc} {rN : NRec} {B : BRec}

/-- **`splitRel`, unsplit**: the node and its parent (if any) put back as they were. -/
theorem splitRel_one (hb : X1.t.bs !! bl = some B) (hlv : n ∈ X1.live)
    (hbl : rN.nv.bucket' = bl) (hcap : rN.capOwn = true) (hsp : rN.nv.spilled' = false)
    (hil : rN.ins.length = rN.ws.length) (hch : rN.nv.children' = slice.nil)
    (psOld : List (Loc × NRec)) (hnd : (psOld.map (·.1)).Nodup) (hn : (n, rN) ∈ psOld)
    (hold : ∀ p ∈ psOld, B.ns !! p.1 = some p.2)
    (hT : ∀ p ∈ psOld, p.1 = n ∨ p.1 = rN.nv.parent')
    (hpar : rN.nv.parent' ≠ null → ∃ rp, (rN.nv.parent', rp) ∈ psOld) :
    ∃ rp', splitRel0 X1 (splitX X1 bl B psOld []) bl n rN [(n, rN.nv, rN.ins)] [rN.ws]
      rN.nv.parent' rp' := by
  have hnd' : ((psOld ++ ([] : List (Loc × NRec))).map (·.1)).Nodup := by simpa using hnd
  have hnode : ∀ p ∈ psOld, (splitX X1 bl B psOld []).node bl p.1 = some p.2 :=
    fun p hp => splitX_node hnd' p (by simpa using hp)
  have hfr := splitX_frame (psOld := psOld) (psNew := []) hb
    ([(n, rN.nv, rN.ins)].map (·.1) ++ [rN.nv.parent'])
    (fun p hp => by
      simp only [List.append_nil] at hp
      rcases hT p hp with h | h <;> simp [h]) (fun p hp => by cases hp)
  have hrp : ∃ rp', (rN.nv.parent' = null ∧ [(n, rN.nv, rN.ins)].length = 1 ∧ rN.nv.parent' = null) ∨
      (rN.nv.parent' = null ∧ 2 ≤ [(n, rN.nv, rN.ins)].length ∧ rN.nv.parent' ≠ null ∧
        X1.t.objs !! rN.nv.parent' = none ∧
        rp' = newParRec (newParent rN.nv rp'.nv.children') ([(n, rN.nv, rN.ins)].map (·.1)) ∧
        (splitX X1 bl B psOld []).node bl rN.nv.parent' = some rp' ∧
        rN.nv.parent' ∈ (splitX X1 bl B psOld []).live) ∨
      (rN.nv.parent' ≠ null ∧ rN.nv.parent' = rN.nv.parent' ∧ ∃ rp, X1.node bl rN.nv.parent' = some rp ∧
        rp' = { rp with nv := { rp.nv with children' := rp'.nv.children' },
                        cs := rp.cs ++ ([(n, rN.nv, rN.ins)].drop 1).map (·.1) } ∧
        (splitX X1 bl B psOld []).node bl rN.nv.parent' = some rp' ∧
        (rN.nv.parent' ∈ (splitX X1 bl B psOld []).live ↔ rN.nv.parent' ∈ X1.live)) := by
    by_cases h0 : rN.nv.parent' = null
    · exact ⟨rN, Or.inl ⟨h0, rfl, h0⟩⟩
    · obtain ⟨rp, hrp⟩ := hpar h0
      refine ⟨rp, Or.inr (Or.inr ⟨h0, rfl, rp, ?_, by simp, hnode _ hrp, ?_⟩)⟩
      · unfold WX.node; rw [hb]; exact hold _ hrp
      · rw [splitX_live]; simp
  obtain ⟨rp', hpr⟩ := hrp
  refine ⟨rp', ⟨by simp, rfl, by simp, rfl, by simp, by simp, ?_, ?_, by simp, hpr, hfr, rfl, rfl, rfl, rfl⟩⟩
  · intro i x w hx hw
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hw
      subst hx hw
      exact ⟨hil.symm, fun h => by simp at h⟩
    | succ i => simp at hx
  · intro i x w hx hw
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hw
      subst hx hw
      simp only [decide_true, List.length_singleton, ↓reduceIte]
      rw [splitRec_self rN n hcap]
      refine ⟨hnode _ hn, by rw [splitX_live]; exact Or.inl hlv, hbl, ?_, hsp, ?_, ?_, hch, ?_⟩ <;> first | rfl | trivial
    | succ i => simp at hx

/-- The fields of a piece of a split (`piecesShape`), at index `i`. -/
theorem piece_fields {ps : Nat} {pl : Loc} {xs : List (Loc × node × List Inode)}
    (hsh : piecesShape ps n rN.nv pl xs) (i : Nat) (x : Loc × node × List Inode)
    (hx : xs[i]? = some x) :
    x.2.1.bucket' = rN.nv.bucket' ∧ x.2.1.isLeaf' = rN.nv.isLeaf' ∧
    x.2.1.spilled' = (if i = 0 then rN.nv.spilled' else false) ∧
    x.2.1.pgid' = (if i = 0 then rN.nv.pgid' else W64 0) ∧ x.2.1.parent' = pl ∧
    x.2.1.children' = (if i = 0 then rN.nv.children' else slice.nil) ∧
    x.2.1.key' = (if i = 0 then rN.nv.key' else slice.nil) ∧ (i = 0 → x.1 = n) := by
  obtain ⟨-, x0, rest, hd, hx0, hx0s, hrest⟩ := hsh
  subst hd
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    simp only [↓reduceIte]
    rw [hx0s]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => hx0⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hx
    obtain ⟨-, hs⟩ := hrest x (List.mem_of_getElem? hx)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, false_imp_iff, and_true]
    rw [hs]
    exact pieceStruct_fields _ _ _

/-- The pieces' part of `splitRel` for a split (`2 ≤ xs.length`), their records in `X2`. -/
theorem splitRel_pieces {ps : Nat} {pl : Loc} {xs : List (Loc × node × List Inode)} {X2 : WX}
    (hsh : piecesShape ps n rN.nv pl xs) (h2 : 2 ≤ xs.length)
    (hflat : (xs.map (·.2.2)).flatten = rN.ins) (hil : rN.ins.length = rN.ws.length)
    (hbl : rN.nv.bucket' = bl) (hsp : rN.nv.spilled' = false) (hch : rN.nv.children' = slice.nil)
    (hnode : ∀ p ∈ pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true,
      X2.node bl p.1 = some p.2)
    (hlive : ∀ (i : Nat) (x : Loc × node × List Inode), xs[i]? = some x → x.1 ∈ X2.live) :
    (cutWs (xs.map (·.2.2)) rN.ws).length = xs.length ∧
    (cutWs (xs.map (·.2.2)) rN.ws).flatten = rN.ws ∧
    (∀ (i : Nat) (x : Loc × node × List Inode) (w : List WEntry), xs[i]? = some x →
      (cutWs (xs.map (·.2.2)) rN.ws)[i]? = some w →
      w.length = x.2.2.length ∧ (2 ≤ xs.length → 0 < w.length)) ∧
    (∀ (i : Nat) (x : Loc × node × List Inode) (w : List WEntry), xs[i]? = some x →
      (cutWs (xs.map (·.2.2)) rN.ws)[i]? = some w →
      X2.node bl x.1 = some (splitRec rN x w (decide (i = 0)) (decide (xs.length = 1))) ∧
      x.1 ∈ X2.live ∧ x.2.1.bucket' = bl ∧ x.2.1.isLeaf' = rN.nv.isLeaf' ∧
      x.2.1.spilled' = false ∧ x.2.1.pgid' = (if i = 0 then rN.nv.pgid' else W64 0) ∧
      x.2.1.parent' = pl ∧ x.2.1.children' = slice.nil ∧
      x.2.1.key' = (if i = 0 then rN.nv.key' else slice.nil)) := by
  have hfl : (xs.map (·.2.2)).flatten.length = rN.ws.length := by rw [hflat, hil]
  have hx22 : ∀ (i : Nat) (x : Loc × node × List Inode), xs[i]? = some x → (xs.map (·.2.2))[i]? = some x.2.2 := by
    intro i x hx; rw [List.getElem?_map, hx]; rfl
  refine ⟨by simp [cutWs_length], cutWs_flatten _ _ hfl, ?_, ?_⟩
  · intro i x w hx hw
    have e := cutWs_get _ _ hfl i x.2.2 w (hx22 i x hx) hw
    refine ⟨e, fun _ => ?_⟩
    have := (hsh.1 x (List.mem_of_getElem? hx)).2
    omega
  · intro i x w hx hw
    have h1 : decide (xs.length = 1) = false := by simp; omega
    rw [h1]
    have hm := pieceRecs_mem rN false xs _ true i x w hx hw
    simp only [Bool.true_and] at hm
    obtain ⟨fb, fl, fs, fp, fpa, fc, fk, -⟩ := piece_fields hsh i x hx
    refine ⟨hnode _ hm, hlive i x hx, fb.trans hbl, fl, ?_, fp, fpa, ?_, fk⟩
    · rw [fs]; split <;> simp [hsp]
    · rw [fc]; split <;> simp [hch]

/-- A piece's record is its struct's. -/
theorem pieceRecs_inv (one : Bool) (xs : List (Loc × node × List Inode))
    (ws : List (List WEntry)) (b : Bool) (p : Loc × NRec) (hp : p ∈ pieceRecs rN one xs ws b) :
    ∃ x ∈ xs, p.1 = x.1 ∧ p.2.nv = x.2.1 := by
  induction xs generalizing ws b with
  | nil => cases ws <;> simp [pieceRecs] at hp
  | cons y xs ih =>
    cases ws with
    | nil => simp [pieceRecs] at hp
    | cons v ws =>
      simp only [pieceRecs, List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨y, List.mem_cons_self .., rfl, ?_⟩
        unfold splitRec; split <;> rfl
      · obtain ⟨x, hx, h1, h2⟩ := ih ws false hp
        exact ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩

theorem pieceRecs_drop_fst (rN : NRec) (xs : List (Loc × node × List Inode)) :
    ((pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).drop 1).map (·.1) =
      (xs.drop 1).map (·.1) := by
  rw [List.map_drop, pieceRecs_fst rN false xs _ true (by simp [cutWs_length]), List.map_drop]

theorem fresh_of_drop {X1 : WX} {rN : NRec} {xs : List (Loc × node × List Inode)}
    (hfresh : ∀ x ∈ xs.drop 1, X1.t.objs !! x.1 = none) :
    ∀ p ∈ (pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true).drop 1,
      X1.t.objs !! p.1 = none := by
  intro p hp
  have hm : p.1 ∈ (xs.drop 1).map (·.1) := by
    rw [← pieceRecs_drop_fst rN xs]; exact List.mem_map.2 ⟨p, hp, rfl⟩
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  rw [← e]; exact hfresh x hx

/-- A piece after the first is in `xs.drop 1`. -/
theorem mem_drop_one_of {α : Type} {xs : List α} {i : Nat} {x : α} (hx : xs[i]? = some x)
    (hi : i ≠ 0) : x ∈ xs.drop 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  apply List.mem_of_getElem? (i := j)
  rw [List.getElem?_drop]; rw [Nat.add_comm] at hx; exact hx

/-- **`splitRel`, split under a new parent** `pl` (a top node): `n`'s record replaced, the other
pieces and the parent fresh. -/
theorem splitRel_top {ps : Nat} {pl : Loc} {xs : List (Loc × node × List Inode)} {pv' : node}
    (hb : X1.t.bs !! bl = some B) (hlv : n ∈ X1.live)
    (hbl : rN.nv.bucket' = bl) (hsp : rN.nv.spilled' = false)
    (hil : rN.ins.length = rN.ws.length) (hch : rN.nv.children' = slice.nil)
    (h0 : rN.nv.parent' = null) (hsh : piecesShape ps n rN.nv pl xs) (h2 : 2 ≤ xs.length)
    (hpl : pl ≠ null) (hpv : pv' = newParent rN.nv pv'.children')
    (hflat : (xs.map (·.2.2)).flatten = rN.ins) (hnd : (xs.map (·.1)).Nodup)
    (hplx : pl ∉ xs.map (·.1)) :
    let recs := pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true
    let par : Loc × NRec := (pl, newParRec pv' (xs.map (·.1)))
    (recs.take 1).map (·.1) = [n] ∧
    ((recs.take 1 ++ (recs.drop 1 ++ [par])).map (·.1)).Nodup ∧
    (∀ p ∈ recs.take 1 ++ (recs.drop 1 ++ [par]), p.2.nv.parent' ≠ p.1) ∧
    ((∀ x ∈ xs.drop 1, X1.t.objs !! x.1 = none) → X1.t.objs !! pl = none → splitRel0 X1 (splitX X1 bl B (recs.take 1) (recs.drop 1 ++ [par])) bl n rN xs
      (cutWs (xs.map (·.2.2)) rN.ws) pl (newParRec pv' (xs.map (·.1)))) := by
  intro recs par
  have hlen : (cutWs (xs.map (·.2.2)) rN.ws).length = xs.length := by simp [cutWs_length]
  have hfst : recs.map (·.1) = xs.map (·.1) := pieceRecs_fst rN false xs _ true hlen
  have hx0 : ∃ x0 rest, xs = x0 :: rest ∧ x0.1 = n := by
    obtain ⟨-, x0, rest, hd, h, -⟩ := hsh; exact ⟨x0, rest, hd, h⟩
  have happ : recs.take 1 ++ (recs.drop 1 ++ [par]) = recs ++ [par] := by
    rw [← List.append_assoc, List.take_append_drop]
  have hndA : ((recs ++ [par]).map (·.1)).Nodup := by
    rw [List.map_append, hfst]
    refine List.nodup_append.2 ⟨hnd, by simp, ?_⟩
    intro a ha b hb' e; simp at hb'; subst hb'; subst e; exact hplx ha
  have hndA' : ((recs.take 1 ++ (recs.drop 1 ++ [par])).map (·.1)).Nodup := by rw [happ]; exact hndA
  have hnode : ∀ p ∈ recs ++ [par],
      (splitX X1 bl B (recs.take 1) (recs.drop 1 ++ [par])).node bl p.1 = some p.2 := by
    intro p hp; rw [← happ] at hp; exact splitX_node hndA' p hp
  have hfr := fun hnew => splitX_frame (psOld := recs.take 1) (psNew := recs.drop 1 ++ [par]) hb
    (xs.map (·.1) ++ [pl]) (fun p hp => by
      rw [happ, List.mem_append] at hp
      rcases hp with hp | hp
      · exact List.mem_append_left _ (hfst ▸ List.mem_map.2 ⟨p, hp, rfl⟩)
      · simp at hp; subst hp; simp [par]) hnew
  obtain ⟨x0, rest, hd, hx0n⟩ := hx0
  have hlv2 : ∀ (i : Nat) (x : Loc × node × List Inode), xs[i]? = some x →
      x.1 ∈ (splitX X1 bl B (recs.take 1) (recs.drop 1 ++ [par])).live := by
    intro i x hx
    rw [splitX_live]
    by_cases hi : i = 0
    · subst hi; rw [hd] at hx; simp at hx; subst hx; rw [hx0n]; exact Or.inl hlv
    · right
      have hm := mem_drop_one_of hx hi
      rw [List.map_append, List.mem_append]; left
      rw [List.map_drop, hfst, ← List.map_drop]; exact List.mem_map.2 ⟨x, hm, rfl⟩
  obtain ⟨hl, hws, hpl', hpr⟩ := splitRel_pieces hsh h2 hflat hil hbl hsp hch
    (fun p hp => hnode p (List.mem_append_left _ hp)) hlv2
  refine ⟨?_, hndA', ?_, fun hfresh hplf => ⟨by rw [hd]; simp, by rw [hd]; simp [hx0n], hnd, hl, hws, hflat,
    hpl', hpr, hfresh, Or.inr (Or.inl ⟨h0, h2, hpl, hplf, ?_, hnode par (by simp), ?_⟩),
    hfr (fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact fresh_of_drop hfresh p hp
      · simp at hp; subst hp; exact hplf),
    rfl, rfl, rfl, rfl⟩⟩
  · rw [List.map_take, hfst, hd]; simp [hx0n]
  · intro p hp
    rw [happ, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨x, hx, h1, h2'⟩ := pieceRecs_inv false xs _ true p hp
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      rw [h2', h1, (piece_fields hsh i x hi).2.2.2.2.1]
      intro e; subst e; exact hplx (List.mem_map.2 ⟨x, hx, rfl⟩)
    · simp at hp; subst hp
      simp only [par, newParRec]
      rw [hpv]; exact fun e => hpl e.symm
  · simp only [newParRec]; rw [← hpv]
  · rw [splitX_live]; right; simp [par]

/-- **`splitRel`, split under `n`'s parent** `pl` (record `rp`): `n`'s and the parent's records
replaced (the other pieces appended to its children), the other pieces fresh. -/
theorem splitRel_child {ps : Nat} {pl : Loc} {xs : List (Loc × node × List Inode)} {pv' : node}
    {pcs' : List Loc} {rp : NRec}
    (hb : X1.t.bs !! bl = some B) (hlv : n ∈ X1.live)
    (hbl : rN.nv.bucket' = bl) (hsp : rN.nv.spilled' = false)
    (hil : rN.ins.length = rN.ws.length) (hch : rN.nv.children' = slice.nil)
    (h0 : rN.nv.parent' ≠ null) (hsh : piecesShape ps n rN.nv pl xs) (h2 : 2 ≤ xs.length)
    (hplp : pl = rN.nv.parent') (hrp : B.ns !! pl = some rp) (hplv : pl ∈ X1.live)
    (hrpp : rp.nv.parent' ≠ pl) (hpv : pv' = { rp.nv with children' := pv'.children' })
    (hpcs : pcs' = rp.cs ++ (xs.map (·.1)).drop 1)
    (hflat : (xs.map (·.2.2)).flatten = rN.ins) (hnd : (xs.map (·.1)).Nodup)
    (hplx : pl ∉ xs.map (·.1)) :
    let recs := pieceRecs rN false xs (cutWs (xs.map (·.2.2)) rN.ws) true
    let par : Loc × NRec := (pl, { rp with nv := pv', cs := pcs' })
    (recs.take 1 ++ [par]).map (·.1) = [n, pl] ∧
    (((recs.take 1 ++ [par]) ++ recs.drop 1).map (·.1)).Nodup ∧
    (∀ p ∈ (recs.take 1 ++ [par]) ++ recs.drop 1, p.2.nv.parent' ≠ p.1) ∧
    ((∀ x ∈ xs.drop 1, X1.t.objs !! x.1 = none) → splitRel0 X1 (splitX X1 bl B (recs.take 1 ++ [par]) (recs.drop 1)) bl n rN xs
      (cutWs (xs.map (·.2.2)) rN.ws) pl { rp with nv := pv', cs := pcs' }) := by
  intro recs par
  have hlen : (cutWs (xs.map (·.2.2)) rN.ws).length = xs.length := by simp [cutWs_length]
  have hfst : recs.map (·.1) = xs.map (·.1) := pieceRecs_fst rN false xs _ true hlen
  obtain ⟨x0, rest, hd, hx0n⟩ : ∃ x0 rest, xs = x0 :: rest ∧ x0.1 = n := by
    obtain ⟨-, x0, rest, hd, h, -⟩ := hsh; exact ⟨x0, rest, hd, h⟩
  have hperm : ((recs.take 1 ++ [par]) ++ recs.drop 1).Perm (recs ++ [par]) := by
    rw [List.append_assoc]
    conv => rhs; rw [← List.take_append_drop 1 recs, List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm)
  have hmem : ∀ p, p ∈ (recs.take 1 ++ [par]) ++ recs.drop 1 ↔ p ∈ recs ++ [par] :=
    fun p => hperm.mem_iff
  have hndA : ((recs ++ [par]).map (·.1)).Nodup := by
    rw [List.map_append, hfst]
    refine List.nodup_append.2 ⟨hnd, by simp, ?_⟩
    intro a ha b hb' e; simp at hb'; subst hb'; subst e; exact hplx ha
  have hndA' : (((recs.take 1 ++ [par]) ++ recs.drop 1).map (·.1)).Nodup :=
    (hperm.map _).nodup_iff.2 hndA
  have hnode : ∀ p ∈ recs ++ [par],
      (splitX X1 bl B (recs.take 1 ++ [par]) (recs.drop 1)).node bl p.1 = some p.2 := by
    intro p hp; exact splitX_node hndA' p ((hmem p).2 hp)
  have hfr := fun hnew => splitX_frame (psOld := recs.take 1 ++ [par]) (psNew := recs.drop 1) hb
    (xs.map (·.1) ++ [pl]) (fun p hp => by
      rw [hmem, List.mem_append] at hp
      rcases hp with hp | hp
      · exact List.mem_append_left _ (hfst ▸ List.mem_map.2 ⟨p, hp, rfl⟩)
      · simp at hp; subst hp; simp [par]) hnew
  have hdrop : (recs.drop 1).map (·.1) = (xs.drop 1).map (·.1) := by
    rw [List.map_drop, hfst, List.map_drop]
  have hlv2 : ∀ (i : Nat) (x : Loc × node × List Inode), xs[i]? = some x →
      x.1 ∈ (splitX X1 bl B (recs.take 1 ++ [par]) (recs.drop 1)).live := by
    intro i x hx
    rw [splitX_live]
    by_cases hi : i = 0
    · subst hi; rw [hd] at hx; simp at hx; subst hx; rw [hx0n]; exact Or.inl hlv
    · right
      rw [hdrop]; exact List.mem_map.2 ⟨x, mem_drop_one_of hx hi, rfl⟩
  obtain ⟨hl, hws, hpl', hpr⟩ := splitRel_pieces hsh h2 hflat hil hbl hsp hch
    (fun p hp => hnode p (List.mem_append_left _ hp)) hlv2
  refine ⟨?_, hndA', ?_, fun hfresh => ⟨by rw [hd]; simp, by rw [hd]; simp [hx0n], hnd, hl, hws, hflat,
    hpl', hpr, hfresh, Or.inr (Or.inr ⟨h0, hplp, rp, ?_, ?_, hnode par (by simp), ?_⟩),
    hfr (fun p hp => fresh_of_drop hfresh p hp),
    rfl, rfl, rfl, rfl⟩⟩
  · rw [List.map_append, List.map_take, hfst, hd]; simp [hx0n, par]
  · intro p hp
    rw [hmem, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨x, hx, h1, h2'⟩ := pieceRecs_inv false xs _ true p hp
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      rw [h2', h1, (piece_fields hsh i x hi).2.2.2.2.1]
      intro e; subst e; exact hplx (List.mem_map.2 ⟨x, hx, rfl⟩)
    · simp at hp; subst hp
      simp only [par]
      rw [hpv]; exact hrpp
  · unfold WX.node; rw [hb]; exact hrp
  · simp only
    rw [hpcs, ← hpv, List.map_drop]
  · rw [splitX_live, hdrop]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso; obtain ⟨x, hx, e⟩ := List.mem_map.1 h
        exact hplx (List.mem_map.2 ⟨x, List.mem_of_mem_drop hx, e⟩)
    · exact Or.inl

end rel

end recs

end Spill

end bbolt
end EtcdGrove
end Perennial
