/-
`node.spill` after its children's loop (U9z3, `notes/bbolt-proof-plan.md`; pure): **the keys
around a piece's entry in its parent** (`pcKeys`, what `Spill/PcStepPar.parPut` takes in
`Spill/NodeSpillTailStep.pcInv_stepX`): `n`'s entries after its children's loop are sorted and
within `n`'s bounds (`spEnd_keys`), a piece's first key is one of them (`wssKey_flat`), so it lies
between the parent's neighbouring entries and after the previous piece's.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section keys
variable [GooseExts] [GoGlobalContext]

theorem pk_lt_of_lt_nlt {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  by_cases h : go.GoStringLt b c
  · exact go.goStringLt_trans h1 h
  · rw [← go.goStringLt_eq_of_not_lt h h2]; exact h1

theorem pk_uNode {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {lo hi h F D N E}
    (hu : uTree X bl P hwm n lo hi h F D N E) {r : NRec} (hn : X.node bl n = some r) :
    uNode X bl n r lo hi := by
  cases hu with
  | leaf _ r' _ _ _ hr hun => rw [hn] at hr; cases hr; exact hun
  | branch _ r' _ _ _ _ hr hun => rw [hn] at hr; cases hr; exact hun

/-- **`n`'s entries after its children's loop**: sorted, within `[lo, hi)`; its key and its key
slice's nilness as at the start. -/
theorem spEnd_keys {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    wsSorted r'.ws ∧ (∀ e ∈ r'.ws, keyIn lo hi e.key) ∧ r'.key = rn.key ∧
    (r'.nv.key' = slice.nil ↔ rn.nv.key' = slice.nil) := by
  obtain ⟨hn, -, hc⟩ := hpre
  rcases hc with ⟨hs, -⟩ | ⟨hut, -⟩
  · rw [hs] at hsp; cases hsp
  rcases hend with ⟨-, -, -, rfl, -, -⟩ | ⟨-, h', es, i, -, hl, -⟩
  · have hun := pk_uNode hut hn
    exact ⟨hun.2.2.2.2.2.1, fun e he => (hun.2.2.2.2.2.2.1 e he).1, rfl, Iff.rfl⟩
  · have hun := hl.br.un
    exact ⟨hun.2.2.2.2.2.1, fun e he => (hun.2.2.2.2.2.2.1 e he).1, hl.key, hl.knil⟩

/-- The entries before piece `k`. -/
def wssOff (wss : List (List WEntry)) (k : Nat) : Nat := ((wss.take k).map List.length).sum

/-- A non-empty piece's first key is the entry at its offset. -/
theorem wssKey_flat {wss : List (List WEntry)} {k : Nat} {ws : List WEntry}
    (hk : wss[k]? = some ws) (hne : 0 < ws.length) :
    wssOff wss k < wss.flatten.length ∧ wKey wss.flatten (wssOff wss k) = wssKey wss k := by
  have hlt : k < wss.length := (List.getElem?_eq_some_iff.1 hk).1
  have hd : wss.drop k = ws :: wss.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hk).2]
  have hf : wss.flatten = (wss.take k).flatten ++ (ws ++ (wss.drop (k + 1)).flatten) := by
    have e := congrArg List.flatten (List.take_append_drop k wss)
    rw [← e, hd]; simp
  have hlen : (wss.take k).flatten.length = wssOff wss k := by
    unfold wssOff; rw [List.length_flatten]
  unfold wssKey; rw [hk]
  simp only [Option.getD_some]
  constructor
  · rw [hf, List.length_append, List.length_append, hlen]; omega
  · unfold wKey; rw [hf, ← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    cases ws with
    | nil => simp at hne
    | cons e es => simp

theorem wssOff_succ {wss : List (List WEntry)} {k : Nat} {ws : List WEntry}
    (hk : wss[k]? = some ws) : wssOff wss (k + 1) = wssOff wss k + ws.length := by
  unfold wssOff
  rw [List.take_add_one, hk]; simp

/-- **The keys around piece `i`'s entry in the parent** (`parPut`'s premises, the piece's key
`wssKey wss i`): the node's entry `j` in the base `bs` (none for a new root), the first piece put
at the node's key, the piece's key above the base's previous entry and the previous piece's, below
the base's next entry. -/
theorem pcKeys {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {pl : Loc} {bs : List WEntry} {j : Nat}
    (hcs : match cs with
     | .child pl' rp j' _ _ => pl = pl' ∧ j = j' ∧ bs.map wDat = rp.ws.map wDat
     | .top => bs = [] ∧ j = 0)
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T)
    {X1 X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)}
    {rp0 : NRec} (hsr : splitRel X1 X2 bl n r'.nilCh xs wss pl rp0)
    {i : Nat} {ws : List WEntry} (hws : wss[i]? = some ws) (hne : 0 < ws.length)
    {ps : List Piece} (hps : ∀ p, i ≠ 0 → ps[i - 1]? = some p → p.k = wssKey wss (i - 1))
    {ra : NRec}
    (hra : i = 0 → (ra.nv.key' = slice.nil ↔ r'.nv.key' = slice.nil) ∧ ra.key = r'.key) :
    (j < bs.length ∨ (bs = [] ∧ j = 0)) ∧
    (i = 0 → bs ≠ [] → wKey bs j = pcOldKey ra) ∧
    (i = 0 → 0 < j → go.GoStringLt (wKey bs (j - 1)) (wssKey wss i)) ∧
    (i ≠ 0 → ∀ p, ps[i - 1]? = some p → go.GoStringLt p.k (wssKey wss i)) ∧
    (j + 1 < bs.length → go.GoStringLt (wssKey wss i) (wKey bs (j + 1))) := by
  obtain ⟨hsort, hin, hkey, hknil⟩ := spEnd_keys hpre hsp hend
  have hflat : wss.flatten = r'.ws := hsr.ws
  obtain ⟨hoff, hkw⟩ := wssKey_flat hws hne
  rw [hflat] at hoff hkw
  have hkin : keyIn lo hi (wssKey wss i) := by
    rw [← hkw]; unfold wKey; rw [List.getElem?_eq_getElem hoff]
    simp only [Option.map_some, Option.getD_some]
    exact hin _ (List.getElem_mem hoff)
  have k5 : i ≠ 0 → ∀ p, ps[i - 1]? = some p → go.GoStringLt p.k (wssKey wss i) := by
    intro hi0 p hp
    rw [hps p hi0 hp]
    have hil : i < xs.length := by rw [← hsr.len]; exact (List.getElem?_eq_some_iff.1 hws).1
    obtain ⟨wp, hwp⟩ : ∃ wp, wss[i - 1]? = some wp :=
      ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; omega)⟩
    obtain ⟨xp, hxp⟩ : ∃ xp, xs[i - 1]? = some xp := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hnp : 0 < wp.length := (hsr.plen _ xp wp hxp hwp).2 (by omega)
    obtain ⟨-, hkw'⟩ := wssKey_flat hwp hnp
    rw [hflat] at hkw'
    have hsucc := wssOff_succ hwp
    rw [show i - 1 + 1 = i by omega] at hsucc
    rw [← hkw', ← hkw]
    exact hsort _ _ (by omega) hoff
  cases cs with
  | top =>
    obtain ⟨rfl, rfl⟩ := hcs
    exact ⟨Or.inr ⟨rfl, rfl⟩, fun _ h => absurd rfl h, fun _ h => absurd h (Nat.lt_irrefl _), k5,
      fun h => by simp at h⟩
  | child pl' rp j' plo phi =>
    obtain ⟨rfl, rfl, hbs⟩ := hcs
    obtain ⟨-, -, hc⟩ := hpre
    rcases hc with ⟨hs, -⟩ | ⟨-, hctx, -⟩
    · rw [hs] at hsp; cases hsp
    obtain ⟨-, -, -, -, hun, -, -, -, ⟨we, hwe, -, hwk⟩, hlo, hhi, hkn, -, -⟩ := hctx
    have hK : wKey bs = wKey rp.ws := wKey_of_dat hbs
    have hL : bs.length = rp.ws.length := length_of_dat hbs
    have hjl : j < rp.ws.length := (List.getElem?_eq_some_iff.1 hwe).1
    refine ⟨Or.inl (by rw [hL]; exact hjl), ?_, ?_, k5, ?_⟩
    · intro hi0 _
      obtain ⟨hk1, hk2⟩ := hra hi0
      have hne' : ¬ ra.nv.key' = slice.nil := fun he => hkn (hknil.1 (hk1.1 he))
      unfold pcOldKey; rw [if_neg hne', hk2, hkey, hK]
      unfold wKey; rw [hwe]; simp [hwk]
    · intro _ hj
      rw [hK]
      have hlo' := hkin.1 (wKey rp.ws j) (by rw [hlo]; unfold childLo; rw [if_neg (by omega)])
      exact pk_lt_of_lt_nlt (hun.2.2.2.2.2.1 (j - 1) j (by omega) hjl) hlo'
    · intro hj
      rw [hK]; rw [hL] at hj
      exact hkin.2 _ (by rw [hhi]; unfold childHi; rw [if_pos hj])

end keys

end Spill

end bbolt
end EtcdGrove
end Perennial
