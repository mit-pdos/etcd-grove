/-
`rblX` through the root's collapse (U8b, `Rebalance/RblXSteps.lean`'s `rblX_col`): the bucket
step `rbl_col`, the tree `col_tree`, the freelist `flView_free`, the reached nodes (a path from
the root through the child `lc` now goes from the root straight to `lc`'s children), assembled
by `rblX_kill`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSRm
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSColT

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section col
variable [GooseExts]

/-- A path through nodes of a set closed under children survives a change keeping their
children. -/
theorem descIn_mono (B B' : BRec) (Q : Loc → Prop)
    (hQ : ∀ x rx, B.ns !! x = some rx → Q x → ∀ c ∈ rx.cs, Q c)
    (hk : ∀ x rx, B.ns !! x = some rx → Q x → ∃ rx', B'.ns !! x = some rx' ∧
      ∀ c ∈ rx.cs, c ∈ rx'.cs) :
    ∀ a d, descIn B a d → Q a → descIn B' a d := by
  intro a d h
  induction h with
  | self x => intro _; exact descIn.self x
  | child a c d ra ha hc _ ih =>
    intro hqa
    obtain ⟨ra', ha', hcs⟩ := hk a ra ha hqa
    exact descIn.child a c d ra' ha' (hcs c hc) (ih (hQ a ra ha hqa c hc))

theorem rblX_col' (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (w0 : WEntry)
    (lc : Loc) (rc : NRec) (sI : GoSlice) (pg : List w8)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hrn : B.ns !! n = some rn)
    (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null) (hws : rn.ws = [w0])
    (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc)
    (hpg : X.v.pages !! rc.nv.pgid'.toNat = some pg) :
    rblX (X.kill bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)) lc
        { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' rc.nv.pgid' (1 + pageOverflow pg)) bl none ∧
    rblRel X fl (X.kill bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)) lc
        { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' rc.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    rc.nv.pgid' ≠ W64 0 ∧
    (∀ y ry', (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y = some ry' →
        ry'.nv.unbalanced' = true → y = n ∧ rn.nv.unbalanced' = true ∨
        (y ≠ lc ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
          ry'.nv.pgid' = ry.nv.pgid')) := by
  have hI' := hI
  obtain ⟨⟨-, -, -, htx, -⟩, hBk, -, -, -, -, -, hLR, hFV, hU, hX, hPL, -⟩ := hI'
  obtain ⟨hrb, -, -, hrt, hlive⟩ := hBk bl B hb
  rw [if_pos rfl] at hrb
  have hrb' := hrb
  obtain ⟨hc, ⟨bnd, hk⟩, ha, -⟩ := hrb'
  obtain ⟨hB', hent, hunb⟩ := rbl_col X.v _ bl B n rn w0 lc rc sI hrb hrn hbr hpn hws hlc hrc
  obtain ⟨hp1, hlcn, hpe, hnm1, hpgne, h0, honly, -⟩ :=
    col_basic X.v _ bl B n rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hp0 : rc.nv.pgid' ≠ W64 0 := by
    intro he; have := (hc.2.2.2.2.2.2.2.1 lc rc hrc).2.2.2.2.2.2.2.2.2.1 h0
    cases this with
    | page _ _ h2' _ _ _ _ _ => rw [he] at h2'; simp at h2'
  obtain ⟨pg', hpg', -, -, -, hcan⟩ := rblX_canFree' X fl bl (some n) B lc rc hI hb hrc hp0
  rw [hpg] at hpg'; cases hpg'
  have hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null := hk.2.1
  have hnn : n ≠ null := (hc.2.2.2.2.1 _ _ hnm1).1
  have hrootn : B.bv.rootNode' = n := ncol_root (hc.2.2.2.2.2.2.2.1 n rn hrn) hpn
  let B' := colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)
  let rn' : NRec := { rc with nv := { rc.nv with parent' := null, pgid' := W64 0 } }
  have hlook : ∀ y ry', B'.ns !! y = some ry' → y ≠ lc ∧ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ ry'.nv.isLeaf' = (if y = n then rc else ry).nv.isLeaf' ∧
      ry'.ws = (if y = n then rc else ry).ws ∧ ry'.cs = (if y = n then rc else ry).cs := by
    intro y ry' hy
    change (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y = some ry' at hy
    rw [col_ns] at hy
    by_cases hyn : y = n
    · rw [if_pos hyn] at hy; cases hy; subst hyn
      exact ⟨fun h => hlcn h.symm, rn, hrn, rfl, by rw [if_pos rfl]; rfl, by rw [if_pos rfl]; rfl,
        by rw [if_pos rfl]; rfl⟩
    · rw [if_neg hyn] at hy
      by_cases hyl : y = lc
      · rw [if_pos hyl] at hy; cases hy
      · rw [if_neg hyl] at hy
        cases hy0 : B.ns !! y with
        | none => rw [hy0] at hy; cases hy
        | some ry =>
          rw [hy0] at hy
          simp only [Option.map_some, Option.some.injEq] at hy
          subst hy
          refine ⟨hyl, ry, rfl, ?_, ?_, ?_, ?_⟩ <;> (try rw [if_neg hyn]) <;> split <;> rfl
  have hk3 : ∀ y ry, B.ns !! y = some ry → y ≠ lc → (B'.ns !! y).isSome = true := by
    intro y ry hy hyl
    obtain ⟨ry', hry', -⟩ := col_look X.v _ bl B n rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI
      y ry hy hyl
    show ((colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).ns !! y).isSome = true
    rw [hry']; rfl
  obtain ⟨hrt', hlv, hpos1, hpos2⟩ :=
    col_tree X bl B n rn w0 lc rc sI hb hc ha hrn hbr hpn hws hlc hrc hroot hrt
  obtain ⟨rt, hrtI, hdI⟩ := hLR.2 bl B lc rc hb hrc (hlive lc rc hrc)
  have hE := node_pos X bl B hb hc hroot hrt h0 rt lc hrtI hdI rc hrc
  have hEx := posExtent_node X bl B hb hc h0 lc rc hrc hp0 pg hpg
  have hdom : ∀ c, ((X.kill bl B' lc rn').t.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [kill_look]; split
    · subst c; rw [hb]; rfl
    · rfl
  have hlvx : ((X.kill bl B' lc rn').leaves bl).flatten = (X.leaves bl).flatten := by
    rw [kill_leaves]; exact hlv
  have hfl := flView_free X (X.kill bl B' lc rn') fl bl rc.nv.pgid' (1 + pageOverflow pg)
    X.t.mv.txid' hFV hU rfl hdom (by rw [hb]; simp)
    (fun c hc' => ⟨by rw [kill_positions, setBkt_positions_other X bl B B' hb rfl c hc'],
      by rw [kill_posExtent, setBkt_posExtent_other X bl B' c hc']⟩)
    (fun q hq => hpos1 q (by rw [← kill_positions]; exact hq))
    (fun q hq hqE => by rw [kill_positions]; exact hpos2 q hq hqE)
    (fun q hq => by
      rw [kill_posExtent]
      exact col_posExtent X bl B n rn w0 lc rc sI hb hc ha hrn hbr hpn hws hlc hrc q hq)
    hE hEx ⟨pg, hpg⟩
    (by
      apply rootEnts_of_leaves X (X.kill bl B' lc rn') rfl
      by_cases hrl : X.rl = bl
      · rw [hrl]; exact hlvx
      · rw [kill_leaves, setBkt_leaves_other X bl B B' hb rfl _ hrl])
    (by
      rw [kill_bktLoc]; funext nm; unfold bktLoc
      show ((X.setBkt bl B').t.bs !! X.rl).bind _ = _
      rw [setBkt_look]; split
      · rename_i h; rw [h, hb]; rfl
      · rfl)
    hcan (hX _ pg hpg) hPL (by omega)
  -- the children of a node other than `n`, `lc` are neither
  have hcl : ∀ x rx, B.ns !! x = some rx → ∀ c ∈ rx.cs, ∃ rcc, B.ns !! c = some rcc ∧
      rcc.nv.parent' = x := fun x rx hx c hc' =>
    (hc.2.2.2.2.2.2.2.1 x rx hx).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c hc'
  have hxnn : ∀ x rx, B.ns !! x = some rx → x ≠ null := fun x rx hx =>
    (hc.2.2.2.2.1 _ _ (hc.2.2.2.2.2.2.2.1 x rx hx).2.2.2.2.2.2.2.1).1
  have hQ : ∀ x rx, B.ns !! x = some rx → (x ≠ n ∧ x ≠ lc) → ∀ c ∈ rx.cs, c ≠ n ∧ c ≠ lc := by
    intro x rx hx hq c hc'
    obtain ⟨rcc, hrcc, hpc⟩ := hcl x rx hx c hc'
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he; rw [hrn] at hrcc; cases hrcc; rw [hpn] at hpc; exact hxnn x rx hx hpc.symm
    · subst he; rw [hrc] at hrcc; cases hrcc; rw [hp1] at hpc; exact hq.1 hpc.symm
  have hkQ : ∀ x rx, B.ns !! x = some rx → (x ≠ n ∧ x ≠ lc) → ∃ rx', B'.ns !! x = some rx' ∧
      ∀ c ∈ rx.cs, c ∈ rx'.cs := by
    intro x rx hx hq
    obtain ⟨rx', hrx'⟩ := Option.isSome_iff_exists.1 (hk3 x rx hx hq.2)
    obtain ⟨-, ry, hry, -, -, -, hcs⟩ := hlook x rx' hrx'
    rw [hx] at hry; cases hry
    rw [if_neg hq.1] at hcs
    exact ⟨rx', hrx', fun c h => by rw [hcs]; exact h⟩
  have hlr : ∀ l r', B'.ns !! l = some r' → l ∈ (X.kill bl B' lc rn').live →
      ∃ rt, nodeRootIn B' B'.bv.rootNode' rt ∧ descIn B' rt l := by
    intro l r' hl hll
    obtain ⟨hll', hlx⟩ := (kill_live X bl B' lc rn' l).1 hll
    obtain ⟨-, ry, hry, -⟩ := hlook l r' hl
    obtain ⟨rt, hrtI, hd⟩ := hLR.2 bl B l ry hb hry hlx
    have hrte : rt = n := by
      cases hrtI with
      | top _ rr hrr hp' => exact hrootn
      | up _ _ rr hrr hp' _ => exact absurd (hroot rr hrr) hp'
    subst hrte
    have hBn : B'.ns !! rt = some (colRoot rn rc sI) := by
      show (colBkt B rt lc rc.nv.pgid' (colRoot rn rc sI)).ns !! rt = _
      rw [col_ns, if_pos rfl]
    refine ⟨rt, ?_, ?_⟩
    · show nodeRootIn B' B.bv.rootNode' rt
      rw [hrootn]; exact nodeRootIn.top rt _ hBn hpn
    · cases hd with
      | self => exact descIn.self _
      | child _ c _ ra ha' hc' hd' =>
        rw [hrn] at ha'; cases ha'
        have hcl' : c = lc := by
          obtain ⟨rcc, hrcc, hpc⟩ := hcl rt rn hrn c hc'
          exact honly c rcc hrcc hpc
        subst hcl'
        cases hd' with
        | self => exact absurd rfl hll'
        | child _ c' _ ra' ha'' hc'' hd'' =>
          rw [hrc] at ha''; cases ha''
          have hq' : c' ≠ rt ∧ c' ≠ c := by
            obtain ⟨rcc, hrcc, hpc⟩ := hcl c rc hrc c' hc''
            refine ⟨fun he => ?_, fun he => ?_⟩
            · subst he; rw [hrn] at hrcc; cases hrcc; rw [hpn] at hpc
              exact hxnn c rc hrc hpc.symm
            · subst he; rw [hrc] at hrcc; cases hrcc; rw [hp1] at hpc; exact hlcn hpc.symm
          exact descIn.child rt c' l _ hBn hc''
            (descIn_mono B B' (fun x => x ≠ rt ∧ x ≠ c) hQ hkQ c' l hd'' hq')
  obtain ⟨h1, h2'⟩ := rblX_kill X fl bl (some n) none B B' lc rn' rc.nv.pgid'
    (1 + pageOverflow pg) X.t.mv.txid' hI hb (by rw [hrc]; rfl) ⟨rfl, rfl, rfl⟩
    (fun y ry' hy => by
      obtain ⟨hyl, ry, hry, hpg2, -⟩ := hlook y ry' hy
      exact ⟨hyl, ry, hry, hpg2⟩)
    (fun y ry' hy x hx => by
      obtain ⟨-, ry, hry, -, hlf, hws', -⟩ := hlook y ry' hy
      by_cases hyn : y = n
      · rw [if_pos hyn] at hlf hws'
        exact ⟨lc, rc, hrc, hlf.symm, by rw [← hws']; exact hx⟩
      · rw [if_neg hyn] at hlf hws'
        exact ⟨y, ry, hry, hlf.symm, by rw [← hws']; exact hx⟩)
    hk3 hB' hent ((kill_rtOK X bl B' lc rn' bl).2 hrt') hlvx hfl hlr hcan ⟨pg, hpg, rfl⟩
  exact ⟨h1, h2', hp0, hunb⟩

end col

end bbolt
end EtcdGrove
end Perennial
