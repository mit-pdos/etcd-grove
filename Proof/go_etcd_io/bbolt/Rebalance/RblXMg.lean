/-
`node.rebalance`'s merge over the writer's records (U8b, `notes/bbolt-proof-plan.md`): two
siblings `ll`, `lr` (the parent `pl`'s entries `k`, `k + 1`, one of them the deficient node)
merged into `ll` (`Rebalance/RblMg`: `mgBkt`, `mgParent`, `mgLeft`, the moved children
reparented), the right node `lr` dead (`WX.kill`) with its page freed; the parent the deficient
node. The records are those after all of the merge's code (the reparenting loop, the append, the
parent's `del` and `removeChild`, the cache's delete, `rightNode.free()`).

The dead right node's `children` slice and list are any (the loop's `removeChild`s change them;
a dead node keeps only its struct). Assembled by `rblX_kill` as `rblX_rm'`: the bucket step
`rbl_mg`, the tree `mg_tree` (`RblXSMgT`), the freelist `flView_free`, the reached nodes (a path
through the right node goes through the left one after: `descIn_mg`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSteps
public import Proof.go_etcd_io.bbolt.Rebalance.RblMg
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMgT

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section steps
variable [GooseExts]

/-- The bucket after the merge. -/
def mgBktX (B : BRec) (pl : Loc) (rp : NRec) (k : Nat) (ll lr : Loc) (rl rr : NRec)
    (sI sC sI' sC' : GoSlice) : BRec :=
  mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC') (mgLeft rl rr (kidsOf B rr.ws) sI sC)

/-- The dead right node (its page id `0`, its children slice `sCr` and list `csr`). -/
def mgDead (rr : NRec) (sCr : GoSlice) (csr : List Loc) : NRec :=
  { rr with nv := { rr.nv with pgid' := W64 0, children' := sCr }, cs := csr }

/-- A path in the bucket before the merge, not ending at the right node `lr`, is one after it
from the same node, or from the left one `ll` if it started at `lr`. -/
theorem descIn_mg (B B' : BRec) (pl ll lr : Loc) (rp rr : NRec)
    (hrp : B.ns !! pl = some rp) (hrr : B.ns !! lr = some rr) (hrrp : rr.nv.parent' = pl)
    (hcl : ∀ x rx, B.ns !! x = some rx → ∀ c ∈ rx.cs, ∃ rc, B.ns !! c = some rc ∧
      rc.nv.parent' = x)
    (hself : ∀ x rx, B.ns !! x = some rx → rx.nv.parent' ≠ x)
    (hpl : ∃ rp', B'.ns !! pl = some rp' ∧ ll ∈ rp'.cs ∧ ∀ c ∈ rp.cs, c ≠ lr → c ∈ rp'.cs)
    (hll : ∃ rl', B'.ns !! ll = some rl' ∧ ∀ c ∈ rr.cs, c ∈ rl'.cs)
    (hllk : ∀ rl ry, B.ns !! ll = some rl → B'.ns !! ll = some ry → ∀ c ∈ rl.cs, c ∈ ry.cs)
    (hoth : ∀ x rx, B.ns !! x = some rx → x ≠ pl → x ≠ ll → x ≠ lr →
      ∃ rx', B'.ns !! x = some rx' ∧ rx'.cs = rx.cs) :
    ∀ a d, descIn B a d → d ≠ lr → descIn B' (if a = lr then ll else a) d := by
  intro a d h
  induction h with
  | self x => intro hd; rw [if_neg hd]; exact descIn.self x
  | child a c d ra ha hc hd ih =>
    intro hdl
    have ihc := ih hdl
    by_cases hal : a = lr
    · subst hal; rw [hrr] at ha; cases ha
      rw [if_pos rfl]
      have hcl' : c ≠ a := by
        obtain ⟨rc, hrc, hpc⟩ := hcl a rr hrr c hc
        intro he; subst he; exact hself c rc hrc hpc
      rw [if_neg hcl'] at ihc
      obtain ⟨rl', h1, h2⟩ := hll
      exact descIn.child ll c d rl' h1 (h2 c hc) ihc
    rw [if_neg hal]
    by_cases hcl2 : c = lr
    · subst hcl2
      rw [if_pos rfl] at ihc
      obtain ⟨rc, hrc, hpc⟩ := hcl a ra ha c hc
      rw [hrr] at hrc; cases hrc
      rw [hrrp] at hpc; subst hpc
      rw [hrp] at ha; cases ha
      obtain ⟨rp', h1, h2, -⟩ := hpl
      exact descIn.child _ ll d _ h1 h2 ihc
    rw [if_neg hcl2] at ihc
    by_cases hap : a = pl
    · subst hap; rw [hrp] at ha; cases ha
      obtain ⟨rp', h1, -, h3⟩ := hpl
      exact descIn.child _ c d _ h1 (h3 c hc hcl2) ihc
    by_cases hall : a = ll
    · subst hall
      obtain ⟨rl', h1, -⟩ := hll
      exact descIn.child _ c d rl' h1 (hllk ra rl' ha h1 c hc) ihc
    obtain ⟨rx', h1, h2⟩ := hoth a ra ha hap hall hal
    exact descIn.child _ c d rx' h1 (by rw [h2]; exact hc) ihc

/-- **Two siblings merged** (see the module doc): the invariant with the parent deficient, the
steps' relation with the right node's page extent freed, the right node read from a page, and
the unbalanced nodes after (`rblPre`'s form). -/
theorem rblX_mg (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (pl : Loc) (rp : NRec)
    (k : Nat) (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec) (sI sC sI' sC' sCr : GoSlice)
    (csr : List Loc) (pg : List w8)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hn : n = ll ∨ n = lr)
    (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) (hne : 0 < (rl.ws ++ rr.ws).length)
    (hpg : X.v.pages !! rr.nv.pgid'.toNat = some pg) :
    rblX (X.kill bl (mgBktX B pl rp k ll lr rl rr sI sC sI' sC') lr (mgDead rr sCr csr))
      (fl.freePages X.t.mv.txid' rr.nv.pgid' (1 + pageOverflow pg)) bl (some pl) ∧
    rblRel X fl (X.kill bl (mgBktX B pl rp k ll lr rl rr sI sC sI' sC') lr (mgDead rr sCr csr))
      (fl.freePages X.t.mv.txid' rr.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    rr.nv.pgid' ≠ W64 0 ∧
    (∀ y ry', (mgBktX B pl rp k ll lr rl rr sI sC sI' sC').ns !! y = some ry' →
      ry'.nv.unbalanced' = true →
      y = pl ∨ (y ≠ lr ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧
        ry'.nv.pgid' = ry.nv.pgid')) := by
  have hI' := hI
  obtain ⟨⟨-, -, -, htx, -⟩, hBk, -, -, -, -, hV, hLR, hFV, hU, hX, hPL, -⟩ := hI'
  obtain ⟨hrb, -, -, hrt, hlive⟩ := hBk bl B hb
  rw [if_pos rfl] at hrb
  have hrb' := hrb
  obtain ⟨hc, ⟨bnd, hk⟩, ha, -⟩ := hrb'
  have hp00 : X.v.pages !! 0 = none := by
    cases h : X.v.pages !! 0 with
    | none => rfl
    | some pg0 => have := (Read.viewWF_page X.v hV 0 pg0 h).1; omega
  obtain ⟨hB', hent, hunb, hkind⟩ := rbl_mg X.v _ bl B pl rp k wl wr ll lr rl rr n sI sC sI' sC'
    hrb hn hp00 hpn hrp hbr hwl hwr hll hlr hrl hrr hne
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, hnmP, hnd, h0, hllcs, hlrcs, hself, hpgne, -⟩ :=
    mg_basic X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hnmR : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  have hp0 : rr.nv.pgid' ≠ W64 0 := by
    intro he; have := (hc.2.2.2.2.2.2.2.1 lr rr hrr).2.2.2.2.2.2.2.2.2.1 h0
    cases this with
    | page _ _ h2' _ _ _ _ _ => rw [he] at h2'; simp at h2'
  obtain ⟨pg', hpg', -, -, -, hcan⟩ := rblX_canFree' X fl bl (some n) B lr rr hI hb hrr hp0
  rw [hpg] at hpg'; cases hpg'
  have hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null := hk.2.1
  -- the right node's leaves map to no node (as in `rbl_mg`)
  have hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none := by
    intro hl w hw
    have h0' := ((hk.2.2 lr rr hrr).2.2.2.2 hl w hw).1
    rw [h0']
    cases hn0 : B.nm !! W64 0 with
    | none => rfl
    | some l0 =>
      obtain ⟨-, r0, hr0, hpg0⟩ := hc.2.2.2.2.1 _ _ hn0
      have hwf := (hc.2.2.2.2.2.2.2.1 l0 r0 hr0).2.2.2.2.2.2.2.2.2.1 h0
      rw [hpg0] at hwf
      cases hwf with
      | page _ pg _ _ hpg _ _ _ => rw [show (W64 0).toNat = 0 from rfl, hp00] at hpg; cases hpg
  have hmoved := (mg_moved X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr hleaf0).1
  let B' := mgBktX B pl rp k ll lr rl rr sI sC sI' sC'
  let rn' := mgDead rr sCr csr
  have hns : ∀ y, B'.ns !! y = if y = pl then some (mgParent rp (k + 1) lr sI' sC')
      else if y = ll then some (mgLeft rl rr (kidsOf B rr.ws) sI sC) else if y = lr then none else
        (B.ns !! y).map
          (fun x => if x.nv.parent' = lr then { x with nv := { x.nv with parent' := ll } } else x) :=
    fun y => mg_ns _ _ _ _ _ _ _ y
  have hlook : ∀ y ry', B'.ns !! y = some ry' → y ≠ lr ∧ ∃ ry, B.ns !! y = some ry ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧
      ∀ w ∈ ry'.ws, ∃ y3 ry3, B.ns !! y3 = some ry3 ∧ ry3.nv.isLeaf' = ry'.nv.isLeaf' ∧
        w ∈ ry3.ws := by
    intro y ry' hy
    rw [hns] at hy
    by_cases hyp : y = pl
    · rw [if_pos hyp] at hy; cases hy; subst hyp
      exact ⟨fun h => hlrp h.symm, rp, hrp, rfl, rfl, fun w hw => ⟨y, rp, hrp, rfl, List.mem_of_mem_eraseIdx hw⟩⟩
    rw [if_neg hyp] at hy
    by_cases hyl : y = ll
    · rw [if_pos hyl] at hy; cases hy; subst hyl
      refine ⟨hllr, rl, hrl, rfl, rfl, fun w hw => ?_⟩
      rcases List.mem_append.1 hw with hw | hw
      · exact ⟨y, rl, hrl, rfl, hw⟩
      · exact ⟨lr, rr, hrr, hkind.symm, hw⟩
    rw [if_neg hyl] at hy
    by_cases hyr : y = lr
    · rw [if_pos hyr] at hy; cases hy
    rw [if_neg hyr] at hy
    cases hy0 : B.ns !! y with
    | none => rw [hy0] at hy; cases hy
    | some ry =>
      rw [hy0] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy
      refine ⟨hyr, ry, rfl, ?_, ?_, ?_⟩
      · split <;> rfl
      · split <;> rfl
      · intro w hw
        refine ⟨y, ry, hy0, ?_, ?_⟩
        · split <;> rfl
        · split at hw <;> exact hw
  have hk3 : ∀ y ry, B.ns !! y = some ry → y ≠ lr → (B'.ns !! y).isSome = true := by
    intro y ry hy hyr
    obtain ⟨ry', hry', -⟩ := mg_look X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr
      hll hlr hrl hrr sI sC sI' sC' y ry hy hyr
    show ((mgBkt B pl ll lr rr.nv.pgid' _ _).ns !! y).isSome = true
    rw [hry']; rfl
  obtain ⟨hrt', hlv, hpos1, hpos2⟩ :=
    mg_tree X bl B pl rp k wl wr ll lr rl rr sI sC sI' sC' hb hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
      hroot hkind hrt
  obtain ⟨rt, hrtI, hdI⟩ := hLR.2 bl B lr rr hb hrr (hlive lr rr hrr)
  have hE := node_pos X bl B hb hc hroot hrt h0 rt lr hrtI hdI rr hrr
  have hEx := posExtent_node X bl B hb hc h0 lr rr hrr hp0 pg hpg
  have hdom : ∀ c, ((X.kill bl B' lr rn').t.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [kill_look]; split
    · subst c; rw [hb]; rfl
    · rfl
  have hlvx : ((X.kill bl B' lr rn').leaves bl).flatten = (X.leaves bl).flatten := by
    rw [kill_leaves]; exact hlv
  have hfl := flView_free X (X.kill bl B' lr rn') fl bl rr.nv.pgid' (1 + pageOverflow pg)
    X.t.mv.txid' hFV hU rfl hdom (by rw [hb]; simp)
    (fun c hc' => ⟨by rw [kill_positions, setBkt_positions_other X bl B B' hb rfl c hc'],
      by rw [kill_posExtent, setBkt_posExtent_other X bl B' c hc']⟩)
    (fun q hq => hpos1 q (by rw [← kill_positions]; exact hq))
    (fun q hq hqE => by rw [kill_positions]; exact hpos2 q hq hqE)
    (fun q hq => by
      rw [kill_posExtent]
      exact mg_posExtent X bl B pl rp k wl wr ll lr rl rr sI sC sI' sC' hb hc ha hpn hrp hbr hwl hwr
        hll hlr hrl hrr q hq)
    hE hEx ⟨pg, hpg⟩
    (by
      apply rootEnts_of_leaves X (X.kill bl B' lr rn') rfl
      by_cases hrl' : X.rl = bl
      · rw [hrl']; exact hlvx
      · rw [kill_leaves, setBkt_leaves_other X bl B B' hb rfl _ hrl'])
    (by
      rw [kill_bktLoc]; funext nm; unfold bktLoc
      show ((X.setBkt bl B').t.bs !! X.rl).bind _ = _
      rw [setBkt_look]; split
      · rename_i h; rw [h, hb]; rfl
      · rfl)
    hcan (hX _ pg hpg) hPL (by omega)
  -- the reached nodes
  have hcl : ∀ x rx, B.ns !! x = some rx → ∀ c ∈ rx.cs, ∃ rcc, B.ns !! c = some rcc ∧
      rcc.nv.parent' = x := fun x rx hx c hc' =>
    (hc.2.2.2.2.2.2.2.1 x rx hx).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c hc'
  have hxnn : ∀ x rx, B.ns !! x = some rx → x ≠ null := fun x rx hx =>
    (hc.2.2.2.2.1 _ _ (hc.2.2.2.2.2.2.2.1 x rx hx).2.2.2.2.2.2.2.1).1
  have hself' : ∀ x rx, B.ns !! x = some rx → rx.nv.parent' ≠ x := by
    intro x rx hx he
    exact hself x rx hx (by rw [he]; exact hxnn x rx hx) he
  have hdesc := descIn_mg B B' pl ll lr rp rr hrp hrr hp2 hcl hself'
    ⟨_, by rw [hns, if_pos rfl],
      by show ll ∈ rp.cs.eraseIdx (rp.cs.idxOf lr)
         rw [cs_erase_mg]; exact (List.mem_erase_of_ne hllr).2 hllcs,
      fun c hc' hcl' => by
        show c ∈ rp.cs.eraseIdx (rp.cs.idxOf lr)
        rw [cs_erase_mg]; exact (List.mem_erase_of_ne hcl').2 hc'⟩
    ⟨_, by rw [hns, if_neg hllp, if_pos rfl], fun c hc' => by
      obtain ⟨rcc, hrcc, hpc⟩ := hcl lr rr hrr c hc'
      exact List.mem_append_right _ ((hmoved c).2 ⟨rcc, hrcc, hpc⟩)⟩
    (fun rl0 ry h1 h2 c hc' => by
      rw [hrl] at h1; cases h1
      rw [hns, if_neg hllp, if_pos rfl] at h2; cases h2
      exact List.mem_append_left _ hc')
    (fun x rx hx hxp hxl hxr => by
      refine ⟨_, by rw [hns, if_neg hxp, if_neg hxl, if_neg hxr, hx]; rfl, ?_⟩
      dsimp only; split <;> rfl)
  have hlr' : ∀ l r', B'.ns !! l = some r' → l ∈ (X.kill bl B' lr rn').live →
      ∃ rt, nodeRootIn B' B'.bv.rootNode' rt ∧ descIn B' rt l := by
    intro l r' hl hll'
    obtain ⟨hln, hlx⟩ := (kill_live X bl B' lr rn' l).1 hll'
    obtain ⟨-, ry, hry, -⟩ := hlook l r' hl
    obtain ⟨rt, hrtI, hd⟩ := hLR.2 bl B l ry hb hry hlx
    have hrte : ∃ rr0, rt = B.bv.rootNode' ∧ B.ns !! rt = some rr0 ∧ rr0.nv.parent' = null := by
      cases hrtI with
      | top _ rr0 hrr0 hp' => exact ⟨rr0, rfl, hrr0, hp'⟩
      | up _ _ rr0 hrr0 hp' _ => exact absurd (hroot rr0 hrr0) hp'
    obtain ⟨rr0, hrt0, hrr0, hrr0p⟩ := hrte
    have hrtr : rt ≠ lr := by
      intro he; rw [he, hrr] at hrr0; cases hrr0; rw [hp2] at hrr0p; exact hpn hrr0p
    obtain ⟨rr', hrr', -, -, hpar⟩ := mg_look X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr
      hwl hwr hll hlr hrl hrr sI sC sI' sC' rt rr0 hrr0 hrtr
    have hlrn : lr ≠ null := hxnn lr rr hrr
    rw [hrr0p, if_neg (Ne.symm hlrn)] at hpar
    refine ⟨rt, ?_, ?_⟩
    · show nodeRootIn B' B.bv.rootNode' rt
      rw [← hrt0]; exact nodeRootIn.top rt rr' hrr' hpar
    · have := hdesc rt l hd hln
      rw [if_neg hrtr] at this; exact this
  obtain ⟨h1, h2'⟩ := rblX_kill X fl bl (some n) (some pl) B B' lr rn' rr.nv.pgid'
    (1 + pageOverflow pg) X.t.mv.txid' hI hb (by rw [hrr]; rfl) ⟨rfl, rfl, rfl, rfl⟩
    (fun y ry' hy => by
      obtain ⟨hyr, ry, hry, hpg2, -⟩ := hlook y ry' hy
      exact ⟨hyr, ry, hry, hpg2⟩)
    (fun y ry' hy => by
      obtain ⟨-, -, -, -, -, hw⟩ := hlook y ry' hy
      exact hw)
    hk3 (fun y j c hp => ⟨_, _, (mg_pos X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr
      hll hlr hrl hrr sI sC sI' sC' hkind y j c hp).2⟩)
    hB' hent ((kill_rtOK X bl B' lr rn' bl).2 hrt') hlvx hfl hlr' hcan ⟨pg, hpg, rfl⟩
  exact ⟨h1, h2', hp0, hunb⟩

end steps

end bbolt
end EtcdGrove
end Perennial
