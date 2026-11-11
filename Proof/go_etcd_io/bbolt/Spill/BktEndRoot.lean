/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`; moved here from
`Spill/BktEndTree`): **the root bucket's tree at the loop's end** (`end_rootTree`). With a root
node, its unspilled tree (`BktEndInit.end_uTree`) over the nested values `Sb` of its leaf nodes
(a put child's new value, `childSt`; a skipped child's old value, `nil_val`; an unopened bucket's,
`bvalS_uncachedL`). Its slots `D` are distinct pieces (`uTree_piecesE`, `end_gdisj`), each the
root's own (a position's, `own_Lroot`) or a child's (`ent_class`); every owned slot is one of them:
a root position's (`uTree_coverW`), a cached child's at the start (none: its tree's slots are
`Dc0`, or its value's, `uTree_leafCov`), an unopened bucket's (`uTree_leafCov`), a put child's new
value's (`entCov_D`). Its base pages are the root's own (`uTree_F_cov`), so freeable
(`RInv.rootFree`). Its elements' shape and data (`endEls`): `end_els` (U9x10).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndVals
public import Proof.go_etcd_io.bbolt.Spill.BktEndOld

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section root
variable [GooseExts]

variable {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
  {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}

/-- **The root's elements at the end give the root shape and the writer's data** (`endEls`; the
root's tree's elements are its logical leaves', `E`, whose nested slots are owned, `hcovD`, `hDo`):
each a bucket entry (`RInv.rootBkt`) within the bounds (`RInv.entKeys`; a node's by `rootLoc`, a
page's by `RInv.shape0`), its name the start's (`RInv.ents`), its value a put child's new one
(`childSt`), a skipped child's or an unopened bucket's old one (`BktEndOld.oldN`, `oldU`). -/
theorem end_els (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B)
    (hvC : X.v = View.ofC X.v.base w.C) {D : List Nat} {E : List El}
    (hE : (X.leaves X0.rl).flatMap (List.map wEl) = E)
    (hDo : ∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ D)
    (hcovD : ∀ n v s, (n, v) ∈ rootEnts X → bucketCovers X0.v.pages v s → s ∈ D) :
    endEls X0 (spP X) D E := by
  classical
  have hok0 := hpre.1
  have hrlX : X.rl = X0.rl := hI.rl
  have hloc : bktLocalOK X X0.rl := hI.rootOK.1
  obtain ⟨-, B', hB', hcl, -, -, -, -⟩ := hloc
  rw [hB] at hB'; cases hB'
  have h0 : B.ib.root' ≠ W64 0 := by rw [hI.rootIb B hB]; exact hI.rootPg
  have h00 : B0.ib.root' ≠ W64 0 := hI.rootPg
  have hrt0 : rtOK X0 X0.rl := hpre.2.2.2.1 X0.rl (by rw [hB0]; simp)
  have hcp : X.v.pages = w0.C.pages := by
    have := congrArg View.pages hvC; simp only [View.ofC] at this; rw [this, hI.C]
  have hcp0 : X0.v.pages = w0.C.pages := by rw [← hI.pages]; exact hcp
  have hext : pagesExt X0.v.pages := hfv.2.2.1
  have hext' : pagesExt X.v.pages := by rw [hI.pages]; exact hext
  have hag0 : pagesLe X0.v.pages (spP X) := by rw [← hI.pages]; exact spP_agree hI.G hext'
  have hcm : w0.C.hwm ≤ X.t.mv.pgid'.toNat := Nat.le_trans hI.hwm0 hI.mark
  have h640 : ∀ p pg, X0.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp
    have := hI.cok.2.2.2.1 p pg (by rw [← hcp0]; exact hp)
    have := X.t.mv.pgid'.isLt
    omega
  -- the elements are the root's entries
  have hmemE : ∀ e ∈ E, ∃ we ∈ X.allEnts X0.rl, e = wEl we := by
    intro e he
    rw [← hE] at he
    obtain ⟨ws, hws, hm⟩ := List.mem_flatMap.1 he
    obtain ⟨we, hwe, rfl⟩ := List.mem_map.1 hm
    exact ⟨we, by unfold WX.allEnts; exact List.mem_flatten.2 ⟨ws, hws, hwe⟩, rfl⟩
  -- an entry within `bboltEntryMax`: a node's (`rootLoc`), a page's (`shape0`)
  have hbnd : ∀ we ∈ X.allEnts X0.rl, we.key.length + we.value.length ≤ bboltEntryMax := by
    intro we hwe
    have hwe' := hwe
    unfold WX.allEnts WX.leaves at hwe'
    obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hwe'
    have hrp : X.rootPid X0.rl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
    rw [hrp] at hws
    rcases walk_entryR hB hcl h0 _ _ (walkInv_root hcl h0) ws hws we hw with
      ⟨l, r, hr, -, hw'⟩ | ⟨c, p, pg, i, hc, hown, hpg, hlf, hi, rfl⟩
    · obtain ⟨B1, hB1, hn⟩ := hI.rootOK.2.2
      rw [hB] at hB1; cases hB1
      exact ((hn l r hr).2 we hw').2
    · obtain ⟨c0, hc0, hto⟩ := hI.rootPos B hB c hc
      obtain ⟨pgc, hpgc⟩ : ∃ pgc, X.v.pages !! c = some pgc := by
        cases hown with
        | root _ pg' h => exact ⟨_, h⟩
        | child _ pg' _ _ h _ _ _ => exact ⟨_, h⟩
      rw [hI.pages] at hpgc hown hpg
      have hown0 := ownHas_trans (ownTo_ownHas hto hpgc) hown
      have hs := hI.shape0 c0 p pg hc0 hown0 hpg hlf i hi
      rw [(mat_pageW_leaf pg i hlf).2.2.1, (mat_pageW_leaf pg i hlf).2.2.2]
      unfold leafKey leafValue
      have := Write.bytesAt_length_le pg (elemOff i + leafPos pg i) (leafKsize pg i)
      have := Write.bytesAt_length_le pg (elemOff i + leafPos pg i + leafKsize pg i)
        (leafVsize pg i)
      omega
  have hel : ∀ e ∈ E, e.1 % 2 = bucketLeafFlag ∧ (0 < e.2.1.length ∧ e.2.1.length ≤ maxKeySize) ∧
      e.2.1.length + e.2.2.length ≤ bboltEntryMax := by
    intro e he
    obtain ⟨we, hwe, rfl⟩ := hmemE e he
    refine ⟨?_, hI.entKeys we hwe, hbnd we hwe⟩
    unfold bucketLeafFlag; exact (isBkt_iff _).1 (hI.rootBkt we hwe)
  -- the names
  have hnames : E.map (fun e => e.2.1) = (rootEnts X0).map Prod.fst := by
    have h1 : (rootEnts X).map Prod.fst = (rootEnts X0).map Prod.fst := by
      rw [hI.ents, List.map_map]; rfl
    rw [← h1, ← hE, List.map_flatMap]
    unfold rootEnts
    rw [List.map_flatMap, hrlX]
    apply Write.flatMap_congr'
    intro ws hws
    rw [filterMap_bkt_keys ws fun we hw => hI.rootBkt we (by
      unfold WX.allEnts; exact List.mem_flatten.2 ⟨ws, hws, hw⟩), List.map_map]
    rfl
  -- the values
  have hval : ∀ e ∈ E, elVal X0 (spP X) D e := by
    intro e he
    obtain ⟨we, hwe, rfl⟩ := hmemE e he
    have hbk := hI.rootBkt we hwe
    have hre : (we.key, we.value) ∈ rootEnts X :=
      rootEnts_of_allEnts (X := X) (by rw [hrlX]; exact hwe) hbk
    have he' : (we.key, we.value) ∈ (rootEnts X0).map (fun e => (e.1, (ks e.1).entVal e.2)) :=
      hI.ents ▸ hre
    obtain ⟨⟨n0, v0⟩, hm0, heq⟩ := List.mem_map.1 he'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hk0, hv0⟩ := heq
    subst hk0
    have hbd := bktData_mem hok0 hB0 h00 hm0
    -- an old value over the view
    have lift : ∀ hwmv Sv L, bvalS X0.v.pages hwmv v0 Sv → bvalData X0.v.pages v0 L →
        v0 = we.value → bktDataOf X0 we.key v0 = GMap.ofList L → elVal X0 (spP X) D (wEl we) := by
      intro hwmv Sv L hS hd hvv hdo
      subst hvv
      have hagS : ∀ x ∈ Sv, spP X !! x = X0.v.pages !! x := by
        intro x hx
        obtain ⟨pg, hpg⟩ := bvalS_page hS hx
        rw [hpg]; exact hag0 x pg hpg
      refine ⟨hwmv, Sv, L, bvalS_agree hagS (Nat.le_refl _) hS, ?_, bvalData_agree hS hagS hd, ?_⟩
      · intro x hx
        obtain ⟨pg, hpg⟩ := bvalS_page hS hx
        exact hcovD _ _ x hre ⟨x, pg, (bvalS_has hS x).2 hx, hpg, Nat.le_refl _, by omega⟩
      · show bktData X0 we.key = _
        rw [hbd, hdo]
    cases hbm : B0.bm !! we.key with
    | none =>
      have hnk : we.key ∉ keys := fun h => by have := (hk _).1 h; rw [hbm] at this; cases this
      rw [hI.notKeys _ hnk] at hv0; simp only [KSt.entVal] at hv0
      obtain ⟨hwmv, Sv, hS, hd⟩ := oldU hok0 hI.cok hcp0 hB0 h00 hm0 hbm
      exact lift hwmv Sv _ hS hd hv0 (by simp only [bktDataOf, hB0, Option.bind_some, hbm]; rfl)
    | some c =>
      have hkk : we.key ∈ keys := (hk _).2 (by rw [hbm]; rfl)
      have hch := hI.kids we.key c hbm
      have hdo : bktDataOf X0 we.key v0 = GMap.ofList (lbktEnts X0 c) := by
        simp only [bktDataOf, hB0, Option.bind_some, hbm]
      cases hst : ks we.key with
      | todo => exact absurd hst (ksEnd hks hkk).1
      | val v p =>
        cases p with
        | false => exact absurd hst ((ksEnd hks hkk).2 v)
        | true =>
          rw [hst] at hv0 hch; simp only [KSt.entVal] at hv0
          subst hv0
          obtain ⟨S, hS, hDk, hd, -⟩ := hch
          refine ⟨X.t.mv.pgid'.toNat, S, lbktEnts X0 c, hS, ?_, hd, ?_⟩
          · intro x hx
            obtain ⟨pg, hpg⟩ := bvalS_page hS hx
            apply hDo
            refine List.mem_append_right _ (List.mem_flatMap.2 ⟨we.key, hkk, ?_⟩)
            rw [hDk]; exact mem_pgSlots_of hx hpg (Nat.le_refl _) (by omega)
          · show bktData X0 we.key = _
            rw [hbd, hdo]
      | nilc =>
        rw [hst] at hv0 hch; simp only [KSt.entVal] at hv0
        obtain ⟨-, C0, hC0, hrwe.key⟩ := hch
        obtain ⟨Dc0, -, hDc0⟩ := hI.lroot
        obtain ⟨-, -, -, -, hne, -⟩ := hDc0 we.key c hbm
        obtain ⟨hwmv, Sv, hS, hd⟩ :=
          oldN hok0 hreach hI.cok hcp0 hB0 h00 hrt0 h640 hm0 hbm hC0 hrwe.key hne
        exact lift hwmv Sv _ hS hd hv0 hdo
  exact endEls_of hel hval hnames

/-- **The root bucket's unspilled tree at the loop's end** (see the module doc). -/
theorem end_rootTree (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' ≠ null)
    (hvC : X.v = View.ofC X.v.base w.C) :
    ∃ rn h F D N E, X.node X0.rl B.bv.rootNode' = some rn ∧ rn.nv.parent' = null ∧
      rn.nv.spilled' = false ∧
      uTree X X0.rl (spP X) X.t.mv.pgid'.toNat B.bv.rootNode' none none h F D N E ∧
      spFree X w.fl w0.wtxid F ∧ D.Nodup ∧ (∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ D) ∧
      (∀ s ∈ D, s ∈ Lroot ++ keys.flatMap Dc) ∧ endEls X0 (spP X) D E := by
  classical
  have hok0 := hpre.1
  have hrlX : X.rl = X0.rl := hI.rl
  have hloc : bktLocalOK X X0.rl := hI.rootOK.1
  have hrt : rtOK X X0.rl := hI.rootOK.2.1
  have hloc' := hloc
  obtain ⟨-, B', hB', hcl, -, -, -, hvw⟩ := hloc'
  rw [hB] at hB'; cases hB'
  have h0 : B.ib.root' ≠ W64 0 := by rw [hI.rootIb B hB]; exact hI.rootPg
  have hcp : X.v.pages = w0.C.pages := by
    have := congrArg View.pages hvC; simp only [View.ofC] at this; rw [this, hI.C]
  have hext : pagesExt X0.v.pages := hfv.2.2.1
  have hext' : pagesExt X.v.pages := by rw [hI.pages]; exact hext
  have hag : pagesLe X.v.pages (spP X) := spP_agree hI.G hext'
  have hag0 : pagesLe X0.v.pages (spP X) := by rw [← hI.pages]; exact hag
  have hreachX : liveReach X := hI.G.2.2.2.2.1
  have hcm : w0.C.hwm ≤ X.t.mv.pgid'.toNat := Nat.le_trans hI.hwm0 hI.mark
  have hcm0 : w0.C.hwm ≤ X0.t.mv.pgid'.toNat := hI.hwm0
  have hcp0 : X0.v.pages = w0.C.pages := by rw [← hI.pages]; exact hcp
  have h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp
    have := hI.cok.2.2.2.1 p pg (by rw [← hcp]; exact hp)
    have := X.t.mv.pgid'.isLt
    omega
  have h640 : ∀ p pg, X0.v.pages !! p = some pg → p < 2 ^ 64 := by
    rw [← hI.pages]; exact h64
  have hcl0 : bktClean X0.v X0.t.mv.pgid'.toNat X0.rl B0 := (hok0.1.2.2.2.2.2 X0.rl B0 hB0).1
  have h00 : B0.ib.root' ≠ W64 0 := hI.rootPg
  have hrt0 : rtOK X0 X0.rl := hpre.2.2.2.1 X0.rl (by rw [hB0]; simp)
  have hbm : B.bm = B0.bm := by
    obtain ⟨B1, hB1, -, hbm⟩ := hI.root; rw [hB] at hB1; cases hB1; exact hbm
  obtain ⟨Dc0, hL, hDc0⟩ := hI.lroot
  -- a cached child's entry at the end, from its entry at the start
  have hentX : ∀ k c, B0.bm !! k = some c → ∃ v0, (k, v0) ∈ rootEnts X0 ∧
      (k, (ks k).entVal v0) ∈ rootEnts X := by
    intro k c hc
    obtain ⟨Cc, v, -, hent, -⟩ := (hok0.2.1 X0.rl B0 hB0).2 k c hc
    obtain ⟨-, -, -, -, hm⟩ := entryIn_rootEnts hok0 hreach hB0 h00 hrt0 h640 hent
    refine ⟨v, hm, ?_⟩
    rw [hI.ents]; exact List.mem_map.2 ⟨(k, v), hm, rfl⟩
  -- the nested values of the root's leaf nodes
  have hex : ∀ (l : Loc) (r : NRec) (i : Nat) (w' : WEntry), B.ns !! l = some r →
      r.nv.isLeaf' = true → r.ws[i]? = some w' →
      isBktFlag w'.flags → ∃ S, bvalS (spP X) X.t.mv.pgid'.toNat w'.value S := by
    intro l r i w' hr hl hw hbk
    have hwm := List.mem_of_getElem? hw
    cases hbmk : B.bm !! w'.key with
    | none =>
      obtain ⟨S, hS, -⟩ := bvalS_uncachedL hloc hI.cok hcp hcm hag hB hr hl hwm hbk hbmk
      exact ⟨S, hS⟩
    | some c =>
      have hc : B0.bm !! w'.key = some c := by rw [← hbm]; exact hbmk
      have hkk : w'.key ∈ keys := (hk _).2 (by rw [hc]; rfl)
      have hwA := mem_allEnts_nodeL hreachX hloc hrt hB h0 hr hl hwm
      have hre : (w'.key, w'.value) ∈ rootEnts X :=
        rootEnts_of_allEnts (X := X) (by rw [hrlX]; exact hwA) hbk
      have he' : (w'.key, w'.value) ∈ (rootEnts X0).map (fun e => (e.1, (ks e.1).entVal e.2)) :=
        hI.ents ▸ hre
      obtain ⟨⟨k0, v0⟩, hm0, heq⟩ := List.mem_map.1 he'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hk0, hv0⟩ := heq
      subst hk0
      have hch := hI.kids w'.key c hc
      cases hst : ks w'.key with
      | todo => exact absurd hst (ksEnd hks hkk).1
      | val v p =>
        cases p with
        | false => exact absurd hst ((ksEnd hks hkk).2 v)
        | true =>
          rw [hst] at hv0 hch; simp only [KSt.entVal] at hv0
          obtain ⟨S, hS, -⟩ := hch
          exact ⟨S, by rw [← hv0]; exact hS⟩
      | nilc =>
        rw [hst] at hv0 hch; simp only [KSt.entVal] at hv0
        obtain ⟨-, C0, hC0, hrn0⟩ := hch
        obtain ⟨-, S, hS, -⟩ := nil_val hok0 hreach hI.cok hcp0 hcm hag0 hB0 h00 hrt0 h640 hc hC0
          hrn0 hm0
        exact ⟨S, by rw [← hv0]; exact hS⟩
  let Sb : Loc → Nat → List Nat := fun l i =>
    match (B.ns !! l).bind (fun r => r.ws[i]?) with
    | some (w' : WEntry) =>
      if h : isBktFlag w'.flags ∧ ∃ S, bvalS (spP X) X.t.mv.pgid'.toNat w'.value S
      then Classical.choose h.2 else []
    | none => []
  have hsb : ∀ (l : Loc) (r : NRec) (i : Nat) (w' : WEntry), B.ns !! l = some r →
      r.nv.isLeaf' = true → r.ws[i]? = some w' →
      (isBktFlag w'.flags → bvalS (spP X) X.t.mv.pgid'.toNat w'.value (Sb l i)) ∧
      (¬ isBktFlag w'.flags → Sb l i = []) := by
    intro l r i w' hr hl hw
    have e1 : (B.ns !! l).bind (fun r => r.ws[i]?) = some w' := by rw [hr]; exact hw
    refine ⟨fun hbk => ?_, fun hbk => ?_⟩
    · have hh : isBktFlag w'.flags ∧ ∃ S, bvalS (spP X) X.t.mv.pgid'.toNat w'.value S :=
        ⟨hbk, hex l r i w' hr hl hw hbk⟩
      have e : Sb l i = Classical.choose hh.2 := by simp only [Sb, e1, dif_pos hh]
      rw [e]; exact Classical.choose_spec hh.2
    · simp only [Sb, e1]
      rw [dif_neg (fun h => hbk h.1)]
  obtain ⟨rn, h, F, D, N, E, hnode, hpar, hsp, hu, hE⟩ := end_uTree hI hB hrn hvC hext hsb
  -- the pieces
  obtain ⟨t, ht, htp, hth, -⟩ := hrt
  have hpos := positions_rt X X0.rl t ht htp hth
  have hpd : pagesDisjoint X.v.pages := by
    obtain ⟨C', hC', hvC'⟩ := hvw; rw [← hvC']; exact hC'.2.2.1
  have hg := end_gdisj hpre hreach hfv hB0 hk hI hks hvC
  have hkn : keysNe E := by
    rw [← hE]
    have h1 := leaves_keys_ne hloc
    have e : ∀ L : List (List WEntry), L.flatMap (List.map wEl) = L.flatten.map wEl := by
      intro L; induction L with
      | nil => rfl
      | cons a t ih => simp only [List.flatMap_cons, List.flatten_cons, List.map_append, ih]
    unfold keysNe
    rw [e]
    exact List.pairwise_map.2 h1
  have hrp : X.rootPid X0.rl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  have hres0 : resolve B B.ib.root' = some B.bv.rootNode' := by
    rw [← hrp]; exact resolve_rootPid hB hcl hrn
  have hroot : B.ib.root' ∈ t.pos := by rw [← hrp, ← htp]; exact pid_mem_pos t
  obtain ⟨hnd, hlab⟩ := uTree_piecesE hB hcl h0 hpd h64 hag (hE ▸ hg) ht hpos hu
    (fun e he => he) hkn B.ib.root' hres0 hroot
  -- every slot is owned
  have hDi : ∀ s ∈ D, s ∈ Lroot ++ keys.flatMap Dc := by
    intro s hs
    rcases hlab s hs with ⟨-, q, hq⟩ | ⟨e, he, hb, hc⟩
    · exact List.mem_append_left _ (own_Lroot hpre hreach hfv hB0 hk hI hq)
    · have he' := ent_of_E0 (X := X) (by rw [hrlX, hE]; exact he) hb
      rcases ent_class hpre hreach hfv hB0 hk hI hks hvC he' hc with ⟨hkk, hsD⟩ | ⟨-, hsL⟩
      · exact List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hkk, hsD⟩)
      · exact List.mem_append_left _ hsL
  -- an entry of the root at the end covers its value's slots in the view
  have hleaf : ∀ n v s, (n, v) ∈ rootEnts X → bucketCovers X0.v.pages v s → s ∈ D := by
    intro n v s hm hc
    obtain ⟨ws, hws, w', hw', hbk, -, rfl⟩ := mem_rootEnts_leaf hm
    rw [hrlX] at hws
    exact uTree_leafCov hB hcl hrn hag hu hws hw' hbk (by rw [hI.pages]; exact hc)
  -- every owned slot is a slot
  have hDo : ∀ s ∈ Lroot ++ keys.flatMap Dc, s ∈ D := by
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · rw [hL] at hs
      obtain ⟨-, hlc, hnD0⟩ := mem_rootOwn.1 hs
      rcases hlc with ⟨bl, e, hbl, he, h1, h2⟩ | ⟨n, v, hnv, hbl, hbc⟩
      · obtain ⟨Bl, hBl⟩ := Option.ne_none_iff_exists'.1 hbl
        rcases bkt_root_or_child hok0 hreach hB0 hBl with hb | ⟨n, hn⟩
        · subst hb
          obtain ⟨pid, hpid⟩ := coverW_of_extent (X := X) (by rw [hB]; simp)
            (by rw [hI.rootExt]; exact he) h1 h2
          exact uTree_coverW hB hcl hrn hag hu hpid
        · have hnk : n ∈ keys := (hk n).2 (by rw [hn]; rfl)
          obtain ⟨Cc, hCc, -, -, hne, -, -, -, hnil, hrnd⟩ := hDc0 n bl hn
          rw [hBl] at hCc; cases hCc
          obtain ⟨pid, hpid⟩ := coverW_of_extent hbl he h1 h2
          by_cases hrn0 : Bl.bv.rootNode' = null
          · -- a skipped child: its value's pages, an entry of the root at the end
            have hst : ks n = .nilc := by
              rcases hI.nilKids n bl Bl hn hBl hrn0 with h | ⟨h, -⟩
              · exact h
              · exact absurd h (ksEnd hks hnk).1
            obtain ⟨v0, hm0, hmX⟩ := hentX n bl hn
            rw [hst] at hmX; simp only [KSt.entVal] at hmX
            obtain ⟨hib, S, hS, hsl⟩ := nil_val hok0 hreach hI.cok hcp0 hcm0
              (fun _ _ h => h) hB0 h00 hrt0 h640 hn hBl hrn0 hm0
            have hclc : bktClean X0.v X0.t.mv.pgid'.toNat bl Bl := (hok0.1.2.2.2.2.2 bl Bl hBl).1
            by_cases hc0 : Bl.ib.root' = W64 0
            · exact (inline_noCover hBl hclc hrn0 hc0 hpid).elim
            have hwfc : treeWF X0.v.pages X0.t.mv.pgid'.toNat Bl.ib.root'.toNat :=
              (hclc.2.1 hc0).2 hrn0
            have hnmc : Bl.nm = ∅ := (hclc.2.2.1 hrn0).2
            have hrpc : X0.rootPid bl = Bl.ib.root' := by unfold WX.rootPid; rw [hBl]; rfl
            obtain ⟨-, hp, e', he', h1', h2'⟩ := hpid
            obtain ⟨id, pg, hth, hpg, a1, a2⟩ := walkCov_pages hBl hc0 X0.fuel Bl.ib.root' hwfc
              (fun d _ => by rw [hnmc]; rfl) s
              (Or.inl ⟨pid, by rw [← hrpc]; exact hp, e', he', h1', h2'⟩)
            have hr : Bl.ib.root'.toNat = inBucketRoot v0 := by rw [hib]; rfl
            refine hleaf n v0 s hmX ⟨id, pg, ?_, hpg, a1, a2⟩
            exact bucketHas.file v0 id (by rw [← hr]; intro e0; exact hc0 (by
              apply BitVec.eq_of_toNat_eq; rw [e0]; rfl)) (by rw [← hr]; exact hth)
          · -- a child with a root node: its starting tree owns the slot, not the root
            obtain ⟨rn0, h0', F0, N0, E0, -, -, hu0, -⟩ := hrnd hrn0
            have hcl0' : bktClean X0.v X0.t.mv.pgid'.toNat bl Bl := (hok0.1.2.2.2.2.2 bl Bl hBl).1
            have hag00 : pagesLe X0.v.pages (spP X0) := by
              rw [spP_clean hok0.1.2.1.2.1]; exact fun _ _ h => h
            exact absurd (List.mem_flatMap.2 ⟨n, hnk, uTree_coverW hBl hcl0' hrn0 hag00 hu0 hpid⟩)
              hnD0
      · -- an unopened bucket: not iterated, its entry unchanged
        have hn0 : B0.bm !! n = none := by unfold bktLoc at hbl; rw [hB0] at hbl; exact hbl
        have hnk : n ∉ keys := fun h => by have := (hk n).1 h; rw [hn0] at this; cases this
        have hmX : (n, v) ∈ rootEnts X := by
          rw [hI.ents]
          refine List.mem_map.2 ⟨(n, v), hnv, ?_⟩
          simp only [hI.notKeys n hnk, KSt.entVal]
        obtain ⟨id, pg, hbh, hpg, a1, a2⟩ := hbc
        exact hleaf n v s hmX ⟨id, pg, hbh, hpg, a1, a2⟩
    · obtain ⟨k, hkk, hsD⟩ := List.mem_flatMap.1 hs
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((hk k).1 hkk)
      have hch := hI.kids k c hc
      cases hst : ks k with
      | todo => exact absurd hst (ksEnd hks hkk).1
      | nilc => rw [hst] at hch; rw [hch.1] at hsD; cases hsD
      | val v p =>
        cases p with
        | false => exact absurd hst ((ksEnd hks hkk).2 v)
        | true =>
          rw [hst] at hch
          obtain ⟨S, hS, hDk, -⟩ := hch
          obtain ⟨v0, -, hmX⟩ := hentX k c hc
          rw [hst] at hmX; simp only [KSt.entVal] at hmX
          obtain ⟨ws, hws, w', hw', hbk, hwk, hwv⟩ := mem_rootEnts_leaf hmX
          rw [hDk] at hsD
          have hP : ∀ x ∈ S, ((spP X) !! x).isSome := by
            rcases hS.2 with ⟨-, rfl, -⟩ | ⟨-, h', hs'⟩
            · intro x hx; cases hx
            · exact sTree_isSome hs'
          obtain ⟨x, hx, pg, hpg, a1, a2⟩ := mem_pgSlots hP hsD
          refine entCov_D hu (wEl w') ?_ ((isBkt_iff _).1 hbk) s
            ⟨x, pg, by rw [show (wEl w').2.2 = v from hwv]; exact (bvalS_has hS x).2 hx, hpg,
              a1, a2⟩
          rw [← hE, ← hrlX]
          exact List.mem_flatMap.2 ⟨ws, hws, List.mem_map_of_mem hw'⟩
  -- the base pages are the root's own
  have hF : spFree X w.fl w0.wtxid F := by
    refine hI.rootFree F fun id hid => ⟨?_, ?_, (uTree_F_view hu id hid).2⟩
    · obtain ⟨q, hq⟩ := uTree_F_cov hB hcl h0 ht hpos hu B.ib.root' hres0 hroot id hid
      exact own_Lroot hpre hreach hfv hB0 hk hI hq
    · rw [← hI.pages]; exact (uTree_F_view hu id hid).1
  exact ⟨rn, h, F, D, N, E, hnode, hpar, hsp, hu, hF, hnd, hDo, hDi,
    end_els hpre hreach hfv hB0 hk hI hks hB hvC hE hDo hleaf⟩

end root

end Spill

end bbolt
end EtcdGrove
end Perennial
