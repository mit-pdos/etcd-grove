/-
`Bucket.spill`'s root loop (U9x, `notes/bbolt-proof-plan.md`): **the invariant after a child's
spill** (`rinv_spilled'`, `BktLoopStep.rinv_spilled`'s proof). The child's spill (`bkDone`: a
`spFrame` of the child's bucket, then its header `setBkt`) keeps every other bucket modulo sources
(`bktKept`), so the root bucket's facts (`rootLoc_kept`), entries and keys, and the other children's
states (`childSt_kept`: their unspilled trees, `uTree_kept`, over slots the step does not touch);
the child's own state becomes the header of its written tree (`bvalS`, `bvalData`); the slots are
the child's new ones in place of its old ones.

The view after the step is the committed state's at the new mapping (`hv'`, the caller's
`wdbW`): `bkDone` does not say the view's root is kept, which `bktLocalOK`'s `viewWF` needs.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureKeepTree
public import Proof.go_etcd_io.bbolt.Spill.BktSpec
public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Spill.SlotInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeBnd
public import Proof.go_etcd_io.bbolt.Spill.BktLoopExt

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section spilled
variable [GooseExts]

theorem inBucketOf_encode (ib : InBucket) : inBucketOf (encode ib) = ib := by
  unfold inBucketOf bytesAt
  rw [List.drop_zero, List.take_of_length_le (by simp), ByteEncoding.decode_encode]

theorem encode_ib_length (ib : InBucket) : (encode ib).length = 16 := by simp

/-- A nested bucket's data in a page map agreeing on its pages. -/
theorem bvalData_agree {P P' : Pages} {hwm : Nat} {v : List w8} {S : List Nat} {E : List BoltEnt}
    (hb : bvalS P hwm v S) (hag : ∀ x ∈ S, P' !! x = P !! x) (hd : bvalData P v E) :
    bvalData P' v E := by
  refine ⟨hd.1, fun hr => ?_⟩
  rcases hb.2 with ⟨hr0, -⟩ | ⟨-, h, hs⟩
  · exact absurd hr0 hr
  obtain ⟨d1, d2⟩ := hd.2 hr
  refine ⟨by rw [← treeEls_entries, treeEls_agree hs hag, treeEls_entries]; exact d1, ?_⟩
  unfold plainTree at d2 ⊢
  rw [treeLeaves_sTree_agree hs hag]; exact d2

theorem allEnts_kept {X X' : WX} {bl : Loc}
    (h : (X'.leaves bl).map (List.map wDat) = (X.leaves bl).map (List.map wDat)) {we' : WEntry}
    (hw : we' ∈ X'.allEnts bl) : ∃ we ∈ X.allEnts bl, we'.key = we.key := by
  have e : (X'.allEnts bl).map wDat = (X.allEnts bl).map wDat := by
    unfold WX.allEnts; rw [List.map_flatten, List.map_flatten, h]
  obtain ⟨we, hwe, he⟩ := mem_of_dat e hw
  exact ⟨we, hwe, wDat_key he⟩

/-- `allEnts_kept` with the flags. -/
theorem allEnts_keptF {X X' : WX} {bl : Loc}
    (h : (X'.leaves bl).map (List.map wDat) = (X.leaves bl).map (List.map wDat)) {we' : WEntry}
    (hw : we' ∈ X'.allEnts bl) : ∃ we ∈ X.allEnts bl, we'.flags = we.flags := by
  have e : (X'.allEnts bl).map wDat = (X.allEnts bl).map wDat := by
    unfold WX.allEnts; rw [List.map_flatten, List.map_flatten, h]
  obtain ⟨we, hwe, he⟩ := mem_of_dat e hw
  exact ⟨we, hwe, congrArg (fun d => d.1) he⟩

/-- **The root bucket's facts through a kept step.** -/
theorem rootLoc_kept {X X' : WX} {bl : Loc} (h : rootLoc X bl) (hkept : bktKept X X' bl)
    (hv : X'.v.pages = X.v.pages) (hvw : viewWF X'.v)
    (hh : X.t.mv.pgid'.toNat ≤ X'.t.mv.pgid'.toNat) (hlB : bl ∈ X'.liveB)
    (hreach : liveReach X) (hp' : derefPre X') (hf' : liveFresh X') (hfuel : X'.fuel = X.fuel)
    (h0 : ∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0)
    (hvs : ∀ B B' l r r', X.t.bs !! bl = some B → X'.t.bs !! bl = some B' → B.ns !! l = some r →
      B'.ns !! l = some r' → l ∈ X.live → leafVs r → leafVs r') :
    rootLoc X' bl := by
  obtain ⟨hloc, hrt, B, hB, hn⟩ := h
  obtain ⟨B', hB', hs, hns⟩ := hkept B hB
  refine ⟨bktLocalOK_kept hloc hkept hv hvw hh hlB hreach hp' hf' ?_ hvs,
    rtOK_kept hB hB' hs hns hv hfuel hrt, B', hB', ?_⟩
  · intro B1 B1' hb1 _ e; rw [hB] at hb1; cases hb1; exact absurd e (h0 B hB)
  · intro l r' hr'
    obtain ⟨r, hr, e⟩ := bwd_kept hns hr'
    obtain ⟨⟨n1, n2⟩, n3⟩ := hn l r hr
    refine ⟨⟨fun hp => ?_, fun hl => ?_⟩, fun w' hw' => ?_⟩
    · rw [length_of_dat e.2.2.1]; exact n1 (by rw [← nodeSim_parent e]; exact hp)
    · rw [length_of_dat e.2.2.1]; exact n2 (by rw [← nodeSim_isLeaf e]; exact hl)
    · obtain ⟨w, hw, he⟩ := mem_of_dat e.2.2.1 hw'
      rw [wDat_key he, wDat_value he]; exact n3 w hw

/-- **A child's state through a kept step** (its bucket kept, its slots untouched). -/
theorem childSt_kept {X0 X X' : WX} {w w' : WDb} {txid : w64} {c : Loc} {D : List Nat} {s : KSt}
    (hold : childSt X0 X w txid c D s) (hkept : bktKept X X' c)
    (hvs : ∀ B B' l r r', X.t.bs !! c = some B → X'.t.bs !! c = some B' → B.ns !! l = some r →
      B'.ns !! l = some r' → l ∈ X.live → leafVs r → leafVs r')
    (hv : X'.v.pages = X.v.pages) (hvw : viewWF X'.v)
    (hh : X.t.mv.pgid'.toNat ≤ X'.t.mv.pgid'.toNat) (hlB : X'.liveB = X.liveB) (hrl : X'.rl = X.rl)
    (hreach : liveReach X) (hp' : derefPre X') (hf' : liveFresh X') (hfuel : X'.fuel = X.fuel)
    (hP : ∀ x ∈ D, spP X' !! x = spP X !! x)
    (hfree : ∀ F, (∀ id ∈ F, id ∈ D) → spFree X w.fl txid F → spFree X' w'.fl txid F) :
    childSt X0 X' w' txid c D s := by
  cases s with
  | nilc => exact hold
  | val v p =>
    obtain ⟨S, hb, hD, hdat, hvl⟩ := hold
    have hag : ∀ x ∈ S, spP X' !! x = spP X !! x :=
      fun x hx => hP x (by rw [hD]; exact mem_pgSlots_self hx)
    exact ⟨S, bvalS_agree hag hh hb, by rw [hD, pgSlots_congr hag], bvalData_agree hb hag hdat, hvl⟩
  | todo =>
    obtain ⟨C, hC, hlive, hbm, hne, hloc, hrt, hents, hnil, htree⟩ := hold
    obtain ⟨C', hC', hs, hns⟩ := hkept C hC
    have hlB' : c ∈ X'.liveB := by rw [hlB]; exact hlive
    refine ⟨C', hC', hlB', by rw [hs.2.2.2.1]; exact hbm, by rw [hrl]; exact hne, fun hn => ?_,
      rtOK_kept hC hC' hs hns hv hfuel hrt, ?_, fun hn => ?_, fun hn => ?_⟩
    · rw [hs.1] at hn
      refine bktLocalOK_kept (hloc hn) hkept hv hvw hh hlB' hreach hp' hf' ?_ hvs
      intro B B' hB _ _ e; rw [hC] at hB; cases hB; exact absurd e hn
    · rw [Write.lbktEnts_eq_of_dat X X' c (leaves_kept hC hC' hs hns hv hfuel)]; exact hents
    · rw [hs.1] at hn; exact hnil hn
    · rw [hs.1] at hn ⊢
      obtain ⟨rn, h, F, N, E, hrn, hpar, hu, hfr, hE, hpl⟩ := htree hn
      have hk := nodesKept_of_kept hkept hv hreach hp' hlB'
      obtain ⟨rn', hrn', e, -⟩ := hk.2 _ rn hrn
      exact ⟨rn', h, F, N, E, hrn', by rw [nodeSim_parent e]; exact hpar,
        uTree_kept hk hh hu hP, hfree F (uTree_F_D hu) hfr, hE, hpl⟩

theorem flatMap_upd_filter {keys : List GoString} {Dc : GoString → List Nat} {k : GoString}
    (D' : List Nat) :
    (keys.filter fun k' => decide (k' ≠ k)).flatMap (upd Dc k D') =
      (keys.filter fun k' => decide (k' ≠ k)).flatMap Dc := by
  apply flatMap_congr'
  intro x hx
  have : x ≠ k := by simpa using (List.mem_filter.1 hx).2
  unfold upd; rw [if_neg this]

/-- The owned slots with the child's replaced, as `othersO` and the child's. -/
theorem perm_upd {Lroot : List Nat} {keys : List GoString} {Dc : GoString → List Nat}
    {k : GoString} (hnd : keys.Nodup) (hk : k ∈ keys) (D' : List Nat) :
    (Lroot ++ keys.flatMap (upd Dc k D')).Perm (othersO Lroot keys Dc k ++ D') := by
  unfold othersO
  rw [List.append_assoc]
  refine List.Perm.append_left _ ?_
  have := flatMap_perm_split (Dc := upd Dc k D') hnd hk
  rw [flatMap_upd_filter, upd_same] at this
  exact this

theorem perm_old {Lroot : List Nat} {keys : List GoString} {Dc : GoString → List Nat}
    {k : GoString} (hnd : keys.Nodup) (hk : k ∈ keys) :
    (Lroot ++ keys.flatMap Dc).Perm (othersO Lroot keys Dc k ++ Dc k) := by
  unfold othersO
  rw [List.append_assoc]
  exact List.Perm.append_left _ (flatMap_perm_split hnd hk)

theorem mem_othersO {Lroot : List Nat} {keys : List GoString} {Dc : GoString → List Nat}
    {k k' : GoString} (hk' : k' ∈ keys) (hne : k' ≠ k) {x : Nat} (hx : x ∈ Dc k') :
    x ∈ othersO Lroot keys Dc k :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨k', List.mem_filter.2 ⟨hk', by simpa using hne⟩, hx⟩)

set_option maxHeartbeats 1000000 in
/-- **After `child.spill()`** (see the module doc). -/
theorem rinv_spilled' {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hnd : keys.Nodup)
    {k : GoString} {c : Loc} {C : BRec} (hk : k ∈ keys) (hks : ks k = .todo)
    (hc : B0.bm !! k = some c) (hC : X.t.bs !! c = some C) (hnn : C.bv.rootNode' ≠ null)
    {X' : WX} {w' : WDb} {st' : List FLStep}
    (hd : bkDone X X' w w' c C (othersO Lroot keys Dc k) (Dc k) st')
    (hv' : X'.v = View.ofC X'.v.base w'.C) (hbufs : bufsOK X' w0.C w'.fl) :
    ∃ C' D', X'.t.bs !! c = some C' ∧ C'.bv.rootNode' ≠ null ∧ c ∈ X'.liveB ∧
      RInv X0 w0 B0 keys Lroot X' w' (st ++ st') (upd Dc k D')
        (upd ks k (.val (encode C'.ib) false)) := by
  obtain ⟨hstep, hcase⟩ := hd
  rcases hcase with ⟨h0, -, -⟩ | ⟨-, X1, T, B1, rt, rr, S, D', h', hfr, hB1, hrr, hrtl, hrsp,
    hrpar, hX', hsT, hD', hsi, hD1, hD2, hents, hplain⟩
  · exact absurd h0 hnn
  have hgrow : markGrow X X' := hstep.2.2.2.2.2.2.2.2.2.1
  have hsrc : srcGrow X X' w.fl := hstep.2.2.2.2.2.2.2.2.2.2.1
  have hwbk : wbKeep w w' := hstep.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hstep
  have htodo := hI.kids k c hc
  rw [hks] at htodo
  obtain ⟨C0, hC0, hlive, -, hcne, -, -, hlb, -, -⟩ := htodo
  rw [hC] at hC0; cases hC0
  have hwx : w.wtxid = w0.wtxid := wtxid_of_C hI.C
  have hcX0 : c ≠ X0.rl := by rw [← hI.rl]; exact hcne
  obtain ⟨f1, -, -, f4, -, -, f7, f8, f9, -, -, f12, f13, -, -, -, f17⟩ := hfr
  subst hX'
  -- the other buckets
  have hkept : ∀ bl, bl ≠ c → bktKept X (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')) bl := by
    intro bl hbl B hB
    obtain ⟨B', hB', hs, hns⟩ := f12 bl hbl B hB
    refine ⟨B', ?_, hs, hns⟩
    show (X1.t.bs.insert c _) !! bl = some B'
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hbl)]; exact hB'
  have hvs : ∀ bl, bl ≠ c → ∀ B B' l r r', X.t.bs !! bl = some B →
      (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).t.bs !! bl = some B' → B.ns !! l = some r →
      B'.ns !! l = some r' → l ∈ X.live → leafVs r → leafVs r' := by
    intro bl hbl B B' l r r' hB hB' hr hr' hlv hl
    have e : (X1.t.bs.insert c (bkRooted B1 rt rr.nv.pgid')) !! bl = some B' := hB'
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hbl)] at e
    exact f17 bl B B' l r r' hB e hr hr' (fun h => absurd h hbl) hlv hl
  have hbs : ∀ bl, ((X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).t.bs !! bl).isSome =
      (X.t.bs !! bl).isSome := by
    intro bl
    show ((X1.t.bs.insert c _) !! bl).isSome = _
    by_cases hbl : bl = c
    · subst hbl; rw [GMap.lookup_insert, hC]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hbl)]
      cases hB : X.t.bs !! bl with
      | none => rw [f13 bl hbl hB]
      | some B => obtain ⟨B', hB', -⟩ := f12 bl hbl B hB; rw [hB']; rfl
  have hfuel := fuel_kept s3 hbs
  have hvw : viewWF (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).v :=
    ⟨w'.C, by rw [s1, hI.C]; exact hI.cok, hv'.symm⟩
  have hreach : liveReach X := hI.G.2.2.2.2.1
  have hp' := s4.2.2.1
  have hf' := s4.2.2.2.1
  have hlB : (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).liveB = X.liveB := f4
  have hrl : (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).rl = X.rl := f1
  have hh : X.t.mv.pgid'.toNat ≤ (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).t.mv.pgid'.toNat := f9
  have hO : ∀ x ∈ othersO Lroot keys Dc k,
      spP (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')) !! x = spP X !! x := by
    intro x hx
    by_cases hne : spP (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')) !! x = spP X !! x
    · exact hne
    · exact absurd hx (s7 x hne).1
  -- the root bucket
  have hrootB : ∀ B, X.t.bs !! X0.rl = some B → B.ib.root' ≠ W64 0 := by
    intro B hB; rw [hI.rootIb B hB]; exact hI.rootPg
  have hlBr : X0.rl ∈ (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).liveB := by
    rw [hlB]; exact hI.rootOK.1.1
  obtain ⟨Br, hBr, hBrb, hBrm⟩ := hI.root
  obtain ⟨Br', hBr', hsr, hnsr⟩ := hkept X0.rl (Ne.symm hcX0) Br hBr
  have hleavesR := leaves_kept hBr hBr' hsr hnsr s3 hfuel
  -- the child's new header
  have hroot : inBucketRoot (encode (bkRooted B1 rt rr.nv.pgid').ib) = rr.nv.pgid'.toNat := by
    unfold inBucketRoot; rw [inBucketOf_encode]; rfl
  have hpg2 : 2 ≤ rr.nv.pgid'.toNat := by
    cases hsT.wf with | page _ _ h2 _ _ _ _ _ => exact h2
  have hBc : (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')).t.bs !! c =
      some (bkRooted B1 rt rr.nv.pgid') := GMap.lookup_insert _ _ _
  refine ⟨bkRooted B1 rt rr.nv.pgid', D', hBc, ?_, by rw [hlB]; exact hlive, ?_⟩
  · intro e
    have h1 := (hp'.2.2.1 c _ hBc).2
    have h2 : B1.ns !! rt = some rr := hrr
    have h1' : B1.ns !! null = none := h1
    simp only [bkRooted] at e
    rw [← e] at h1'; rw [h1'] at h2; cases h2
  exact {
    C := s1.trans hI.C
    fl := by rw [s2, hI.fl, hwx, applySteps_append]
    pages := s3.trans hI.pages
    rl := hrl.trans hI.rl
    mark := Nat.le_trans hI.mark hh
    G := by rw [← hwx]; exact s4
    root := ⟨Br', hBr', by rw [hsr.1]; exact hBrb, by rw [hsr.2.2.2.1]; exact hBrm⟩
    rootOK := rootLoc_kept hI.rootOK (hkept X0.rl (Ne.symm hcX0)) s3 hvw hh hlBr hreach hp' hf'
      hfuel hrootB (hvs X0.rl (Ne.symm hcX0))
    rootIb := by
      intro B hB
      rw [hBr'] at hB; cases hB
      rw [hsr.2.1]; exact hI.rootIb Br hBr
    slots := slotInv_perm (perm_upd hnd hk D').symm hsi
    base := by
      intro s hs
      rcases hI.base s hs with hm | hp
      · rcases List.mem_append.1 ((perm_old hnd hk).mem_iff.1 hm) with ho | hdk
        · exact Or.inl ((perm_upd hnd hk D').mem_iff.2 (List.mem_append_left _ ho))
        · rcases hD1 s hdk with h1 | h1
          · exact Or.inl ((perm_upd hnd hk D').mem_iff.2 (List.mem_append_right _ h1))
          · exact Or.inr h1
      · exact Or.inr (s6 s hp)
    new := by
      intro s hs
      have hst : ∀ x ∈ st, x ∈ st ++ st' := fun x hx => List.mem_append_left _ hx
      have hold : s ∈ Lroot ++ keys.flatMap Dc →
          s ∈ treeSlots w0.C ∨ newSlot (st ++ st') X0.t.mv.pgid'.toNat s := by
        intro hm
        rcases hI.new s hm with h | h
        · exact Or.inl h
        · exact Or.inr (newSlot_mono h hst (Nat.le_refl _))
      rcases List.mem_append.1 ((perm_upd hnd hk D').mem_iff.1 hs) with ho | hdk
      · exact hold ((perm_old hnd hk).mem_iff.2 (List.mem_append_left _ ho))
      · rcases hD2 s hdk with h1 | h1
        · exact hold ((perm_old hnd hk).mem_iff.2 (List.mem_append_right _ h1))
        · exact Or.inr (newSlot_mono h1 (fun x hx => List.mem_append_right _ hx) hI.mark)
    agree := by
      intro x hx
      rw [hO x (List.mem_append_left _ hx)]; exact hI.agree x hx
    kids := by
      intro k' c' hc'
      by_cases e : k' = k
      · subst e
        rw [hc] at hc'; cases hc'
        unfold upd; rw [if_pos rfl, if_pos rfl]
        refine ⟨S, ⟨by rw [encode_ib_length]; omega, Or.inr ⟨by rw [hroot]; omega, h', by rw [hroot]; exact hsT⟩⟩,
          hD', ⟨fun h0 => absurd h0 (by rw [hroot]; omega), fun _ => ?_⟩,
          by rw [encode_ib_length]; omega⟩
        rw [hroot, ← hlb]
        exact ⟨hents, hplain⟩
      · have hcc : c' ≠ c := by
          intro h; subst h; exact e (hI.inj k' k c' hc' hc)
        have hk' : k' ∈ keys := hI.keysAll k' (by rw [hc']; rfl)
        unfold upd; rw [if_neg e, if_neg e]
        refine childSt_kept (hI.kids k' c' hc') (hkept c' hcc) (hvs c' hcc) s3 hvw hh hlB hrl
          hreach hp' hf' hfuel (fun x hx => hO x (mem_othersO hk' e hx)) ?_
        intro F hF hfr
        rw [← hwx] at hfr ⊢
        exact s8.1 F (fun id hid => mem_othersO hk' e (hF id hid)) hfr
    ents := by
      rw [show rootEnts (X1.setBkt c (bkRooted B1 rt rr.nv.pgid')) = rootEnts X from
        Write.rootEnts_eq_of_dat X _ (by rw [hrl, hI.rl]; exact hleavesR), hI.ents]
      congr 1; funext e
      unfold upd
      by_cases h : e.1 = k
      · rw [if_pos h, h, hks]; rfl
      · rw [if_neg h]
    keysAll := hI.keysAll
    rootPg := hI.rootPg
    entKeys := by
      intro we hwe
      obtain ⟨we0, hwe0, hk0⟩ := allEnts_kept hleavesR hwe
      rw [hk0]; exact hI.entKeys we0 hwe0
    rootBkt := by
      intro we hwe
      obtain ⟨we0, hwe0, hf0⟩ := allEnts_keptF hleavesR hwe
      rw [hf0]; exact hI.rootBkt we0 hwe0
    inj := hI.inj
    cok := hI.cok
    bufs := hbufs
    grow := markGrow_trans hI.grow hgrow
    src := bufSrc_grow hI.src hsrc (fun y hy => by
      rw [hI.fl] at hy; exact applySteps_free_sub st w0.fl w0.wtxid y hy) hI.mark
    wb := wbKeep_trans hI.wb hwbk
    rootPos := by
      intro B hB
      rw [hBr'] at hB; cases hB
      exact rootUnder_sim (hI.rootPos Br hBr) hsr hnsr
    shape0 := hI.shape0
    hwm0 := hI.hwm0
    freeNC := hI.freeNC
    tt := (f7 : X1.t.t = X.t.t).trans hI.tt
    same := fun h => absurd h (same_upd_val hk _ _)
    putRoot := by
      intro hp B hB
      rw [hBr'] at hB; cases hB
      rw [hsr.1]
      exact hI.putRoot (putRoot_upd (fun _ e => by cases e) hp) Br hBr
    mvEq := mv_trans hI.mvEq (f8 : X1.t.mv = { X.t.mv with pgid' := X1.t.mv.pgid' })
    rootFree := by
      intro F hF
      have h := s8.1 F (fun id hid => List.mem_append_left _ (hF id hid).1)
        (by rw [hwx]; exact hI.rootFree F hF)
      rw [← hwx]; exact h
    lroot := hI.lroot
    rootExt := (extents_kept hBr hBr' hsr hnsr s3 hfuel).trans hI.rootExt
    notKeys := notKeys_upd hI.notKeys hk
    nilKids := by
      refine nilKids_upd hI ?_ ?_
      · intro c0 C0 hc0 hC0 hn
        rw [hc] at hc0; cases hc0
        rcases hI.nilKids k c C0 hc hC0 hn with h | ⟨-, h⟩
        · rw [hks] at h; cases h
        · exact absurd (h C hC) hnn
      · intro k' c' Cx e hc' _ hCx hn C' hC'
        have hcc : c' ≠ c := by
          intro h; subst h; exact e (hI.inj k' k c' hc' hc)
        obtain ⟨B', hB', hs, -⟩ := hkept c' hcc Cx hCx
        rw [hB'] at hC'; cases hC'; rw [hs.1]; exact hn }

end spilled

end Spill

end bbolt
end EtcdGrove
end Perennial
