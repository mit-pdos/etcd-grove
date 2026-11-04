/-
The spill's pure tree facts (U9e, `notes/bbolt-proof-plan.md`): **an unspilled tree outside a
spill's touched nodes is kept** (`uTree_frame`): through a spill step's frame (`spFrame`: the
untouched nodes as before, modulo sources), in a page map agreeing on its slots, below a higher
mark. What the siblings of a spilled child keep (`node.spill`'s loop), and what `dereference` and
a remap keep (`Spill/UTreeStep`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Spill.STreeAgree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section frame
variable [GooseExts]

/-! ## Entries by data -/

theorem wKey_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    wKey ws' = wKey ws := by
  funext i
  have e := congrArg (fun l => (l[i]?).map fun d => d.2.2.1) h
  simp only [List.getElem?_map, Option.map_map] at e
  unfold wKey
  have : ∀ o : Option WEntry, o.map WEntry.key = o.map ((fun d => d.2.2.1) ∘ wDat) := by
    intro o; cases o <;> rfl
  rw [this, this, e]

theorem length_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    ws'.length = ws.length := by
  have := congrArg List.length h; simpa using this

theorem get_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) {i : Nat}
    {w' : WEntry} (hw : ws'[i]? = some w') : ∃ w, ws[i]? = some w ∧ wDat w' = wDat w := by
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, hw, Option.map_some] at e
  cases hx : ws[i]? with
  | none => rw [hx] at e; cases e
  | some w => rw [hx] at e; exact ⟨w, rfl, Option.some.inj e⟩

theorem mem_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) {w' : WEntry}
    (hw : w' ∈ ws') : ∃ w ∈ ws, wDat w' = wDat w := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  obtain ⟨w, hw, he⟩ := get_of_dat h (List.getElem?_eq_getElem hi)
  exact ⟨w, List.mem_of_getElem? hw, he⟩

theorem wsSorted_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat)
    (hs : wsSorted ws) : wsSorted ws' := by
  intro i j hij hj
  rw [wKey_of_dat h]
  exact hs i j hij (by rw [← length_of_dat h]; exact hj)

theorem wDat_key {w w' : WEntry} (h : wDat w' = wDat w) : w'.key = w.key :=
  congrArg (fun d => d.2.2.1) h

theorem wDat_pgid {w w' : WEntry} (h : wDat w' = wDat w) : w'.pgid = w.pgid :=
  congrArg (fun d => d.2.1) h

theorem wDat_flags {w w' : WEntry} (h : wDat w' = wDat w) : w'.flags = w.flags :=
  congrArg (fun d => d.1) h

theorem wDat_value {w w' : WEntry} (h : wDat w' = wDat w) : w'.value = w.value :=
  congrArg (fun d => d.2.2.2) h

/-- Entries equal by data have the same leaf elements. -/
theorem wEl_of_dat {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    ws'.map wEl = ws.map wEl := by
  have : ws'.map wEl = (ws'.map wDat).map (fun d => (d.1.toNat, d.2.2.1, d.2.2.2)) := by
    rw [List.map_map]; rfl
  rw [this, h, List.map_map]; rfl

/-! ## Records modulo sources -/

theorem nodeSim_pgid {r r' : NRec} (h : nodeSim r r') : r'.nv.pgid' = r.nv.pgid' := by
  rw [h.1]

theorem nodeSim_isLeaf {r r' : NRec} (h : nodeSim r r') : r'.nv.isLeaf' = r.nv.isLeaf' := by
  rw [h.1]

theorem nodeSim_spilled {r r' : NRec} (h : nodeSim r r') : r'.nv.spilled' = r.nv.spilled' := by
  rw [h.1]

theorem nodeSim_bucket {r r' : NRec} (h : nodeSim r r') : r'.nv.bucket' = r.nv.bucket' := by
  rw [h.1]

theorem nodeSim_parent {r r' : NRec} (h : nodeSim r r') : r'.nv.parent' = r.nv.parent' := by
  rw [h.1]

/-- An untouched node of `bl` through the frame. -/
theorem spFrame_node {X X' : WX} {bl : Loc} {T : List Loc} (hfr : spFrame X X' bl T) {l : Loc}
    {r : NRec} (hr : X.node bl l = some r) (hl : l ∉ T) :
    ∃ r', X'.node bl l = some r' ∧ nodeSim r r' ∧ (l ∈ X'.live ↔ l ∈ X.live) := by
  unfold WX.node at hr
  cases hb : X.t.bs !! bl with
  | none => rw [hb] at hr; cases hr
  | some B =>
    rw [hb] at hr
    simp only [Option.bind_some] at hr
    obtain ⟨B', hb', -, hns⟩ := hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B hb
    have hsim := hns l hl
    rw [hr] at hsim
    cases hr' : B'.ns !! l with
    | none => rw [hr'] at hsim; exact absurd hsim id
    | some r' =>
      rw [hr'] at hsim
      refine ⟨r', by unfold WX.node; rw [hb']; exact hr', hsim, ?_⟩
      exact hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l hl ⟨bl, B, hb, by rw [hr]; rfl⟩

theorem uNode_frame {X X' : WX} {bl : Loc} {T : List Loc} (hfr : spFrame X X' bl T) {n : Loc}
    {r r' : NRec} {lo hi : Option (List w8)} (hu : uNode X bl n r lo hi) (hs : nodeSim r r')
    (hl : n ∈ X'.live ↔ n ∈ X.live) : uNode X' bl n r' lo hi := by
  obtain ⟨hlive, hb, hsp, hcap, hlen, hsort, hent, hown⟩ := hu
  refine ⟨hl.2 hlive, by rw [nodeSim_bucket hs]; exact hb, by rw [nodeSim_spilled hs]; exact hsp,
    by rw [hs.2.2.2.2.2.2]; exact hcap, by rw [hs.2.2.2.1, length_of_dat hs.2.2.1]; exact hlen,
    wsSorted_of_dat hs.2.2.1 hsort, fun w' hw' => ?_, ?_⟩
  · obtain ⟨w, hw, he⟩ := mem_of_dat hs.2.2.1 hw'
    rw [wDat_key he, wDat_value he]; exact hent w hw
  · unfold ownPg at hown ⊢; rw [nodeSim_pgid hs, hfr.2.2.2.2.1]; exact hown

theorem spilledN_frame {X X' : WX} {bl : Loc} {T : List Loc} (hfr : spFrame X X' bl T) {c : Loc}
    (hc : spilledN X bl c) (hcT : c ∉ T) : spilledN X' bl c := by
  obtain ⟨hl, rc, hrc, hb, hsp, hcs⟩ := hc
  obtain ⟨rc', hrc', hs, hl'⟩ := spFrame_node hfr hrc hcT
  exact ⟨hl'.2 hl, rc', hrc', by rw [nodeSim_bucket hs]; exact hb,
    by rw [nodeSim_spilled hs]; exact hsp, by rw [hs.2.2.2.2.1]; exact hcs⟩

/-! ## Slots -/

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem mem_pgSlots_self {P : Pages} {S : List Nat} {x : Nat} (hx : x ∈ S) : x ∈ pgSlots P S := by
  unfold pgSlots
  refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
  cases P !! x with
  | none => simp
  | some pg => exact List.mem_range'_1.2 ⟨Nat.le_refl _, by omega⟩

theorem pgSlots_congr {P P' : Pages} {S : List Nat} (h : ∀ x ∈ S, P' !! x = P !! x) :
    pgSlots P' S = pgSlots P S := by
  unfold pgSlots
  apply flatMap_congr'
  intro x hx
  rw [h x hx]

theorem ownSl_congr {v v' : View} (h : v'.pages = v.pages) (p : w64) : ownSl v' p = ownSl v p := by
  unfold ownSl; rw [h]

theorem uTree_head {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {lo hi h F D N E}
    (hu : uTree X bl P hwm n lo hi h F D N E) : n ∈ N := by
  cases hu <;> simp

/-- **A written tree's leaf elements depend only on its pages.** (U9h: stated, not yet proved;
`treeLeaves`' fuel is the page map's size, so the proof shows the walk's result independent of
the fuel past the tree's height.) -/
theorem treeEls_agree {P P' : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) (hag : ∀ x ∈ S, P' !! x = P !! x) :
    treeEls P' id = treeEls P id := by
  sorry

theorem fTree_agree {P P' : Pages} {hwm hwm' id : Nat} {k : List w8} {hi : Option (List w8)}
    {h : Nat} {S : List Nat} {E : List El} (hag : ∀ x ∈ pgSlots P S, P' !! x = P !! x)
    (hh : hwm ≤ hwm') (hf : fTree P hwm id k hi h S E) :
    fTree P' hwm' id k hi h S E ∧ pgSlots P' S = pgSlots P S := by
  have hagS : ∀ x ∈ S, P' !! x = P !! x := fun x hx => hag x (mem_pgSlots_self hx)
  refine ⟨⟨sTree_agree hagS hh hf.1, ?_, by rw [treeEls_agree hf.1 hagS]; exact hf.2.2⟩,
    pgSlots_congr hagS⟩
  obtain ⟨pg, hpg, h1, h2⟩ := hf.2.1
  have hid : id ∈ S := (hf.1.has id).1 (treeHas.root id pg hpg)
  exact ⟨pg, by rw [hagS id hid]; exact hpg, h1, h2⟩

/-! ## The frame -/

/-- **An unspilled tree outside the touched nodes is kept** (see the module doc). -/
theorem uTree_frame {X X' : WX} {bl : Loc} {P P' : Pages} {hwm hwm' : Nat} {T : List Loc}
    (hfr : spFrame X X' bl T) (hh : hwm ≤ hwm') {n : Loc} {lo hi : Option (List w8)} {h : Nat}
    {F D : List Nat} {N : List Loc} {E : List El} (hu : uTree X bl P hwm n lo hi h F D N E) :
    (∀ x ∈ D, P' !! x = P !! x) → (∀ l ∈ T, l ∉ N ∧ ¬ spilledN X bl l) →
      uTree X' bl P' hwm' n lo hi h F D N E :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun n lo hi h F D N E _ => (∀ x ∈ D, P' !! x = P !! x) →
      (∀ l ∈ T, l ∉ N ∧ ¬ spilledN X bl l) → uTree X' bl P' hwm' n lo hi h F D N E)
    (motive_2 := fun n lo hi ws cs h i w e _ => ∀ (ws' : List WEntry) (w' : WEntry),
      ws'.map wDat = ws.map wDat → wDat w' = wDat w →
      (∀ x ∈ e.D, P' !! x = P !! x) → (∀ l ∈ T, l ∉ e.N ∧ ¬ spilledN X bl l) →
      uEnt X' bl P' hwm' n lo hi ws' cs h i w' e)
    (fun n r lo hi Sb hr hun hleaf hcs hbv hb0 hP hT => by
      have hnT : n ∉ T := fun hm => (hT n hm).1 (List.mem_singleton_self n)
      obtain ⟨r', hr', hs, hl⟩ := spFrame_node hfr hr hnT
      have hD : ∀ i, i < r.ws.length → ∀ x ∈ Sb i, P' !! x = P !! x := by
        intro i hi x hx
        refine hP x (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩))
        exact mem_pgSlots_self hx
      have H := uTree.leaf (X := X') (bl := bl) (P := P') (hwm := hwm') n r' lo hi Sb hr'
        (uNode_frame hfr hun hs hl) (by rw [nodeSim_isLeaf hs]; exact hleaf)
        (by rw [hs.2.2.2.2.1]; exact hcs)
        (fun i w' hw' hf => by
          obtain ⟨w, hw, he⟩ := get_of_dat hs.2.2.1 hw'
          rw [wDat_value he]
          have hi : i < r.ws.length := (List.getElem?_eq_some_iff.1 hw).1
          exact bvalS_agree (hD i hi) hh (hbv i w hw (by rw [← wDat_flags he]; exact hf)))
        (fun i w' hw' hf => by
          obtain ⟨w, hw, he⟩ := get_of_dat hs.2.2.1 hw'
          exact hb0 i w hw (by rw [← wDat_flags he]; exact hf))
      rw [nodeSim_pgid hs, ownSl_congr hfr.2.2.2.2.1, length_of_dat hs.2.2.1,
        wEl_of_dat hs.2.2.1] at H
      have e : ((List.range r.ws.length).flatMap fun i => pgSlots P' (Sb i)) =
          (List.range r.ws.length).flatMap fun i => pgSlots P (Sb i) := by
        apply flatMap_congr'
        intro i hi
        exact pgSlots_congr (hD i (List.mem_range.1 hi))
      rw [e] at H
      exact H)
    (fun n r lo hi h es hr hun hleaf h2 hlen hent hchnd hcs hcsnd hNnd hpg0 ih hP hT => by
      have hnT : n ∉ T := fun hm => (hT n hm).1 (List.mem_cons_self ..)
      obtain ⟨r', hr', hs, hl⟩ := spFrame_node hfr hr hnT
      have hlen' := length_of_dat hs.2.2.1
      have H := uTree.branch (X := X') (bl := bl) (P := P') (hwm := hwm') n r' lo hi h es hr'
        (uNode_frame hfr hun hs hl) (by rw [nodeSim_isLeaf hs]; exact hleaf)
        (by rw [hlen']; exact h2) (by rw [hlen']; exact hlen)
        (fun i w' e hw' he => by
          obtain ⟨w, hw, hwe⟩ := get_of_dat hs.2.2.1 hw'
          rw [hs.2.2.2.2.1]
          have hm : e ∈ es := List.mem_of_getElem? he
          refine ih i w e hw he r'.ws w' hs.2.2.1 hwe (fun x hx => hP x ?_) (fun l hlT => ?_)
          · exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, hm, hx⟩)
          · refine ⟨fun hn => (hT l hlT).1 ?_, (hT l hlT).2⟩
            exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨e, hm, hn⟩))
        hchnd
        (fun c hc => by
          rw [hs.2.2.2.2.1] at hc
          rcases hcs c hc with h' | h'
          · exact Or.inl h'
          · refine Or.inr (spilledN_frame hfr h' fun hcT => (hT c hcT).2 h'))
        (by rw [hs.2.2.2.2.1]; exact hcsnd) hNnd
        (fun h0 => hpg0 (by rw [← nodeSim_pgid hs]; exact h0))
      rw [nodeSim_pgid hs, ownSl_congr hfr.2.2.2.2.1] at H
      exact H)
    (fun n lo hi ws cs h i w c rc F D N E hc hrc hpar hpg hkey hk' hut ih ws' w' hws hw hP hT => by
      have hcT : c ∉ T := fun hm => (hT c hm).1 (uTree_head hut)
      obtain ⟨rc', hrc', hs, -⟩ := spFrame_node hfr hrc hcT
      have H := ih hP hT
      rw [← wKey_of_dat hws, ← length_of_dat hws] at H
      refine uEnt.child n lo hi ws' cs h i w' c rc' F D N E hc hrc'
        (by rw [nodeSim_parent hs]; exact hpar) (by rw [nodeSim_pgid hs, wDat_pgid hw]; exact hpg)
        (by rw [hs.2.2.2.2.2.1, wDat_key hw]; exact hkey)
        (fun h0 => hk' (hs.2.1.1 h0)) H)
    (fun n lo hi ws cs h i w S E hf ws' w' hws hw hP _ => by
      obtain ⟨hf', he⟩ := fTree_agree hP hh hf
      have H := uEnt.fin (X := X') (bl := bl) (P := P') (hwm := hwm') n lo hi ws' cs h i w' S E
        (by rw [wDat_pgid hw, wDat_key hw, wKey_of_dat hws, length_of_dat hws]; exact hf')
      rw [he] at H
      exact H)
    hu

/-! ## After the children's loop -/

/-- An unspilled node is not a spilled one. -/
theorem uTree_not_spilled {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {c : Loc} {lo hi h F D N E}
    (hu : uTree X bl P hwm c lo hi h F D N E) : ¬ spilledN X bl c := by
  intro ⟨_, rc, hrc, _, hsp, _⟩
  cases hu with
  | leaf _ r _ _ _ hr hun =>
    rw [hr] at hrc; cases hrc; rw [hun.2.2.1] at hsp; cases hsp
  | branch _ r _ _ _ _ hr hun =>
    rw [hr] at hrc; cases hrc; rw [hun.2.2.1] at hsp; cases hsp

/-- **Every entry finished** once every child is spilled (`node.spill`'s children's loop done):
each entry's descriptor is a finished subtree's. -/
theorem uEnt_fin_of_spilled {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {ws : List WEntry} {cs : List Loc} {h i : Nat} {w : WEntry}
    {e : UE} (he : uEnt X bl P hwm n lo hi ws cs h i w e) (hcs : ∀ c ∈ cs, spilledN X bl c) :
    ∃ S E, e = ⟨none, [], pgSlots P S, [], E⟩ ∧
      fTree P hwm w.pgid.toNat w.key (childHi hi (wKey ws) ws.length i) h S E := by
  cases he with
  | child _ _ _ _ _ _ _ _ c rc F D N E hc _ _ _ _ _ hut =>
    exact absurd (hcs c hc) (uTree_not_spilled hut)
  | fin _ _ _ _ _ _ _ _ S E hf => exact ⟨S, E, rfl, hf⟩

end frame

end Spill

end bbolt
end EtcdGrove
end Perennial
