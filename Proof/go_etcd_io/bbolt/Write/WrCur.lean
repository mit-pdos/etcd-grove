/-
**The writer's cursor facts kept** (maintainer 16, `notes/bbolt-proof-plan.md`): `wrCurFacts`
(`Model/WrCur`) across the writer's steps that close `boltTx`: `wrCurFacts_congr` (a step that keeps
every bucket's node cache, root position and the root's entries' roots), materializations
(`wrCurFacts_matGrow`), a node's record replaced (`wrCurFacts_setNode`), the open of a top-level
bucket (`wrCurFacts_bktOpened`), and `CreateBucket`'s put (`wrCurFacts_createPost`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WrCur
public import Proof.go_etcd_io.bbolt.Write.MatGrow
public import Proof.go_etcd_io.bbolt.Write.CreateBktPost
public import Proof.go_etcd_io.bbolt.Read.WOpenWOK
public import Proof.go_etcd_io.bbolt.Read.PubWBkt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wrcur
variable [GooseExts]

theorem W64_toNat_self (w : w64) : W64 ((w.toNat : Nat) : Int) = w := by
  apply BitVec.eq_of_toNat_eq; simp

/-- **A step that keeps the registry, the live buckets, every bucket's node cache and root
position, the root's cache, and the root's entries' roots** keeps `wrCurFacts` (`T'`'s `wRoot`
the same; the opened buckets may grow). -/
theorem wrCurFacts_congr (T T' : TxView) (X X' : WX) (hnl : X'.nloc = X.nloc)
    (hlb : X'.liveB = X.liveB)
    (hnm : ∀ b, (X'.t.bs !! b).map BRec.nm = (X.t.bs !! b).map BRec.nm)
    (hrp : ∀ b, X'.rootPid b = X.rootPid b) (hloc : ∀ n, bktLoc X' n = bktLoc X n)
    (hwr : ∀ n, wRoot X'.v T' n = wRoot X.v T n) (hR : ∀ n, rootEntRef X' n = rootEntRef X n)
    (hbo : ∀ b, (X.t.bobjs !! b).isSome → (X'.t.bobjs !! b).isSome)
    (h : wrCurFacts T X) : wrCurFacts T' X' := by
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h
  refine ⟨⟨fun l b p hl hb => ?_, fun b B c l hB hb hc => ?_⟩, fun n b hn => ?_, fun n => ?_,
    fun l b p hl => ?_⟩
  · rw [hnl] at hl; rw [hlb] at hb
    obtain ⟨B, hB, hm⟩ := h1 l b p hl hb
    have e := hnm b
    rw [hB] at e
    cases hB' : X'.t.bs !! b with
    | none => rw [hB'] at e; cases e
    | some B' =>
      rw [hB'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact ⟨B', rfl, by rw [e]; exact hm⟩
  · rw [hnl]; rw [hlb] at hb
    have e := hnm b
    rw [hB] at e
    cases hB0 : X.t.bs !! b with
    | none => rw [hB0] at e; cases e
    | some B0 =>
      rw [hB0] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact h2 b B0 c l hB0 hb (by rw [← e]; exact hc)
  · rw [hrp, hwr]; rw [hloc] at hn; exact h3 n b hn
  · rw [hR, hwr]; exact h4 n
  · rw [hnl] at hl; exact hbo b (h5 l b p hl)

/-- The root's entries kept, the root's entries' roots kept. -/
theorem rootEntRef_of_rootEnts (X X' : WX) (h : rootEnts X' = rootEnts X) (n : GoString) :
    rootEntRef X' n = rootEntRef X n := by
  unfold rootEntRef rootEntVal; rw [h]

/-! ## Materializations -/

/-- **A materialization keeps `wrCurFacts`**: the new node `l` (fresh: no live bucket caches it)
is cached at `pgid` and registered at `(bl, pgid)` together. -/
theorem wrCurFacts_nodeAdded (T : TxView) (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent)
    (hw : wrCurFacts T X) : wrCurFacts T X' := by
  have hf := wOK_matFresh X X' bl l pgid parent hok h hpos
  obtain ⟨hre, hloc, -, hv, -, hrp, -, -⟩ :=
    nodeAdded_facts X X' bl l pgid parent h hf (wOK_inlineLeaf X bl pgid hok)
  obtain ⟨B, pa, pg, r, ns', bv', hB, -, hnm0, -, hlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hX'⟩ := h
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hw
  have hbs : ∀ b, X'.t.bs !! b = if bl = b then
      some ({ B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } : BRec) else X.t.bs !! b := by
    intro b; rw [hX']; simp only [GMap.lookup_insert_eq_iff]
  have hnl : ∀ x, X'.nloc !! x = if l = x then some (bl, pgid.toNat) else X.nloc !! x := by
    intro x; rw [hX']; simp only [GMap.lookup_insert_eq_iff]
  have hlb : X'.liveB = X.liveB := by rw [hX']
  -- a node a live bucket caches is not `l`
  have hne : ∀ b B0 c l0, X.t.bs !! b = some B0 → B0.nm !! c = some l0 → l0 ≠ l := by
    intro b B0 c l0 hB0 hc e
    subst e
    obtain ⟨-, r0, hr0, -⟩ := (wOK_bktClean X hok b B0 hB0).2.2.2.2.1 c l0 hc
    have := objs_isSome_node X.t b B0 l0 hB0 (by simp [hr0])
    rw [hlo'] at this; cases this
  refine ⟨⟨fun l' b p hl hb => ?_, fun b B' c l' hB' hb hc => ?_⟩, fun n b hn => ?_, fun n => ?_,
    fun l' b p hl => ?_⟩
  · rw [hlb] at hb
    rw [hnl] at hl
    split at hl
    · rename_i e; subst e
      cases hl
      refine ⟨_, by rw [hbs, if_pos rfl], ?_⟩
      show (B.nm.insert pgid l) !! W64 ((pgid.toNat : Nat) : Int) = some l
      rw [W64_toNat_self, GMap.lookup_insert]
    · obtain ⟨B0, hB0, hm⟩ := h1 l' b p hl hb
      by_cases e : bl = b
      · subst e
        rw [hB] at hB0; cases hB0
        refine ⟨_, by rw [hbs, if_pos rfl], ?_⟩
        show (B.nm.insert pgid l) !! _ = some l'
        rw [GMap.lookup_insert_eq_iff, if_neg]
        · exact hm
        · intro e; rw [← e, hnm0] at hm; cases hm
      · exact ⟨B0, by rw [hbs, if_neg e]; exact hB0, hm⟩
  · rw [hlb] at hb
    rw [hnl]
    rw [hbs] at hB'
    split at hB'
    · rename_i e; subst e
      cases hB'
      have hc' : (B.nm.insert pgid l) !! c = some l' := hc
      rw [GMap.lookup_insert_eq_iff] at hc'
      split at hc'
      · rename_i e; subst e; cases hc'; rw [if_pos rfl]
      · rw [if_neg (Ne.symm (hne bl B c l' hB hc'))]; exact h2 bl B c l' hB hb hc'
    · rw [if_neg (Ne.symm (hne b B' c l' hB' hc))]; exact h2 b B' c l' hB' hb hc
  · rw [hrp, hv]; rw [hloc] at hn; exact h3 n b hn
  · rw [rootEntRef_of_rootEnts X X' hre, hv]; exact h4 n
  · rw [hnl] at hl
    have hbo : ∀ b, (X.t.bs !! b).isSome → (X'.t.bobjs !! b).isSome := by
      intro b hb
      unfold WTx.bobjs
      rw [GMap.lookup_union, hbs]; split
      · rfl
      · cases e : X.t.bs !! b <;> simp_all
    split at hl
    · cases hl; exact hbo bl (by rw [hB]; rfl)
    · have := h5 l' b p hl
      unfold WTx.bobjs at this ⊢
      cases hb : X.t.bs !! b with
      | some _ => exact hbo b (by rw [hb]; rfl)
      | none =>
        have hd : X'.t.deadB = X.t.deadB := by rw [hX']
        rw [GMap.lookup_union, hb] at this
        rw [GMap.lookup_union, hd]
        cases hb' : X'.t.bs !! b <;> simp_all

/-- **Materializations keep `wrCurFacts`.** -/
theorem wrCurFacts_matGrow (T : TxView) (X X' : WX) (bl : Loc) (hok : wOK X)
    (h : matGrow X X' bl) (hw : wrCurFacts T X) : wrCurFacts T X' := by
  revert hok hw
  induction h with
  | refl => intro _ hw; exact hw
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    intro hok hw
    exact ih (wOK_nodeAdded X Y bl l pgid parent hok hadd hpos)
      (wrCurFacts_nodeAdded T X Y bl l pgid parent hok hadd hpos hw)

/-! ## A node's record replaced -/

/-- **A node's record replaced keeps `wrCurFacts`**, given the root's entries' roots kept (a node of
a bucket other than the root: `rootEnts_setNode_ne`). -/
theorem wrCurFacts_setNode (T T' : TxView) (X : WX) (b l : Loc) (B : BRec) (r' : NRec)
    (hB : X.t.bs !! b = some B) (hwr : ∀ n, wRoot X.v T' n = wRoot X.v T n)
    (hR : ∀ n, rootEntRef (X.setNode b l r') n = rootEntRef X n) (hw : wrCurFacts T X) :
    wrCurFacts T' (X.setNode b l r') := by
  have hX : X.setNode b l r' = X.setBkt b { B with ns := B.ns.insert l r' } := by
    unfold WX.setNode; rw [hB]
  have hbs : ∀ c, (X.setNode b l r').t.bs !! c =
      if b = c then some { B with ns := B.ns.insert l r' } else X.t.bs !! c := by
    intro c; rw [hX]; unfold WX.setBkt; simp only [GMap.lookup_insert_eq_iff]
  have hmap : ∀ {β : Type} (f : BRec → β), (∀ D : BRec, f { D with ns := D.ns.insert l r' } = f D) →
      ∀ c, ((X.setNode b l r').t.bs !! c).map f = (X.t.bs !! c).map f := by
    intro β f hf c
    rw [hbs]; split
    · rename_i e; subst e; rw [hB]; simp only [Option.map_some, hf]
    · rfl
  refine wrCurFacts_congr T T' X _ (by rw [hX]; rfl) (by rw [hX]; rfl)
    (hmap BRec.nm (fun _ => rfl)) (fun c => ?_) (fun n => ?_) (fun n => by rw [hX]; exact hwr n)
    hR (fun c hc => ?_) hw
  · have := hmap (fun D => D.ib.root') (fun _ => rfl) c
    unfold WX.rootPid; rw [this]
  · have hrl : (X.setNode b l r').rl = X.rl := by rw [hX]; rfl
    have := hmap BRec.bm (fun _ => rfl) X.rl
    unfold bktLoc; rw [hrl]
    cases h1 : (X.setNode b l r').t.bs !! X.rl <;> cases h2 : X.t.bs !! X.rl <;>
      rw [h1, h2] at this <;> simp_all
  · unfold WTx.bobjs at hc ⊢
    have hd : (X.setNode b l r').t.deadB = X.t.deadB := by rw [hX]; rfl
    have := hmap (fun _ => ()) (fun _ => rfl) c
    rw [GMap.lookup_union] at hc ⊢; rw [hd]
    cases h1 : (X.setNode b l r').t.bs !! c <;> cases h2 : X.t.bs !! c <;>
      rw [h1, h2] at this <;> simp_all

/-- **A node of a bucket other than the root replaced keeps the root's entries.** -/
theorem rootEnts_setNode_ne (X : WX) (b l : Loc) (B : BRec) (r' : NRec)
    (hB : X.t.bs !! b = some B) (hb : b ≠ X.rl) : rootEnts (X.setNode b l r') = rootEnts X := by
  have hX : X.setNode b l r' = X.setBkt b { B with ns := B.ns.insert l r' } := by
    unfold WX.setNode; rw [hB]
  have hrl : (X.setNode b l r').rl = X.rl := by rw [hX]; rfl
  have hbs : (X.setNode b l r').t.bs !! X.rl = X.t.bs !! X.rl := by
    rw [hX]; unfold WX.setBkt; simp only [GMap.lookup_insert_eq_iff, if_neg hb]
  have hv : (X.setNode b l r').v = X.v := by rw [hX]; rfl
  have hfuel : (X.setNode b l r').fuel = X.fuel := by
    rw [hX]; unfold WX.fuel WX.setBkt; simp only
    rw [GMap.map_size_insert_Some _ _ _ _ hB]
  have hlt : ∀ q, ltree (X.setNode b l r') X.rl q = ltree X X.rl q := by
    intro q; unfold ltree; rw [hbs, hv]
  have hrp : (X.setNode b l r').rootPid X.rl = X.rootPid X.rl := by
    unfold WX.rootPid; rw [hbs]
  unfold rootEnts WX.leaves
  rw [hrl, hfuel, hrp, WOpen.lleaves_congr' _ _ X.rl hlt]

end wrcur

end Write

end bbolt
end EtcdGrove
end Perennial
