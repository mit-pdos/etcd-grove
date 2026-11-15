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
public import Proof.go_etcd_io.bbolt.Txn.WInit

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

/-! ## The open of a top-level bucket -/

theorem mem_rootEnts_of (X : WX) (w : WEntry) (hw : w ∈ X.allEnts X.rl) (hf : isBktFlag w.flags) :
    (w.key, w.value) ∈ rootEnts X := by
  unfold rootEnts
  unfold WX.allEnts at hw
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_flatten] at hw ⊢
  obtain ⟨ws, hws, hw⟩ := hw
  exact ⟨ws, hws, w, hw, by simp [hf]⟩

/-- **The root's entry of a bucket entry's name is its value** (the root's keys are distinct). -/
theorem rootEntVal_of_mem (X : WX) (hok : wOK X) (R : BRec) (hR : X.t.bs !! X.rl = some R)
    (w : WEntry) (hw : w ∈ X.allEnts X.rl) (hf : isBktFlag w.flags) :
    rootEntVal X w.key = some w.value := by
  unfold rootEntVal
  cases h : (rootEnts X).find? (fun e => decide (e.1 = w.key)) with
  | none =>
    have := List.find?_eq_none.1 h _ (mem_rootEnts_of X w hw hf)
    simp at this
  | some e =>
    have hm := List.mem_of_find?_eq_some h
    have he := List.find?_some h
    simp only [decide_eq_true_eq] at he
    obtain ⟨w', hw', -, hk', hv'⟩ := PubW.mem_rootEnts X e.1 e.2 hm
    have := WOpen.allEnts_key_inj X hok X.rl R hR w' w hw' hw (hk'.trans he)
    subst this
    simp [hv']

/-- **The open of a top-level bucket keeps `wrCurFacts`**: the new bucket (at a location no
registered node names) caches nothing, its root is its entry's (`wRoot`, by the root entries'
roots), and the root's entries are kept. -/
theorem wrCurFacts_bktOpened (T : TxView) (X X' : WX) (c : Loc) (name : List w8) (g : Nat)
    (hop : bktOpened X X' X.rl c name g) (hok : wOK X) (hw : wrCurFacts T X) :
    wrCurFacts T X' := by
  obtain ⟨B, C, w, hB, hwm, hk, hf, hbm, -, hcfresh, hCib, -, -, hCnm, -, -, -, -, hX'⟩ := hop
  have hc : X.t.bs !! c = none := by
    cases e : X.t.bs !! c with
    | none => rfl
    | some D =>
      have := bobjs_bkt X.t c D e
      rw [Option.isNone_iff_eq_none] at hcfresh; rw [hcfresh] at this; cases this
  have hcrl : c ≠ X.rl := by intro e; rw [e, hB] at hc; cases hc
  have hlk : ∀ d, X'.t.bs !! d =
      if c = d then some C else if X.rl = d then some { B with bm := B.bm.insert name c }
      else X.t.bs !! d := by
    intro d; rw [hX']; simp only [GMap.lookup_insert_eq_iff]
  have hrl' : X'.rl = X.rl := by rw [hX']
  have hv' : X'.v = X.v := by rw [hX']
  have hnl : X'.nloc = X.nloc := by rw [hX']
  have hlb : X'.liveB = X.liveB.insert c () := by rw [hX']
  have hXO : X' = WOpen.XO X X.rl c B C name (name, g) := by rw [hX']; rfl
  have hre : rootEnts X' = rootEnts X := by
    have hlv : X'.leaves X.rl = X.leaves X.rl := by
      rw [hXO]; exact WOpen.XO_leaves_old X X.rl c B C name (name, g) hB hc hbm hok X.rl
        (Ne.symm hcrl)
    unfold rootEnts; rw [hrl', hlv]
  have hrlB : X.rl ∈ X.liveB := hok.2.2.2.2.2.1.1
  have hlv' : ∀ d, c ≠ d → d ∈ X'.liveB → d ∈ X.liveB := by
    intro d hd h
    rw [hlb, GMap.mem_iff, GMap.lookup_insert_eq_iff, if_neg hd] at h
    exact h
  have hbo : ∀ d, (X.t.bobjs !! d).isSome → (X'.t.bobjs !! d).isSome := by
    intro d hd
    have hdd : X'.t.deadB = X.t.deadB := by rw [hX']
    unfold WTx.bobjs at hd ⊢
    rw [GMap.lookup_union] at hd ⊢; rw [hlk, hdd]
    split
    · rfl
    · split
      · rfl
      · exact hd
  have hloc : ∀ n, bktLoc X' n = if name = n then some c else bktLoc X n := by
    intro n
    unfold bktLoc
    rw [hrl', hlk, if_neg hcrl, if_pos rfl, hB]
    simp only [Option.bind_some, GMap.lookup_insert_eq_iff]
  have hrp : ∀ d, c ≠ d → X'.rootPid d = X.rootPid d := by
    intro d hd
    unfold WX.rootPid
    rw [hlk, if_neg hd]
    split
    · rename_i e; subst e; rw [hB]; rfl
    · rfl
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hw
  refine ⟨⟨fun l b p hl hb => ?_, fun b B' cc l hB' hb hcc => ?_⟩, fun n b hn => ?_, fun n => ?_,
    fun l b p hl => ?_⟩
  · rw [hnl] at hl
    have hcb : c ≠ b := by
      intro e; subst e
      have := h5 l c p hl
      rw [Option.isNone_iff_eq_none] at hcfresh; rw [hcfresh] at this; cases this
    obtain ⟨B0, hB0, hm⟩ := h1 l b p hl (hlv' b hcb hb)
    rw [hlk, if_neg hcb]
    split
    · rename_i e; subst e; rw [hB] at hB0; cases hB0; exact ⟨_, rfl, hm⟩
    · exact ⟨B0, hB0, hm⟩
  · rw [hnl]
    rw [hlk] at hB'
    split at hB'
    · cases hB'; rw [hCnm] at hcc; simp at hcc
    · rename_i hcb
      split at hB'
      · rename_i e; subst e; cases hB'
        exact h2 X.rl B cc l hB hrlB hcc
      · exact h2 b B' cc l hB' (hlv' b hcb hb) hcc
  · rw [hloc] at hn
    rw [hv']
    split at hn
    · rename_i e; subst e; cases hn
      have hpc : X'.rootPid c = C.ib.root' := by
        unfold WX.rootPid; rw [hlk, if_pos rfl]; rfl
      rw [hpc, hCib, ← hk, ← h4 w.key]
      unfold rootEntRef
      rw [rootEntVal_of_mem X hok B hB w hwm hf]
      rfl
    · obtain ⟨D, v, hD, -⟩ := (hok.2.1 X.rl B hB).2 n b (by unfold bktLoc at hn; rw [hB] at hn; exact hn)
      have hcb : c ≠ b := by intro e; subst e; rw [hc] at hD; cases hD
      rw [hrp b hcb]; exact h3 n b hn
  · rw [rootEntRef_of_rootEnts X X' hre, hv']; exact h4 n
  · rw [hnl] at hl; exact hbo b (h5 l b p hl)

/-! ## `CreateBucket`'s put -/

/-- A node record replaced: the root's entries are `withWs`'s (the same leaf flag). -/
theorem rootEnts_setNode_withWs (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r'.nv.isLeaf' = r.nv.isLeaf') :
    rootEnts (X.setNode bl l r') = rootEnts (X.withWs bl l r'.ws) := by
  have hS : (X.setNode bl l r').t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l r' } := by
    unfold WX.setNode WX.setBkt; rw [hB]
  have hv : (X.setNode bl l r').v = X.v := by unfold WX.setNode WX.setBkt; rw [hB]
  have hrl1 : (X.setNode bl l r').rl = X.rl := by unfold WX.setNode WX.setBkt; rw [hB]
  have hf : (X.setNode bl l r').fuel = (X.withWs bl l r'.ws).fuel := by
    rw [withWs_fuel X bl l r'.ws B r hB hr]
    unfold WX.fuel
    rw [hS, GMap.map_size_insert_Some _ _ _ _ hB, hv]
  have hp : (X.setNode bl l r').rootPid X.rl = (X.withWs bl l r'.ws).rootPid X.rl := by
    rw [withWs_rootPid X bl l r'.ws B r hB hr]
    unfold WX.rootPid
    rw [hS]
    by_cases hc : X.rl = bl
    · rw [hc, GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)]
  unfold rootEnts WX.leaves
  rw [hrl1, show (X.withWs bl l r'.ws).rl = X.rl from rfl, hf, hp,
    ltree_setNode_eq X bl l B r r' hB hr hlf]

/-- **`CreateBucket`'s put keeps `wrCurFacts`** (with `createPost`'s premises): the new entry is
inline (root `0`) and its name had no entry (root `0` too). -/
theorem wrCurFacts_createPost (T : TxView) (X X3 : WX) (kb : List w8) (ib : InBucket) (l : Loc)
    (B3 : BRec) (rl : NRec) (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hcur : T.cur = wtxData X)
    (hmg : matGrow X X3 X.rl) (hok3 : wOK X3)
    (hB3 : X3.t.bs !! X.rl = some B3) (hrl : B3.ns !! l = some rl) (hlf : leafFor X3 X.rl kb l)
    (hnew : T.cur !! kb = none) (h0 : ib.root' = W64 0) (hwc : wrCurFacts T X) :
    wrCurFacts T (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) := by
  have hw3 := wrCurFacts_matGrow T X X3 X.rl hok hmg hwc
  have k2 := (matGrow_keepW hmg).2.1
  obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, hbk, hkin⟩ := id hlf
  rw [hB3] at hB0; cases hB0; rw [hrl] at hr0; cases hr0
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X3 hok3 X.rl B3 hB3).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  have hput : wsPutAt rl.ws kb (createEnt kb ib) = wsPut rl.ws (createEnt kb ib) :=
    wsPutAt_wsPut rl.ws (createEnt kb ib) hpw
  have hdata3 : wtxData X3 = wtxData X := wtxData_matGrow X X3 X.rl hok hmg
  have hnone3 := rootEnts_none X3 kb (by rw [hdata3, ← hcur]; exact hnew)
  have hB3' : X3.t.bs !! X3.rl = some B3 := by rw [k2]; exact hB3
  have hre : rootEnts (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) =
      rootEnts (X3.withWs X3.rl l (wsPut rl.ws (createEnt kb ib))) := by
    rw [rootEnts_setNode_withWs X3 X.rl l B3 rl
      (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib))) hB3 hrl rfl, k2]
    show rootEnts (X3.withWs X.rl l (wsPutAt rl.ws kb (createEnt kb ib))) = _
    rw [hput]
  have hval3 : (rootEnts X3).find? (fun x => decide (x.1 = kb)) = none := by
    cases h : (rootEnts X3).find? (fun x => decide (x.1 = kb)) with
    | none => rfl
    | some x =>
      have hm := List.mem_of_find?_eq_some h
      have he := List.find?_some h
      simp only [decide_eq_true_eq] at he
      exact absurd (he ▸ hm) (hnone3 x.2)
  refine wrCurFacts_setNode T T X3 X.rl l B3 _ hB3 (fun _ => rfl) (fun n => ?_) hw3
  unfold rootEntRef rootEntVal
  rw [hre]
  by_cases hn : n = kb
  · rw [hn, hval3]
    obtain ⟨hA, hBm⟩ := rootEnts_key_eq X3 l B3 rl bnd (createEnt kb ib) hok3 hB3' hrl hlf0 hbk
      hkin (createEnt_flag kb ib)
    cases h : (rootEnts (X3.withWs X3.rl l (wsPut rl.ws (createEnt kb ib)))).find?
        (fun x => decide (x.1 = kb)) with
    | none =>
      have := List.find?_eq_none.1 h _ hBm
      simp [createEnt] at this
    | some x =>
      have hm := List.mem_of_find?_eq_some h
      have he := List.find?_some h
      simp only [decide_eq_true_eq] at he
      have hx := hA x hm he
      rw [hx]
      exact emptyBktVal_root ib h0
  · have hp : ∀ x : GoString × List w8, decide (x.1 = n) = true →
        decide (x.1 ≠ (createEnt kb ib).key) = true := by
      intro x hx; simp only [decide_eq_true_eq] at hx ⊢; rw [hx]; exact hn
    rw [find?_filter_of_imp _ _ hp, rootEnts_filter_ne X3 l B3 rl bnd (createEnt kb ib) hok3 hB3'
      hrl hlf0 hbk hkin, ← find?_filter_of_imp _ _ hp]

/-! ## `beginRWTx` -/

/-- **The initial records' `wrCurFacts`** (generation `0` everywhere): no node registered, nothing
opened, the root's entries the view's. -/
theorem wrCurFacts_wx0 (T : TxView) (C : CommitSt) (b rl : Loc) (t : Tx) (mv : Meta)
    (bv : go_etcd_io.bbolt.Bucket) (ib : InBucket) (htree : treeOK C) (hi : Init0 C t mv bv ib)
    (hgen : ∀ n, T.gen n = 0) : wrCurFacts T (wx0 rl t mv bv ib (View.ofC b C)) := by
  refine ⟨⟨fun l b p hl _ => ?_, fun b' B c l hB _ hc => ?_⟩, fun n b' hn => ?_, fun n => ?_,
    fun l b p hl => ?_⟩
  · simp [wx0] at hl
  · obtain ⟨-, rfl⟩ := wx0_bs_some rl t mv bv ib _ b' B hB
    simp [brec0] at hc
  · unfold bktLoc at hn
    rw [wx0_bs] at hn
    simp [brec0, wx0] at hn
  · unfold wRoot rootEntRef rootEntVal baseRoot baseVal
    rw [if_pos (hgen n), rootEnts_wx0 C b rl t mv bv ib htree hi]
    rfl
  · simp [wx0] at hl

/-! ## For the closers -/

/-- `wrCurFacts` reads only the view's generations (`Put`'s `T.setBkt`, ...). -/
theorem wrCurFacts_gen (T T' : TxView) (X : WX) (hg : T'.gen = T.gen) (h : wrCurFacts T X) :
    wrCurFacts T' X := by
  have e : ∀ n, wRoot X.v T' n = wRoot X.v T n := fun n => by unfold wRoot; rw [hg]
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, fun n b hn => (e n).symm ▸ h2 n b hn, fun n => (e n).symm ▸ h3 n, h4⟩

/-- **`Put`'s and `Delete`'s records** (materializations in the handle's bucket `b`, not the root,
then its leaf's record replaced) keep `wrCurFacts`. -/
theorem wrCurFacts_leafStep (T T' : TxView) (X X3 : WX) (b l : Loc) (B3 : BRec) (r' : NRec)
    (hok : wOK X) (hmg : matGrow X X3 b) (hB3 : X3.t.bs !! b = some B3) (hb : b ≠ X.rl)
    (hg : T'.gen = T.gen) (hw : wrCurFacts T X) : wrCurFacts T' (X3.setNode b l r') := by
  have hw3 := wrCurFacts_matGrow T X X3 b hok hmg hw
  have hb3 : b ≠ X3.rl := by rw [(matGrow_keepW hmg).2.1]; exact hb
  refine wrCurFacts_setNode T T' X3 b l B3 r' hB3 (fun n => by unfold wRoot; rw [hg])
    (fun n => rootEntRef_of_rootEnts _ _ (rootEnts_setNode_ne X3 b l B3 r' hB3 hb3) n) hw3

end wrcur

end Write

end bbolt
end EtcdGrove
end Perennial
