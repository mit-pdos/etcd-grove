/-
`Bucket.spill`'s root loop (U9q, `notes/bbolt-proof-plan.md`): **the invariant's steps**, pure
(statements; proofs to come). At the `i`-th key `k` (child `c`, record `C`, not visited):

- `rinv_bkPre`: `child.spill()`'s pre, the other children's and the root's slots as `O`;
- `rinv_nil`: no root node, `continue` (`nilc`);
- `rinv_spilled`: after `child.spill()`, the header of its new tree as the staged value;
- `rinv_freePre`/`rinv_inline`: `child.free()`'s premise, and after it and `child.write()` the
  inline value as the staged value;
- `rinv_entry`, `rinv_ready`, `rinv_putPre`, `rinv_put`: the root bucket's search for `k`
  (`seek`, `Cursor.node`), and the staged value put into its leaf.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureStart
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureFree
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPurePut
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureSpilled
public import Proof.go_etcd_io.bbolt.Spill.Inlineable
public import Proof.go_etcd_io.bbolt.Spill.PageBuf
public import Proof.go_etcd_io.bbolt.Spill.BktValKey
public import Proof.go_etcd_io.bbolt.Spill.BktPm
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureRPut
public import Proof.go_etcd_io.bbolt.Spill.BktInlineVal
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureInline

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section step
variable [GooseExts]

variable {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString} {Lroot : List Nat}
  {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}

theorem rinv_todo (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    (hks : ks k = .todo) (hc : B0.bm !! k = some c) : childTodo X0 X w w0.wtxid c (Dc k) := by
  have h := hI.kids k c hc
  rw [hks] at h
  exact h

theorem getElem?_inj_nodup {α : Type} {l : List α} (hnd : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', -⟩ := List.getElem?_eq_some_iff.1 hi
  exact hnd.eq_of_getElem?_eq hi' (hi.trans hj.symm)

/-- **The next key's state**: the `i`-th key visited (`s`, neither `todo` nor staged). -/
theorem ksAt_step {keys : List GoString} {i : Nat} {ks : GoString → KSt} (hnd : keys.Nodup)
    (h : ksAt keys i ks) {k : GoString} (hk : keys[i]? = some k) (s : KSt)
    (hs : s ≠ .todo ∧ ∀ v, s ≠ .val v false) : ksAt keys (i + 1) (upd ks k s) := by
  intro j k' hj
  unfold upd
  by_cases e : k' = k
  · subst e
    have hij := getElem?_inj_nodup hnd hj hk
    subst hij
    rw [if_pos rfl]
    exact ⟨fun _ => hs, fun h => absurd h (by omega)⟩
  · rw [if_neg e]
    have hne : j ≠ i := by
      intro hji; subst hji; rw [hk] at hj; cases hj; exact e rfl
    obtain ⟨h1, h2⟩ := h j k' hj
    exact ⟨fun hl => h1 (by omega), fun hl => h2 (by omega)⟩

/-- The `i`-th key's state before its visit. -/
theorem ksAt_todo {keys : List GoString} {i : Nat} {ks : GoString → KSt} (h : ksAt keys i ks)
    {k : GoString} (hk : keys[i]? = some k) : ks k = .todo :=
  (h i k hk).2 (Nat.le_refl _)

/-- A staged state's key, then put. -/
theorem upd_upd {β : Type} (f : GoString → β) (k : GoString) (b b' : β) :
    upd (upd f k b) k b' = upd f k b' := by
  funext k'; unfold upd; by_cases e : k' = k <;> simp [e]

/-- A searchable bucket's nodes' parent pointers (`nodeClean`'s last clause; U9x5's
`BktEnd.parOK_of_local`, repeated here for `rinv_bkPre`). -/
theorem parOK_of_bktLocal {X : WX} {bl : Loc} (h : bktLocalOK X bl) : parOK X bl := by
  obtain ⟨-, B, hB, hcl, -⟩ := h
  intro m rm hm _ c hc
  unfold WX.node at hm ⊢
  rw [hB] at hm ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17⟩ := hcl.2.2.2.2.2.2.2.1 m rm hm
  exact h17 c hc

/-- **`child.spill()`'s pre.** -/
theorem rinv_bkPre (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hnd : keys.Nodup)
    {k : GoString} {c : Loc} {C : BRec} (hk : k ∈ keys) (hks : ks k = .todo)
    (hc : B0.bm !! k = some c) (hC : X.t.bs !! c = some C) :
    ∃ h F N, bkPre X w c C (othersO Lroot keys Dc k) h F (Dc k) N := by
  obtain ⟨C', hC', hcl, hbm, -, hloc, -, hents, -, htree⟩ := rinv_todo hI hks hc
  rw [hC] at hC'; cases hC'
  have hwx : w.wtxid = w0.wtxid := wtxid_of_C hI.C
  have hG : spG X w.wtxid (mapLen w.ms) w.fl := by rw [hwx]; exact hI.G
  by_cases hn : C.bv.rootNode' = null
  · exact ⟨0, [], [], hC, hcl, hbm, hG, rinv_treeLt hI, Or.inl hn⟩
  obtain ⟨rn, h, F, N, E, hrn, hpar, hu, hfr, hE, hpl⟩ := htree hn
  refine ⟨h, F, N, hC, hcl, hbm, hG, rinv_treeLt hI,
    Or.inr ⟨rn, E, hrn, hpar, hu, ?_, ?_, ?_, hpl, parOK_of_bktLocal (hloc hn)⟩⟩
  · apply slotInv_perm _ hI.slots
    unfold othersO
    rw [List.append_assoc]
    exact List.Perm.append_left _ (flatMap_perm_split hnd hk)
  · rw [hwx]; exact hfr
  · rw [hE, hents]

/-- **No root node: nothing changes** (`continue`). -/
theorem rinv_nil (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {C : BRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c) (hC : X.t.bs !! c = some C)
    (hnull : C.bv.rootNode' = null) :
    RInv X0 w0 B0 keys Lroot X w st Dc (upd ks k .nilc) := by
  obtain ⟨C', hC', -, -, -, -, -, -, hnil, -⟩ := rinv_todo hI hks hc
  rw [hC] at hC'; cases hC'
  have hsame : (∀ k' ∈ keys, ∀ v p, upd ks k .nilc k' ≠ .val v p) → X = X0 ∧ w = w0 ∧ st = [] :=
    fun h => hI.same (same_upd_nv hks h)
  have hput := fun hp => hI.putRoot (putRoot_upd (k := k) (s := .nilc) (fun _ e => by cases e) hp)
  have hnk := notKeys_upd (s := .nilc) hI.notKeys (hI.keysAll k (by rw [hc]; rfl))
  have hnil' := nilKids_upd (X' := X) (k := k) (s := .nilc) hI (fun _ _ _ _ _ => Or.inl rfl)
    (fun _ _ _ _ _ _ hCx hn _ hC' => by rw [hCx] at hC'; cases hC'; exact hn)
  refine { hI with kids := ?_, ents := ?_, same := hsame, putRoot := hput, notKeys := hnk, nilKids := hnil' }
  · intro k' c' hc'
    unfold upd
    by_cases e : k' = k
    · subst e; rw [if_pos rfl]; rw [hc] at hc'; cases hc'; exact hnil hnull
    · rw [if_neg e]; exact hI.kids k' c' hc'
  · rw [hI.ents]
    congr 1; funext e
    unfold upd
    by_cases h : e.1 = k
    · rw [if_pos h, h, hks]; rfl
    · rw [if_neg h]

/-- **A child's spill keeps the buffers dirty pages of fresh slots** (`spStep`'s clause). -/
theorem bkDone_bufsOK {X X' : WX} {w w' : WDb} {c : Loc} {C : BRec} {O D : List Nat}
    {st' : List FLStep} {C0 : CommitSt} (hd : bkDone X X' w w' c C O D st')
    (hb : bufsOK X C0 w.fl) (hC0 : w.C = C0) : bufsOK X' C0 w'.fl := by
  subst hC0; exact hd.1.2.2.2.2.2.2.2.2.1 hb

/-- **After `child.spill()`**: its new header (`bkRooted`) staged. -/
theorem rinv_spilled (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hnd : keys.Nodup)
    {k : GoString} {c : Loc} {C : BRec} (hk : k ∈ keys) (hks : ks k = .todo)
    (hc : B0.bm !! k = some c) (hC : X.t.bs !! c = some C) (hnn : C.bv.rootNode' ≠ null)
    {X' : WX} {w' : WDb} {st' : List FLStep}
    (hd : bkDone X X' w w' c C (othersO Lroot keys Dc k) (Dc k) st')
    (hv' : X'.v = View.ofC X'.v.base w'.C) :
    ∃ C' D', X'.t.bs !! c = some C' ∧ C'.bv.rootNode' ≠ null ∧ c ∈ X'.liveB ∧
      RInv X0 w0 B0 keys Lroot X' w' (st ++ st') (upd Dc k D')
        (upd ks k (.val (encode C'.ib) false)) :=
  rinv_spilled' hI hnd hk hks hc hC hnn hd hv' (bkDone_bufsOK hd hI.bufs hI.C)

/-- **A todo child's root node** (for `b.inlineable()`): live, its entries live and bounded. -/
theorem rinv_inlPre (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {C : BRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c) (hC : X.t.bs !! c = some C)
    (hn : C.bv.rootNode' ≠ null) :
    ∃ rn, X.node c C.bv.rootNode' = some rn ∧ C.ns !! C.bv.rootNode' = some rn ∧
      C.bv.rootNode' ∈ X.live ∧ wsLive rn.ws ∧
      ∀ w ∈ rn.ws, w.key.length + w.value.length ≤ bboltEntryMax := by
  obtain ⟨C', hC', -, -, -, hloc, -, -, -, htree⟩ := rinv_todo hI hks hc
  rw [hC] at hC'; cases hC'
  obtain ⟨rn, h, F, N, E, hrn, -, hu, -⟩ := htree hn
  have hns : C.ns !! C.bv.rootNode' = some rn := by
    unfold WX.node at hrn; rw [hC] at hrn; exact hrn
  have hun : uNode X c C.bv.rootNode' rn none none := by
    generalize Dc k = D at hu
    cases hu with
    | leaf _ r _ _ _ hr hu' => rw [hrn] at hr; cases hr; exact hu'
    | branch _ r _ _ _ _ hr hu' => rw [hrn] at hr; cases hr; exact hu'
  obtain ⟨-, B', hB', hcl, -⟩ := hloc hn
  rw [hC] at hB'; cases hB'
  have hnc := hcl.2.2.2.2.2.2.2.1 _ rn hns
  exact ⟨rn, hrn, hns, hun.1, hnc.2.2.2.2.2.1, fun w hw => (hun.2.2.2.2.2.2.1 w hw).2.2⟩

/-- **`child.free()`'s premise** for an inlineable child (its root node a leaf). -/
theorem rinv_freePre (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {C : BRec} {rn : NRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c)
    (hC : X.t.bs !! c = some C) (hrn : X.node c C.bv.rootNode' = some rn)
    (hleaf : rn.nv.isLeaf' = true) :
    C.ib.root' ≠ W64 0 → bktLocalOK X c ∧ (∀ pid ∈ X.positions c, X.t.pm !! pid = none) ∧
      w.fl.canFreeAll w.wtxid (X.extents c) ∧ rtOK X c ∧ X.t.mv.txid' = w.wtxid :=
  rinv_freePre' hI hks hc hC hrn hleaf

/-- **After `child.free()`, for `child.write()`**: the child's record and root leaf after the free,
`write`'s premises, and the inline value staged (`BktLoopPureInline.rinv_inline'`). The inodes'
lengths (`insLens`, `NodeSpillTailWp.wtxW_lens` at the caller) give `write`'s size relation; the
view's pages are the committed state's (`hv`, the caller's `wdbW`): the freed page's slots are
tree slots, no buffer's. -/
theorem rinv_inline (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {C : BRec} {rn : NRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c)
    (hC : X.t.bs !! c = some C) (hrn : X.node c C.bv.rootNode' = some rn)
    (hleaf : rn.nv.isLeaf' = true) (hinl : inlineIns rn.ins) (hlens : insLens rn.ins rn.ws)
    (hnd : keys.Nodup) (hv : X.v.pages = w.C.pages)
    {X' : WX} {w' : WDb}
    (hfree : (C.ib.root' = W64 0 ∧ X' = X ∧ w' = w) ∨
      (C.ib.root' ≠ W64 0 ∧ bktFreed X X' c ∧
        w' = w.withFl (w.fl.freeAll w.wtxid (X.extents c)))) :
    ∃ C1 rn1 st', X'.t.bs !! c = some C1 ∧ C1.bv.rootNode' = C.bv.rootNode' ∧
      C1.ns !! C.bv.rootNode' = some rn1 ∧ C.bv.rootNode' ∈ X'.live ∧ c ∈ X'.liveB ∧
      X'.v = X.v ∧ rn1.nv.isLeaf' = true ∧ wsLive rn1.ws ∧
      (wsMs rn1.ws).length < 0xFFFF ∧ pageFits (wsMs rn1.ws) ∧
      insSize rn1.ins = 16 + (pageBody true (wsMs rn1.ws)).length ∧ insSize rn1.ins < 2 ^ 31 ∧
      RInv X0 w0 B0 keys Lroot X' w' (st ++ st') (upd Dc k [])
        (upd ks k (.val (inlineVal C1.ib rn1.ws) false)) :=
  rinv_inline' hI hnd hks hc hC hrn hleaf hinl hlens hv hfree

theorem isBktFlag_of_mod' (f : Nat) (h : f % 2 = 1) : isBktFlag (W32 (f : Int)) := by
  unfold isBktFlag
  intro e
  have := congrArg BitVec.toNat e
  simp [BitVec.toNat_and] at this
  omega

/-- **The child's entry in the root bucket** (what the search finds). -/
theorem rinv_entry (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    (hc : B0.bm !! k = some c) :
    ∃ we ∈ X.allEnts X0.rl, we.key = k ∧ isBktFlag we.flags := by
  have hok := hpre.1
  have hrt : rtOK X0 X0.rl := hpre.2.2.2.1 X0.rl (by rw [hB0]; simp)
  have h0 : B0.ib.root' ≠ W64 0 := hok.1.2.1.2.2.2.2 B0 hB0
  -- the child's entry at the start
  obtain ⟨we, hwe, hk, hf⟩ : ∃ we ∈ X0.allEnts X0.rl, we.key = k ∧ isBktFlag we.flags := by
    obtain ⟨C, v, -, hin, -⟩ := (hok.2.1 X0.rl B0 hB0).2 k c hc
    rcases hin with ⟨l, r, we, hr, hl, hw, hk, hf, -⟩ | ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, hk, hf, -⟩
    · exact ⟨we, mem_allEnts_node hok hreach hrt hB0 h0 hr hl hw, hk, hf⟩
    · refine ⟨pageW pg i, mem_allEnts_page hok hreach hrt hB0 ?_ hpr hown hpg hfl hi, ?_, ?_⟩
      · intro p' pg' hp'
        have := hfv.2.2.1 p' pg' hp'
        omega
      · unfold pageW; rw [if_pos hfl]; exact hk
      · unfold pageW; rw [if_pos hfl]
        exact isBktFlag_of_mod' _ (by unfold bucketLeafFlag at hf; omega)
  -- its root entry now
  have hm0 : (k, we.value) ∈ rootEnts X0 := by
    unfold rootEnts
    unfold WX.allEnts at hwe
    obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hwe
    refine List.mem_flatMap.2 ⟨ws, hws, List.mem_filterMap.2 ⟨we, hw, ?_⟩⟩
    rw [if_pos (decide_eq_true hf)]; rw [hk]
  have hm : ∃ v', (k, v') ∈ rootEnts X := by
    rw [hI.ents]
    exact ⟨_, List.mem_map.2 ⟨_, hm0, rfl⟩⟩
  obtain ⟨v', hm⟩ := hm
  unfold rootEnts at hm
  obtain ⟨ws, hws, hw⟩ := List.mem_flatMap.1 hm
  obtain ⟨we', hw', he⟩ := List.mem_filterMap.1 hw
  by_cases hb : isBktFlag we'.flags
  · rw [if_pos (decide_eq_true hb)] at he
    cases he
    refine ⟨we', ?_, rfl, hb⟩
    rw [← hI.rl]
    exact List.mem_flatten.2 ⟨ws, hws, hw'⟩
  · rw [if_neg (by simpa using hb)] at he; cases he

/-- **The root bucket's search can materialize its path** (`Cursor.node`'s `matReady`). -/
theorem rinv_ready (hpre : spillPre X0 w0.fl) (hB0 : X0.t.bs !! X0.rl = some B0) (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks)
    {B : BRec} (hB : X.t.bs !! X0.rl = some B) {els : List elemRef} {pids : List w64}
    (hp : lPath X X0.rl els pids) :
    B.ib.root' ≠ W64 0 ∧ viewWF X.v ∧ ∀ pid ∈ pids, resolve B pid = none →
      ∃ pg, X.v.pages !! pid.toNat = some pg ∧ X.t.pm !! pid = none := by
  have h0 : B.ib.root' ≠ W64 0 := by
    rw [hI.rootIb B hB]; exact hpre.1.1.2.1.2.2.2.2 B0 hB0
  obtain ⟨-, B', hB', -, -, -, -, hvw⟩ := hI.rootOK.1
  refine ⟨h0, hvw, ?_⟩
  intro pid hpid hres
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hpid
  obtain ⟨e, he⟩ : ∃ e, els[j]? = some e := by
    have hlen := hp.2.1
    have hjl : j < pids.length := (List.getElem?_eq_some_iff.1 hj).1
    exact ⟨els[j], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨⟨B'', hB'', href⟩, -⟩ := hp.2.2.2 j e pid he hj
  rw [hB] at hB''; cases hB''
  simp only [hres] at href
  obtain ⟨-, pg, hw⟩ := href
  unfold wpageAt at hw
  rw [if_neg h0] at hw
  cases hpg : X.v.pages !! pid.toNat with
  | none => rw [hpg] at hw; cases hw
  | some pg' =>
    refine ⟨pg', rfl, ?_⟩
    cases hpm : X.t.pm !! pid with
    | none => rfl
    | some x =>
      have := pmFresh_of_spG hI.G pid (by rw [hpm]; rfl)
      rw [hpg] at this; cases this

/-- **`node.put`'s premises at the leaf the search lands on** (after `Cursor.node`). -/
theorem rinv_putPre (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {X1 : WX}
    (hm : matGrow X X1 X0.rl) {els : List elemRef} {pids : List w64} {k : List w8}
    (hp : lPath X X0.rl els pids) (hr : lRoutes X X0.rl els pids k) {B1 : BRec} {pid : w64}
    {l : Loc} (hB1 : X1.t.bs !! X0.rl = some B1) (hlast : pids.getLast? = some pid)
    (hres : resolve B1 pid = some l) (hk : ∃ we ∈ X.allEnts X0.rl, we.key = k) :
    ∃ rl, B1.ns !! l = some rl ∧ l ∈ X1.live ∧ rl.nv.bucket' = X0.rl ∧ rl.capOwn = true ∧
      wsSorted rl.ws ∧ wsLive rl.ws ∧ 0 < X1.t.mv.pgid'.toNat ∧ X1.v = X.v ∧
      rl.nv.parent' ≠ l ∧ 0 < k.length ∧ X1.t.bs !! X0.rl = some B1 :=
  rinv_putPre' hI hm hp hB1 hlast hres hk

/-- **The staged value put into the root bucket's leaf.** -/
theorem rinv_put (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {v : List w8} (hks : ks k = .val v false) (hc : B0.bm !! k = some c) {X1 : WX}
    (hm : matGrow X X1 X0.rl) {els : List elemRef} {pids : List w64}
    (hp : lPath X X0.rl els pids) (hr : lRoutes X X0.rl els pids k) {B1 : BRec} {pid : w64}
    {l : Loc} {rl : NRec} (hB1 : X1.t.bs !! X0.rl = some B1) (hlast : pids.getLast? = some pid)
    (hres : resolve B1 pid = some l) (hrl : B1.ns !! l = some rl) (s : GoSlice)
    (ins : List Inode) (hins : ins.length = (wsPutAt rl.ws k (rootEnt k v)).length)
    (hent : ∃ we ∈ X.allEnts X0.rl, we.key = k ∧ isBktFlag we.flags) :
    RInv X0 w0 B0 keys Lroot
      (X1.setNode X0.rl l (rl.withEnts s ins (wsPutAt rl.ws k (rootEnt k v)))) w st Dc
      (upd ks k (.val v true)) :=
  rinv_put' hI hks hc hm hp hr hB1 hlast hres hrl s ins hins hent

end step

end Spill

end bbolt
end EtcdGrove
end Perennial
