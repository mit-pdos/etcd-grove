/-
`Bucket.spill`'s root loop (U9x4, `notes/bbolt-proof-plan.md`): **the invariant after an inlineable
child's `free` and `write`** (`rinv_inline'`, `BktLoopStep.rinv_inline`'s proof). The child's root
node is a leaf of plain entries, so it owns only its own page (`Dc k`, its run); `Bucket.free`
(`bktFreed`, when the bucket is not inline already) sets the header's root and the leaf's page id
to `0` and frees the run (pending); no other bucket changes, so the root bucket's facts and the
other children's states are kept (`childSt_kept` with identity), and the child's state is the
inline value (`inlineVal_ok`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureSpilled
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureFree
public import Proof.go_etcd_io.bbolt.Spill.BktInlineVal
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureG

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section inline
variable [GooseExts]

/-- A node's record but its page id (what `Bucket.free` changes). -/
def nodeF (r r' : NRec) : Prop :=
  r'.nv.parent' = r.nv.parent' ∧ r'.cs = r.cs ∧ r'.nv.bucket' = r.nv.bucket' ∧ r'.ws = r.ws ∧
  r'.nv.key' = r.nv.key' ∧ r'.key = r.key ∧ r'.ksrc = r.ksrc

/-- A bucket's record but its header and its nodes' page ids. -/
def bktF (B B' : BRec) : Prop :=
  B'.bm = B.bm ∧ B'.bv = B.bv ∧ ∀ l, optRel nodeF (B.ns !! l) (B'.ns !! l)

theorem nodeF_refl (r : NRec) : nodeF r r := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nodeRootIn_F {B B' : BRec} (h : bktF B B') {a rt : Loc} (hd : nodeRootIn B a rt) :
    nodeRootIn B' a rt := by
  induction hd with
  | top a r hr hp =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2.2 a)
    exact .top a r' hr' (by rw [hs.1]; exact hp)
  | up a rt r hr hp _ ih =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2.2 a)
    exact .up a rt r' hr' (by rw [hs.1]; exact hp) (by rw [hs.1]; exact ih)

theorem descIn_F {B B' : BRec} (h : bktF B B') {a d : Loc} (hd : descIn B a d) :
    descIn B' a d := by
  induction hd with
  | self a => exact .self a
  | child a c d r hr hc _ ih =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2.2 a)
    exact .child a c d r' hr' (by rw [hs.2.1]; exact hc) ih

/-- **The spill's global state across a change of the buckets' headers and nodes' page ids.** -/
theorem spG_bktF {X : WX} {bs' : GMap Loc BRec} {txid : w64} {ml : Nat} {fl : FLPg}
    (hbs : ∀ bl, optRel bktF (X.t.bs !! bl) (bs' !! bl)) (hG : spG X txid ml fl) :
    spG { X with t := { X.t with bs := bs' } } txid ml fl := by
  obtain ⟨h1, h2, ⟨d1, d2, d3, d4, d5⟩, hf, ⟨r1, r2⟩, h8⟩ := hG
  refine ⟨h1, h2, ⟨?_, ?_, ?_, ?_, d5⟩, ?_, ⟨?_, ?_⟩, h8⟩
  · intro bl B' l r' hB' hr' hl
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨r, hr, hn⟩ := optRel_some_r (hr' ▸ hs.2.2 l)
    obtain ⟨b1, b2, b3, b4⟩ := d1 bl B l r hB hr hl
    refine ⟨by rw [hn.2.2.1]; exact b1, by rw [hn.2.2.2.1]; exact b2,
      by rw [hn.2.2.2.2.1, hn.2.2.2.2.2.1]; exact b3, fun c hc => ?_⟩
    rw [hn.2.1] at hc
    exact ⟨(b4 c hc).1, by rw [← optRel_isSomeQ (hs.2.2 c)]; exact (b4 c hc).2⟩
  · intro bl B' hB' hlb
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨b1, b2⟩ := d2 bl B hB hlb
    refine ⟨fun k c hk => ?_, fun hrn => ?_⟩
    · rw [hs.1] at hk
      obtain ⟨c1, c2⟩ := b1 k c hk
      exact ⟨c1, by show (bs' !! c).isSome; rw [← optRel_isSomeQ (hbs c)]; exact c2⟩
    · rw [hs.2.1] at hrn ⊢
      obtain ⟨rt, hrt, hl⟩ := b2 hrn
      exact ⟨rt, nodeRootIn_F hs hrt, hl⟩
  · intro bl B' hB'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨b1, b2⟩ := d3 bl B hB
    refine ⟨b1, ?_⟩
    have := optRel_isSomeQ (hs.2.2 null)
    rw [b2] at this
    cases e : B'.ns !! null with
    | none => rfl
    | some _ => rw [e] at this; cases this
  · show (bs' !! X.rl).isSome
    rw [← optRel_isSomeQ (hbs X.rl)]; exact d4
  · intro bl B' l r' hB' hr' hl
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨r, hr, hn⟩ := optRel_some_r (hr' ▸ hs.2.2 l)
    obtain ⟨f1, f2⟩ := hf bl B l r hB hr hl
    refine ⟨by rw [hn.2.2.2.1]; exact f1, ?_⟩
    rw [hn.2.2.2.2.1, hn.2.2.2.2.2.2]; exact f2
  · intro bl B' hB' hlb
    obtain ⟨B, hB, -⟩ := optRel_some_r (hB' ▸ hbs bl)
    have hrc := r1 bl B hB hlb
    clear hB' hB hlb
    induction hrc with
    | root => exact .root
    | child b c B2 n hB2 hn _ ih =>
      obtain ⟨B3, hB3, hs⟩ := optRel_some_l (hB2 ▸ hbs b)
      exact .child b c B3 n hB3 (by rw [hs.1]; exact hn) ih
  · intro bl B' l r' hB' hr' hl
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ hbs bl)
    obtain ⟨r, hr, -⟩ := optRel_some_r (hr' ▸ hs.2.2 l)
    obtain ⟨rt, hrt, hd⟩ := r2 bl B l r hB hr hl
    exact ⟨rt, by rw [hs.2.1]; exact nodeRootIn_F hs hrt, descIn_F hs hd⟩

/-- `spG` reads only the freelist's free ids. -/
theorem spG_fl' {X : WX} {txid : w64} {ml : Nat} {fl fl' : FLPg} (hf : fl'.free = fl.free)
    (h : spG X txid ml fl) : spG X txid ml fl' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, fun id hid => by rw [hf]; exact a8 id hid, a9.1, a9.2.1,
    by rw [hf]; exact a9.2.2⟩

theorem not_isBktFlag_of_mod {f : w32} (h : f.toNat % 2 = 0) : ¬ isBktFlag f := by
  unfold isBktFlag
  intro e
  apply e
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and, Nat.and_one_is_mod]
  omega

variable {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString} {Lroot : List Nat}
  {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}

/-- **An inlineable child's facts** (a todo child whose root node is a leaf). -/
theorem inl_child (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {C : BRec} {rn : NRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c)
    (hC : X.t.bs !! c = some C) (hrn : X.node c C.bv.rootNode' = some rn)
    (hleaf : rn.nv.isLeaf' = true) :
    C.ns !! C.bv.rootNode' = some rn ∧ c ∈ X.liveB ∧ c ≠ X.rl ∧
    C.bv.rootNode' ∈ X.live ∧ rn.nv.pgid' = C.ib.root' ∧ Dc k = ownSl X.v rn.nv.pgid' ∧
    ownPg X.v rn.nv.pgid' ∧ rn.ins.length = rn.ws.length ∧ wsSorted rn.ws ∧ wsLive rn.ws ∧
    (∀ w ∈ rn.ws, w.flags.toNat % 2 = 0 ∧ 0 < w.key.length ∧
      w.key.length + w.value.length ≤ bboltEntryMax) ∧
    rn.ws.map (fun w => (w.key, w.value)) = lbktEnts X0 c ∧
    resolve C C.ib.root' = some C.bv.rootNode' := by
  have htd := hI.kids k c hc
  rw [hks] at htd
  obtain ⟨C', hC', hlive, -, hne, hloc, -, -, -, htree⟩ := htd
  rw [hC] at hC'; cases hC'
  have hG := hI.G
  have hns : C.ns !! C.bv.rootNode' = some rn := by
    unfold WX.node at hrn; rw [hC] at hrn; exact hrn
  have hnn : C.bv.rootNode' ≠ null := by
    intro e
    have := (hG.2.2.1.2.2.1 c C hC).2
    rw [e] at hns; rw [this] at hns; cases hns
  obtain ⟨-, B', hB', hcl, -⟩ := hloc hnn
  rw [hC] at hB'; cases hB'
  have hnm := hcl.2.2.2.1 hnn
  obtain ⟨-, r0, hr0, hpg0⟩ := hcl.2.2.2.2.1 _ _ hnm
  rw [hns] at hr0; cases hr0
  have hres : resolve C C.ib.root' = some C.bv.rootNode' := by
    unfold resolve
    by_cases h0 : C.ib.root' = W64 0
    · rw [if_pos h0, if_neg hnn]
    · rw [if_neg h0]; exact hnm
  obtain ⟨rn', h, F, N, E, hrn', -, hu, -, hE, hpl⟩ := htree hnn
  rw [hrn] at hrn'; cases hrn'
  generalize hD : Dc k = D at hu
  cases hu with
  | branch _ r _ _ _ _ hr _ hl =>
    rw [hrn] at hr; cases hr; rw [hleaf] at hl; cases hl
  | leaf _ r _ _ Sb hr hu' _ _ _ hSb =>
    rw [hrn] at hr; cases hr
    have hpl' : ∀ w ∈ rn.ws, w.flags.toNat % 2 = 0 ∧ 0 < w.key.length ∧
        w.key.length + w.value.length ≤ bboltEntryMax :=
      fun w hw => hpl (wEl w) (List.mem_map_of_mem hw)
    have hz : ((List.range rn.ws.length).flatMap fun i => pgSlots (spP X) (Sb i)) = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro i hi
      rw [List.mem_range] at hi
      rw [hSb i rn.ws[i] (List.getElem?_eq_getElem hi)
        (not_isBktFlag_of_mod (hpl' _ (List.getElem_mem hi)).1)]
      rfl
    refine ⟨hns, hlive, hne, hu'.1, hpg0, by rw [hz, List.append_nil], hu'.2.2.2.2.2.2.2, hu'.2.2.2.2.1,
      hu'.2.2.2.2.2.1, (hG.2.2.2.1 c C _ rn hC hns hu'.1).1, hpl', ?_, hres⟩
    rw [← hE, List.map_map]; rfl

theorem freeAll_one (fl : FLPg) (txid id : w64) (n : Nat) :
    fl.freeAll txid [(id, n)] = fl.freePages txid id n := rfl

theorem applySteps_free_one (fl : FLPg) (txid id : w64) (n : Nat) :
    fl.applySteps txid [.free id n] = fl.freePages txid id n := rfl

/-- The entries' value in the root bucket through a state change that is not `val _ true`. -/
theorem ents_upd {X : WX} {ks : GoString → KSt} {k : GoString} {v : List w8}
    (hks : ks k = .todo) (h : rootEnts X = (rootEnts X0).map fun e => (e.1, (ks e.1).entVal e.2)) :
    rootEnts X = (rootEnts X0).map fun e => (e.1, ((upd ks k (.val v false)) e.1).entVal e.2) := by
  rw [h]
  congr 1; funext e
  unfold upd
  by_cases h : e.1 = k
  · rw [if_pos h, h, hks]; rfl
  · rw [if_neg h]

set_option maxHeartbeats 1000000 in
/-- **After `child.free()` and `child.write()`** (see the module doc). -/
theorem rinv_inline' (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hnd : keys.Nodup)
    {k : GoString} {c : Loc}
    {C : BRec} {rn : NRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c)
    (hC : X.t.bs !! c = some C) (hrn : X.node c C.bv.rootNode' = some rn)
    (hleaf : rn.nv.isLeaf' = true) (hinl : inlineIns rn.ins) (hlens : insLens rn.ins rn.ws)
    (hv : X.v.pages = w.C.pages)
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
        (upd ks k (.val (inlineVal C1.ib rn1.ws) false)) := by
  obtain ⟨hns, hlB, hcne, hlive, hpg, hDk, hown, hlen, hsort, hwl, hpl, hEnts, hres⟩ :=
    inl_child hI hks hc hC hrn hleaf
  have hk : k ∈ keys := hI.keysAll k (by rw [hc]; rfl)
  have hwx : w.wtxid = w0.wtxid := wtxid_of_C hI.C
  have hcX0 : c ≠ X0.rl := by rw [← hI.rl]; exact hcne
  have hnnC : C.bv.rootNode' ≠ null := by
    intro e
    have h1 := (hI.G.2.2.1.2.2.1 c C hC).2
    have h2 := hns
    rw [e, h1] at h2; cases h2
  have hnk := notKeys_upd (s := .val (inlineVal C.ib rn.ws) false) hI.notKeys hk
  rcases hfree with ⟨h0, hX', hw'⟩ | ⟨h0, hfd, rfl⟩
  · -- already inline: no page, nothing freed
    rw [hX', hw']
    have hDk0 : Dc k = [] := by rw [hDk, hpg, h0]; unfold ownSl; rw [if_pos rfl]
    have iv := inlineVal_ok (ib := C.ib) h0 hsort hpl hlens hlen hinl.2 (spP X) X.t.mv.pgid'.toNat
    refine ⟨C, rn, [], hC, rfl, hns, hlive, hlB, rfl, hleaf, hwl, iv.1, iv.2.1, iv.2.2.1,
      iv.2.2.2.1, ?_⟩
    have hupd : upd Dc k [] = Dc := by
      funext k'; unfold upd
      by_cases e : k' = k
      · subst e; rw [if_pos rfl, hDk0]
      · rw [if_neg e]
    rw [List.append_nil, hupd]
    have hsame : (∀ k' ∈ keys, ∀ v p,
        upd ks k (.val (inlineVal C.ib rn.ws) false) k' ≠ .val v p) → X = X0 ∧ w = w0 ∧ st = [] :=
      fun h => absurd h (same_upd_val hk _ _)
    have hput := fun hp => hI.putRoot (putRoot_upd (k := k)
      (s := .val (inlineVal C.ib rn.ws) false) (fun _ e => by cases e) hp)
    have hnil' := nilKids_upd (X' := X) (s := .val (inlineVal C.ib rn.ws) false) hI
      (nilKids_self_todo hI hks hc hC hnnC _)
      (fun _ _ _ _ _ _ hCx hn _ hC' => by rw [hCx] at hC'; cases hC'; exact hn)
    refine { hI with kids := ?_, ents := ents_upd hks hI.ents, same := hsame, putRoot := hput, notKeys := hnk, nilKids := hnil' }
    intro k' c' hc'
    unfold upd
    by_cases e : k' = k
    · subst e; rw [if_pos rfl]; rw [hc] at hc'; cases hc'
      exact ⟨[], iv.2.2.2.2.1, by rw [hDk0]; rfl, by rw [← hEnts]; exact iv.2.2.2.2.2.1,
        iv.2.2.2.2.2.2⟩
    · rw [if_neg e]; exact hI.kids k' c' hc'
  -- `Bucket.free`: the header's root and the leaf's page id `0`, its run freed
  obtain ⟨B, ns', hB, hX', hns'⟩ := hfd
  rw [hC] at hB; cases hB
  subst hX'
  have hp0 : rn.nv.pgid' ≠ W64 0 := by rw [hpg]; exact h0
  obtain ⟨pg, hpgv, -, -, -, h2, hb⟩ := hown hp0
  have hpos := positions_leafRoot hC hres hns hleaf
  have hext : X.extents c = [(rn.nv.pgid', 1 + pageOverflow pg)] := by
    unfold WX.extents; rw [hpos]
    simp only [List.filterMap_cons, List.filterMap_nil]
    unfold WX.posExtent
    rw [hC]; simp only; rw [hres]; simp only; rw [hns]
    simp only [Option.map_some, Option.getD_some]
    rw [if_neg hp0, hpgv]; rfl
  rw [hext, freeAll_one, hwx]
  -- the run
  have hDr : Dc k = List.range' rn.nv.pgid'.toNat (1 + pageOverflow pg) := by
    rw [hDk]; unfold ownSl pgSlots; rw [if_neg hp0]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]; rw [hpgv]
  have hsl0 : slotInv w.fl X.t.mv.pgid'.toNat (List.range' rn.nv.pgid'.toNat (1 + pageOverflow pg) ++ othersO Lroot keys Dc k) := by
    refine slotInv_perm ?_ hI.slots
    rw [← hDr]; exact (perm_old hnd hk).trans List.perm_append_comm
  have hidL : rn.nv.pgid'.toNat ∈ Dc k := by rw [hDr]; exact List.mem_range'_1.2 ⟨by omega, by omega⟩
  have hid62 : rn.nv.pgid'.toNat < 2 ^ 62 :=
    (hsl0.2.1 rn.nv.pgid'.toNat (List.mem_append_left _ (List.mem_range'_1.2 ⟨by omega, by omega⟩))).2.1
  have hn64 : rn.nv.pgid'.toNat + (1 + pageOverflow pg) < 2 ^ 64 := by omega
  have hndO : (othersO Lroot keys Dc k ++ Dc k).Nodup := (perm_old hnd hk).nodup_iff.1 hI.slots.1
  -- the records
  let C1 : BRec := { C with ib := { C.ib with root' := W64 0 }, ns := ns' }
  let rn1 : NRec := { rn with nv := { rn.nv with pgid' := W64 0 } }
  have hbs : ∀ bl, bl ≠ c → (X.setBkt c C1).t.bs !! bl = X.t.bs !! bl := by
    intro bl h; show (X.t.bs.insert c C1) !! bl = _; exact GMap.lookup_insert_ne _ _ (Ne.symm h)
  have hBc : (X.setBkt c C1).t.bs !! c = some C1 := GMap.lookup_insert _ _ _
  have hns1 : C1.ns !! C.bv.rootNode' = some rn1 := by
    show ns' !! _ = _
    rw [hns' C.bv.rootNode', hns]
    simp only [Option.map_some]
    rw [if_pos ⟨C.ib.root', by rw [hpos]; exact List.mem_singleton_self _, hres⟩]
  have hF : ∀ bl, optRel bktF (X.t.bs !! bl) ((X.setBkt c C1).t.bs !! bl) := by
    intro bl
    by_cases e : bl = c
    · subst e; rw [hBc, hC]
      refine ⟨rfl, rfl, fun l => ?_⟩
      show optRel nodeF (C.ns !! l) (ns' !! l)
      rw [hns' l]
      cases C.ns !! l with
      | none => trivial
      | some r =>
        simp only [Option.map_some]
        show nodeF r _
        split
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact nodeF_refl r
    · rw [hbs bl e]
      exact optRel_refl (fun B => ⟨rfl, rfl, fun l => optRel_refl nodeF_refl _⟩) _
  have hG' : spG (X.setBkt c C1) w0.wtxid (mapLen w.ms) (w.fl.freePages w0.wtxid rn.nv.pgid' (1 + pageOverflow pg)) :=
    spG_fl' (fl := w.fl) rfl (spG_bktF hF hI.G)
  have hbsS : ∀ bl, ((X.setBkt c C1).t.bs !! bl).isSome = (X.t.bs !! bl).isSome := by
    intro bl
    by_cases e : bl = c
    · subst e; rw [hBc, hC]; rfl
    · rw [hbs bl e]
  have hfuel : (X.setBkt c C1).fuel = X.fuel := fuel_kept rfl hbsS
  have hkept : ∀ bl, bl ≠ c → bktKept X (X.setBkt c C1) bl := by
    intro bl h B hB
    exact ⟨B, by rw [hbs bl h]; exact hB, bktSim_refl B, fun l => optRel_refl nodeSim_refl _⟩
  have hvs : ∀ bl, bl ≠ c → ∀ B B' l r r', X.t.bs !! bl = some B →
      (X.setBkt c C1).t.bs !! bl = some B' → B.ns !! l = some r → B'.ns !! l = some r' →
      l ∈ X.live → leafVs r → leafVs r' := by
    intro bl h B B' l r r' hB hB' hr hr' _ hl
    rw [hbs bl h, hB] at hB'; cases hB'; rw [hr] at hr'; cases hr'; exact hl
  have hvw : viewWF X.v := by
    obtain ⟨-, -, -, -, -, -, -, hvw⟩ := hI.rootOK.1; exact hvw
  have hreach : liveReach X := hI.G.2.2.2.2.1
  have hrootB : ∀ B, X.t.bs !! X0.rl = some B → B.ib.root' ≠ W64 0 := by
    intro B hB; rw [hI.rootIb B hB]; exact hI.rootPg
  obtain ⟨Br, hBr, hBrb, hBrm⟩ := hI.root
  have hBr' : (X.setBkt c C1).t.bs !! X0.rl = some Br := by rw [hbs _ (Ne.symm hcX0)]; exact hBr
  have hleavesR := leaves_kept (X' := X.setBkt c C1) hBr hBr' (bktSim_refl Br)
    (fun l => optRel_refl nodeSim_refl _) rfl hfuel
  have hpendS : ∀ s, s ∈ pendSlots (w.fl.freePages w0.wtxid rn.nv.pgid' (1 + pageOverflow pg)) ↔
      s ∈ pendSlots w.fl ∨ (rn.nv.pgid'.toNat ≤ s ∧ s < rn.nv.pgid'.toNat + (1 + pageOverflow pg)) :=
    pendSlots_freePages w.fl w0.wtxid rn.nv.pgid' (1 + pageOverflow pg) hn64
  have hiv := inlineVal_ok (ib := C1.ib) rfl hsort hpl hlens hlen hinl.2 (spP X) X.t.mv.pgid'.toNat
  refine ⟨C1, rn1, [.free rn.nv.pgid' (1 + pageOverflow pg)], hBc, rfl, hns1, hlive, hlB, rfl, hleaf, hwl, hiv.1, hiv.2.1,
    hiv.2.2.1, hiv.2.2.2.1, ?_⟩
  exact {
    C := hI.C
    fl := by
      show w.fl.freePages w0.wtxid rn.nv.pgid' (1 + pageOverflow pg) = _
      rw [applySteps_append, ← hI.fl, applySteps_free_one]
    pages := hI.pages
    rl := hI.rl
    mark := hI.mark
    G := hG'
    root := ⟨Br, hBr', hBrb, hBrm⟩
    rootOK := rootLoc_kept hI.rootOK (hkept X0.rl (Ne.symm hcX0)) rfl hvw (Nat.le_refl _)
      hI.rootOK.1.1 hreach hG'.2.2.1 hG'.2.2.2.1 hfuel hrootB (hvs X0.rl (Ne.symm hcX0))
    rootIb := by
      intro B hB; rw [hBr'] at hB; cases hB; exact hI.rootIb Br hBr
    slots := by
      have := slotInv_free (txid := w0.wtxid) hsl0
      rw [← List.append_nil (othersO Lroot keys Dc k)] at this
      exact slotInv_perm (perm_upd hnd hk []).symm this
    base := by
      intro s hs
      rcases hI.base s hs with hm | hp
      · rcases List.mem_append.1 ((perm_old hnd hk).mem_iff.1 hm) with ho | hdk
        · exact Or.inl ((perm_upd hnd hk []).mem_iff.2 (List.mem_append_left _ ho))
        · rw [hDr] at hdk
          obtain ⟨a1, a2⟩ := List.mem_range'_1.1 hdk
          exact Or.inr ((hpendS s).2 (Or.inr ⟨a1, a2⟩))
      · exact Or.inr ((hpendS s).2 (Or.inl hp))
    new := by
      intro s hs
      rcases List.mem_append.1 ((perm_upd hnd hk []).mem_iff.1 hs) with ho | hdk
      · rcases hI.new s ((perm_old hnd hk).mem_iff.2 (List.mem_append_left _ ho)) with h | h
        · exact Or.inl h
        · exact Or.inr (newSlot_mono h (fun x hx => List.mem_append_left _ hx) (Nat.le_refl _))
      · cases hdk
    agree := hI.agree
    kids := by
      intro k' c' hc'
      unfold upd
      by_cases e : k' = k
      · subst e
        rw [hc] at hc'; cases hc'
        rw [if_pos rfl, if_pos rfl]
        exact ⟨[], hiv.2.2.2.2.1, rfl, by rw [← hEnts]; exact hiv.2.2.2.2.2.1, hiv.2.2.2.2.2.2⟩
      · have hcc : c' ≠ c := by
          intro h; subst h; exact e (hI.inj k' k c' hc' hc)
        have hk' : k' ∈ keys := hI.keysAll k' (by rw [hc']; rfl)
        rw [if_neg e, if_neg e]
        refine childSt_kept (hI.kids k' c' hc') (hkept c' hcc) (hvs c' hcc) rfl hvw
          (Nat.le_refl _) rfl rfl hreach hG'.2.2.1 hG'.2.2.2.1 hfuel (fun _ _ => rfl) ?_
        intro F hFD hfr x hx
        obtain ⟨a, b⟩ := hfr x hx
        refine ⟨a, ?_⟩
        show ((GMap.delete rn.nv.pgid' w.fl.allocs) !! W64 (x : Int)).getD 0 ≠ _
        rw [GMap.lookup_delete_ne]
        · exact b
        · intro he
          have hxO := mem_othersO (Lroot := Lroot) hk' e (hFD x hx)
          have hx62 := (hI.slots.2.1 x ((perm_old hnd hk).mem_iff.2
            (List.mem_append_left _ hxO))).2.1
          have hxid : x = rn.nv.pgid'.toNat := by rw [he, w64_toNat_of_lt hx62]
          exact (List.nodup_append.1 hndO).2.2 _ hxO _ hidL hxid
    ents := by
      rw [show rootEnts (X.setBkt c C1) = rootEnts X from
        Write.rootEnts_eq_of_dat X _ (by have e := hI.rl; rw [← e] at hleavesR; exact hleavesR)]
      exact ents_upd hks hI.ents
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
    grow := hI.grow
    src := hI.src
    wb := hI.wb
    bufs := by
      intro y pgb hy
      obtain ⟨b1, b2, b3, b4, b5⟩ := hI.bufs y pgb hy
      refine ⟨b1, b2, b3, b4, fun j hj => ⟨(b5 j hj).1, fun hm => ?_, (b5 j hj).2.2.1,
        (b5 j hj).2.2.2⟩⟩
      rcases (hpendS _).1 hm with hm | ⟨a1, a2⟩
      · exact (b5 j hj).2.1 hm
      · apply (b5 j hj).1
        unfold treeSlots
        rw [mem_pagesSlots_iff, ← hI.C, ← hv]
        exact ⟨_, pg, hpgv, a1, a2⟩
    rootPos := by
      intro B hB; rw [hBr'] at hB; cases hB; exact hI.rootPos Br hBr
    shape0 := hI.shape0
    hwm0 := hI.hwm0
    freeNC := hI.freeNC
    tt := hI.tt
    same := fun h => absurd h (same_upd_val hk _ _)
    putRoot := by
      intro hp B hB; rw [hBr'] at hB; cases hB
      exact hI.putRoot (putRoot_upd (fun _ e => by cases e) hp) Br hBr
    mvEq := hI.mvEq
    rootFree := by
      intro F hF x hx
      obtain ⟨a, b⟩ := hI.rootFree F hF x hx
      refine ⟨a, ?_⟩
      show ((GMap.delete rn.nv.pgid' w.fl.allocs) !! W64 (x : Int)).getD 0 ≠ _
      rw [GMap.lookup_delete_ne]
      · exact b
      · intro he
        have hxO : x ∈ othersO Lroot keys Dc k := List.mem_append_left _ (hF x hx).1
        have hxid : x = rn.nv.pgid'.toNat := by rw [he, w64_toNat_of_lt (hF x hx).2.2]
        exact (List.nodup_append.1 hndO).2.2 _ hxO _ hidL hxid
    lroot := hI.lroot
    rootExt := (extents_kept hBr hBr' (bktSim_refl Br) (fun l => optRel_refl nodeSim_refl _) rfl
      hfuel).trans hI.rootExt
    notKeys := notKeys_upd hI.notKeys hk
    nilKids := by
      refine nilKids_upd hI (nilKids_self_todo hI hks hc hC hnnC _) ?_
      intro k' c' Cx e hc' _ hCx hn C' hC'
      have hcc : c' ≠ c := by
        intro h; subst h; exact e (hI.inj k' k c' hc' hc)
      rw [hbs c' hcc, hCx] at hC'; cases hC'; exact hn }

end inline

end Spill

end bbolt
end EtcdGrove
end Perennial
