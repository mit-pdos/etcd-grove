/-
`node.spill` after its children's loop (U9z, `notes/bbolt-proof-plan.md`; pure): **the spill's
global state (`spG`) across a piece's step** (`pcStep`): across the piece's allocation
(`spG_alloc`) and the records and buffer its write leaves (`spG_pcFin`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureG
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureAlloc
public import Proof.go_etcd_io.bbolt.Spill.AllocDeref
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section g
variable [GooseExts]

theorem setNode_t_mv (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.mv = X.t.mv := by
  unfold WX.setNode; split <;> rfl

theorem setNode_t_bufs (X : WX) (bl l : Loc) (r : NRec) :
    (X.setNode bl l r).t.bufs = X.t.bufs := by
  unfold WX.setNode; split <;> rfl

theorem setNode_t_pm (X : WX) (bl l : Loc) (r : NRec) : (X.setNode bl l r).t.pm = X.t.pm := by
  unfold WX.setNode; split <;> rfl

/-- Setting an existing node keeps the objects disjoint. -/
theorem objsDisj_setNode {X : WX} {bl l : Loc} {r : NRec} (hd : objsDisj X.t)
    (hn : X.node bl l = some r) (r' : NRec) : objsDisj (X.setNode bl l r').t := by
  obtain ⟨B, hB, hr⟩ := node_bsQ hn
  unfold WX.setNode; rw [hB]
  exact objsDisj_setNodeT X.t bl l B r r' hd hB hr

/-- An entry of a put's entries is an old one or the put's. -/
theorem mem_wsPutAt {ws : List WEntry} {k : List w8} {e w : WEntry} (h : w ∈ wsPutAt ws k e) :
    w ∈ ws ∨ w = e := by
  unfold wsPutAt at h
  split at h <;>
  · simp only [List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact Or.inl (List.mem_of_mem_take h)
    · exact Or.inr h
    · exact Or.inl (List.mem_of_mem_drop h)

/-- **What a successful `allocate` changes**: the buffer and page-cache entry `id`, the mark (at
the free ids, unchanged; at the mark, past the run). -/
theorem allocRes_basic {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} (h : allocRes X X' fl fl' txid count p id) :
    X'.v.pages = X.v.pages ∧ X'.live = X.live ∧ X'.t.mv.txid' = X.t.mv.txid' ∧
    X'.t.bufs = X.t.bufs.insert id
      (encode (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) ++
        List.replicate (count * 4096 - 16) (W8 0)) ∧
    ((fl.canAlloc id count ∧ fl' = fl.alloc txid id count ∧ X'.t.mv.pgid' = X.t.mv.pgid') ∨
     (id = X.t.mv.pgid' ∧ fl' = fl ∧ id.toNat + count < 2 ^ 62 ∧
       X'.t.mv.pgid'.toNat = id.toNat + count)) := by
  obtain ⟨-, -, Xr, hXr, hX'⟩ := h
  have hR : Xr.v.pages = X.v.pages ∧ Xr.live = X.live ∧ Xr.t.mv = X.t.mv ∧
      Xr.t.bufs = X.t.bufs := by
    rcases hXr with rfl | ⟨Xd, b, hdr, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨(congrArg View.pages hdr.2.1 : Xd.v.pages = X.v.pages), hdr.2.2.1, hdr.2.2.2.2.2.2.1,
        hdr.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨h1, h2, h3, h4⟩ := hR
  rcases hX' with ⟨hc, hf, rfl⟩ | ⟨hid, hf, hlt, rfl⟩
  · refine ⟨h1, h2, by simp only [WX.addPage, h3], by simp only [WX.addPage, h4],
      Or.inl ⟨hc, hf, by simp only [WX.addPage, h3]⟩⟩
  · refine ⟨h1, h2, by simp only [WX.addPage, h3], by simp only [WX.addPage, h4],
      Or.inr ⟨hid, hf, hlt, ?_⟩⟩
    simp only [WX.addPage]; try word

/-- **`allocate`'s page cache**: the page cache with the new buffer's entry. -/
theorem allocRes_pm {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc} {id : w64}
    (h : allocRes X X' fl fl' txid count p id) : X'.t.pm = X.t.pm.insert id p := by
  obtain ⟨-, -, Xr, hXr, hX'⟩ := h
  have hp : Xr.t.pm = X.t.pm := by
    rcases hXr with rfl | ⟨Xd, b, hdr, rfl⟩
    · rfl
    · exact hdr.2.2.2.2.2.2.2.1
  rcases hX' with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> simp only [WX.addPage, hp]

/-- **The spill's global state across an allocation** (the free ids below the mark and no view
pages). -/
theorem spG_alloc {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc} {id : w64}
    {ml ml' : Nat} (h : allocRes X X' fl fl' txid count p id) (hd : objsDisj X.t)
    (hG : spG X txid ml fl) (hml : X'.t.mv.pgid'.toNat * 4096 ≤ ml')
    (hfv : ∀ y ∈ fl.free, X.v.pages !! y.toNat = none)
    (hfl : ∀ y ∈ fl.free, y.toNat < X.t.mv.pgid'.toNat) :
    spG X' txid ml' fl' := by
  have hc0 : 0 < count := h.1
  obtain ⟨hv, -, htx, hbf, hcase⟩ := allocRes_basic h
  have hpm := allocRes_pm h
  have hdr := allocRes_derefPre' X X' fl fl' txid count p id h hd hG.2.2.1 hG.2.2.2.1
    hG.2.2.2.2.1
  obtain ⟨a1, -, -, -, -, a6, a7, a8, a9⟩ := hG
  -- the mark, and the new id's facts
  have hmk : X.t.mv.pgid'.toNat ≤ X'.t.mv.pgid'.toNat ∧ X'.t.mv.pgid'.toNat < 2 ^ 62 ∧
      (∀ y ∈ fl'.free, y ∈ fl.free) ∧
      id.toNat < X'.t.mv.pgid'.toNat ∧ id ∉ fl'.free ∧ X.v.pages !! id.toNat = none := by
    rcases hcase with ⟨hcan, hf, hm⟩ | ⟨hid, hf, hlt, hm⟩
    · have hin : id ∈ fl.free := hcan.2 id (by unfold inRun; omega)
      rw [hm, hf]
      refine ⟨Nat.le_refl _, a7, fun y hy => (List.mem_filter.1 hy).1, hfl id hin, ?_, hfv id hin⟩
      intro hm'
      have := (List.mem_filter.1 hm').2
      simp only [decide_eq_true_eq] at this
      exact this (by unfold inRun; omega)
    · rw [hf, hm]
      have hidn : id.toNat = X.t.mv.pgid'.toNat := by rw [hid]
      refine ⟨by omega, by omega, fun y hy => hy, by omega, fun hm' => ?_, ?_⟩
      · have := hfl id hm'; omega
      · cases e : X.v.pages !! id.toNat with
        | none => rfl
        | some pg => have := a9 _ pg e; omega
  obtain ⟨hle, h62, hfsub, hid1, hid2, hid3⟩ := hmk
  refine ⟨htx.trans a1, hml, hdr.1, hdr.2.1, hdr.2.2, ?_, h62, ?_, ?_⟩
  · intro k
    rw [hpm, hbf]
    by_cases hk : id = k
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ hk, GMap.lookup_insert_ne _ _ hk]; exact a6 k
  · intro k hk
    rw [hbf] at hk
    by_cases he : id = k
    · subst he; rw [hv]; exact ⟨hid1, hid2, hid3⟩
    · rw [GMap.lookup_insert_ne _ _ he] at hk
      obtain ⟨b1, b2, b3⟩ := a8 k hk
      exact ⟨by omega, fun hm => b2 (hfsub k hm), by rw [hv]; exact b3⟩
  · intro y pg hy
    rw [hv] at hy
    have := a9 y pg hy; omega

theorem w0_mem {r : NRec} (h : 0 < r.ws.length) : r.w0 ∈ r.ws := by
  unfold NRec.w0
  cases e : r.ws with
  | nil => rw [e] at h; simp at h
  | cons a l => simp

/-- **The spill's global state across a piece's write** (`pcFin`: the piece's record, its
parent's, the buffer `id` rewritten). -/
theorem spG_pcFin {X2 : WX} {bl l pl : Loc} {ra rp : NRec} {s : GoSlice} {ins : List Inode}
    {id : w64} {count : Nat} {hp : Bool} {txid : w64} {ml : Nat} {fl : FLPg}
    (hG : spG X2 txid ml fl) (hra : X2.node bl l = some ra) (hlv : l ∈ X2.live)
    (hpar : hp = true → X2.node bl pl = some rp ∧ pl ∈ X2.live ∧ pl ≠ l ∧ 0 < ra.ws.length)
    (hbuf : (X2.t.bufs !! id).isSome) :
    spG (pcFin X2 bl l ra pl rp s ins id count hp) txid ml fl := by
  obtain ⟨B, hB, hr⟩ := node_bsQ hra
  obtain ⟨d1, d2, d3, -⟩ := hG.2.2.1.1 bl B l ra hB hr hlv
  obtain ⟨f1, f2⟩ := hG.2.2.2.1 bl B l ra hB hr hlv
  have hY : spG (if hp then (X2.setNode bl l (pcRec ra id true)).setNode bl pl
      (pcPar rp ra id s ins) else X2.setNode bl l (pcRec ra id false)) txid ml fl := by
    cases hp with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact spG_setNode (r' := pcRec ra id false) hra ⟨rfl, rfl⟩ rfl d2 d3 f1 f2 hG
    | true =>
      simp only [ite_true]
      obtain ⟨hrp, hplv, hpl, hne⟩ := hpar rfl
      have hw0 := w0_mem hne
      have hG1 : spG (X2.setNode bl l (pcRec ra id true)) txid ml fl := by
        exact spG_setNode (r' := pcRec ra id true) hra ⟨rfl, rfl⟩ rfl d2 (Or.inr (d2 _ hw0)) f1
          (fun _ => (f1 _ hw0).1) hG
      have hrp1 : (X2.setNode bl l (pcRec ra id true)).node bl pl = some rp := by
        rw [WX.setNode_node_ne _ _ hpl]; exact hrp
      have hplv1 : pl ∈ (X2.setNode bl l (pcRec ra id true)).live := by
        rw [WX.setNode_live]; exact hplv
      obtain ⟨B1, hB1, hr1⟩ := node_bsQ hrp1
      obtain ⟨e1, e2, e3, -⟩ := hG1.2.2.1.1 bl B1 pl rp hB1 hr1 hplv1
      obtain ⟨g1, g2⟩ := hG1.2.2.2.1 bl B1 pl rp hB1 hr1 hplv1
      refine spG_setNode (r' := pcPar rp ra id s ins) hrp1 ⟨rfl, rfl⟩ rfl ?_ e3 ?_ g2 hG1
      · intro w hw
        rcases mem_wsPutAt hw with hw | rfl
        · exact e2 w hw
        · show 0 < ra.w0.key.length
          exact d2 _ hw0
      · intro w hw
        rcases mem_wsPutAt hw with hw | rfl
        · exact g1 w hw
        · exact ⟨(f1 _ hw0).1, by simp [pcEnt]⟩
  unfold pcFin
  refine spG_bufs (X := if hp then (X2.setNode bl l (pcRec ra id true)).setNode bl pl
      (pcPar rp ra id s ins) else X2.setNode bl l (pcRec ra id false)) rfl ?_ hY
  intro k
  have hbk : ∀ Y : WX, Y.t.bufs = X2.t.bufs →
      (((Y.setBuf id (pcPage id ra.nv.isLeaf' ra.ws count)).t.bufs !! k).isSome ↔
        (Y.t.bufs !! k).isSome) := by
    intro Y hYb
    show ((Y.t.bufs.insert id _) !! k).isSome ↔ _
    by_cases hk : id = k
    · subst hk; rw [GMap.lookup_insert, hYb]; simpa using hbuf
    · rw [GMap.lookup_insert_ne _ _ hk]
  apply hbk
  cases hp <;> simp only [Bool.false_eq_true, ite_false, ite_true, setNode_t_bufs]

end g

end Spill

end bbolt
end EtcdGrove
end Perennial
