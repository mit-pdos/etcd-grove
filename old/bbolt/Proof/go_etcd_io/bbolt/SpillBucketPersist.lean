/-
`Bucket.spill`: after a child's spill (which may remap: `dereference` copies every node's bytes
to the heap, `own 1`), the nested buckets' values of a bucket still to be used (`bl`, the
siblings not yet spilled) are made persistent (`own discard`), as `nodeClean` wants
(`spPB`, `bktOwnX_persist`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillBucketSim
public import Proof.go_etcd_io.bbolt.SpillNodeAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- A source made persistent. -/
def spPS : Src → Src
  | .own _ => .own DFrac.discard
  | s => s

open Classical in
/-- A nested bucket's value made persistent. -/
def spPW (w : WEntry) : WEntry := if isBktFlag w.flags then { w with vs := spPS w.vs } else w

def spPR (r : NRec) : NRec := { r with ws := r.ws.map spPW }

def spPB (B : BRec) : BRec := { B with ns := Iris.Std.PartialMap.map spPR B.ns }

theorem spPB_lookup (B : BRec) (l : Loc) : (spPB B).ns !! l = (B.ns !! l).map spPR := by
  show Iris.Std.PartialMap.get? (Iris.Std.PartialMap.map spPR B.ns) l = _
  rw [Iris.Std.LawfulPartialMap.get?_map (M := GMap Loc)]
  rfl

theorem spStrip_PW (w : WEntry) : spStrip (spPW w) = spStrip w := by
  unfold spPW; split <;> rfl

theorem spREq_PR (r : NRec) : spREq r (spPR r) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl⟩
  show (r.ws.map spPW).map spStrip = r.ws.map spStrip
  rw [List.map_map]
  congr 1; funext w; exact spStrip_PW w

theorem spBSim_PB (B : BRec) : spBSim B (spPB B) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun y ry h => ⟨spPR ry, by rw [spPB_lookup, h]; rfl, spREq_PR ry⟩,
    fun y ry' h => ?_⟩
  rw [spPB_lookup] at h
  cases e : B.ns !! y with
  | none => rw [e] at h; cases h
  | some ry => rw [e] at h; cases h; exact ⟨ry, rfl, spREq_PR ry⟩

theorem spPS_live (s : Src) (h : s ≠ Src.stale) : spPS s ≠ Src.stale := by
  cases s <;> simp_all [spPS]

/-- The persisted record's nested buckets' values are persistent, given they are not the view's
or are already. -/
theorem spPW_vs (w : WEntry) (hb : isBktFlag w.flags) (hs : w.vs ≠ Src.stale)
    (hv : w.vs = Src.view → False) : (spPW w).vs = Src.own DFrac.discard := by
  unfold spPW; rw [if_pos hb]
  cases e : w.vs with
  | own _ => rfl
  | view => exact (hv e).elim
  | stale => exact (hs e).elim

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]

theorem srcOwn_persist (W : WView) (s : GoSlice) (src : Src) (bs : List w8) :
    srcOwn (GF := GF) W s src bs ⊢ |==> srcOwn W s (spPS src) bs := by
  cases src with
  | own dq =>
    unfold srcOwn spPS
    iintro H
    iapply ownSlice_persist $$ H
  | view => unfold spPS; iintro H; imodintro; iexact H
  | stale => unfold spPS; iintro H; imodintro; iexact H

theorem wOwn_persist (W : WView) (it : Inode) (w : WEntry) :
    wOwn (GF := GF) W it w ⊢ |==> wOwn W it (spPW w) := by
  unfold spPW
  split
  · unfold wOwn
    iintro ⟨%h, Hk, Hv⟩
    imod (srcOwn_persist W it.value' w.vs w.value) $$ Hv with Hv
    imodintro
    iframe
    ipureintro; exact h
  · iintro H; imodintro; iexact H

theorem wOwns_persist (W : WView) : ∀ (ins : List Inode) (ws : List WEntry),
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) W it w) ⊢
      |==> [∗list] it;w ∈ ins;ws.map spPW, wOwn W it w
  | [], [] => by simp only [List.map_nil]; iintro H; imodintro; iexact H
  | it :: ins, w :: ws => by
    simp only [List.map_cons]
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hw, H⟩
    imod (wOwn_persist W it w) $$ Hw with Hw
    imod (wOwns_persist W ins ws) $$ H with H
    imodintro
    iapply BigSepL2.bigSepL2_cons.2
    iframe
  | [], _ :: _ => by
    iintro H
    ihave %h := BigSepL2.bigSepL2_length $$ H
    simp at h
  | _ :: _, [] => by
    iintro H
    ihave %h := BigSepL2.bigSepL2_length $$ H
    simp at h

theorem nodeOwnX_persist (W : WView) (l : Loc) (r : NRec) :
    nodeOwnX (GF := GF) W l r ⊢ |==> nodeOwnX W l (spPR r) := by
  unfold nodeOwnX spPR
  iintro ⟨Hn, Hins, Hents, Hch, Hcc, Hk⟩
  imod (wOwns_persist W r.ins r.ws) $$ Hents with Hents
  imodintro
  iframe

theorem capOwn_PR (r : NRec) : capOwn (GF := GF) (spPR r) = capOwn r := rfl

theorem spPB_map (B : BRec) (Φ : Loc → NRec → IProp GF) :
    ([∗map] l ↦ r ∈ (spPB B).ns, Φ l r) ⊣⊢ [∗map] l ↦ r ∈ B.ns, Φ l (spPR r) :=
  BiEntails.of_eq (BigSepM.bigSepM_map (M := GMap Loc) (f := spPR) (Φ := Φ) (m := B.ns))

theorem nodesX_persist (W : WView) (B : BRec) :
    ([∗map] l ↦ r ∈ B.ns, nodeOwnX (GF := GF) W l r) ⊢
      |==> [∗map] l ↦ r ∈ (spPB B).ns, nodeOwnX W l r := by
  iintro H
  ihave H := (BigSepM.bigSepM_mono (M := GMap Loc)
    (fun {l r} _ => nodeOwnX_persist (GF := GF) W l r)) $$ H
  imod (BigSepM.bigSepM_bupd (M' := GMap Loc) (fun l r => nodeOwnX (GF := GF) W l (spPR r))) $$ H with H
  imodintro
  iapply (spPB_map B (fun l r => nodeOwnX (GF := GF) W l r)).2
  iexact H

/-- A bucket's nested buckets' values made persistent. -/
theorem bktOwnX_persist (W : WView) (bl : Loc) (B : BRec) (K : Loc → Bool) :
    bktOwnX (GF := GF) W bl B ∗ capsKN K B.ns ⊢ |==> (bktOwnX W bl (spPB B) ∗ capsKN K (spPB B).ns) := by
  iintro ⟨Hb, Hc⟩
  unfold bktOwnX
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
  ihave Hns := (nodesX_persist (GF := GF) W B) $$ Hns
  imod Hns
  imodintro
  have hpo : pageOwn (GF := GF) W (spPB B) = pageOwn W B := rfl
  have hbv : (spPB B).bv = B.bv := rfl
  have hib : (spPB B).ib = B.ib := rfl
  have hnm : (spPB B).nm = B.nm := rfl
  have hbm : (spPB B).bm = B.bm := rfl
  rw [hpo, hbv, hib, hnm, hbm]
  iframe Hbv Hib Hnm Hbm Hpo Hns
  unfold capsKN
  iapply (spPB_map B (fun l r => if K l then iprop(emp) else capOwn (GF := GF) r)).2
  simp only [capOwn_PR]
  iexact Hc

end own

end bbolt
end EtcdGrove
end Perennial
