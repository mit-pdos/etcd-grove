/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__seek_w.lean` (U6d, `notes/bbolt-proof-plan.md`): the
stack emptied (`c.stack[:0]`), `search` from the bucket's root (`Cursor.search_w`), then `keyValue`
at the stack's leaf (`Cursor.keyValue_w`).

The shared statement `Cursor.seek_w.spec` is not provable as stated (U6d's report):
- `tx.page` returns the page cache's buffer for an id in `tx.pages`: a view position's page is
  the view's only if no view page is cached (`pmFresh`, which `bktLocalOK` does not give; `wOK`'s
  `txClean` does: `pm = ∅`);
- an inline bucket's page bytes are owned only if its `page` field's status matches its source
  (`inlSrcOK`; `bktClean` allows `isrc = .view` with `pst = .none`, whose bytes nobody owns);
- an inline page's entries are its bytes', of source `B.isrc` (`leafSrc`), while `ltree` gives
  every page entry `.view` sources, false for an owned inline page (a bucket created in this
  transaction).
Batch 33: `Cursor.seek_w.spec` is the corrected statement (`pmFresh X`; `inlSrcOK X bl` from
`bktLocalOK`, by `bktClean`'s inline clause, `inlSrcOK_of_bktLocalOK`; the returned sources
`leafSrc`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Cursor__search_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_w
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.Write.CurNodeH
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
public import Proof.go_etcd_io.bbolt.Read.WQ

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The entries at a searchable position are fewer than `2^63`. -/
theorem wtxW_ltree_len (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (p : w64) (lf : Bool) (ws : List WEntry) (hB : X.t.bs !! bl = some B) (hloc : bktLocalOK X bl)
    (hl : ltree X bl p = some (lf, ws)) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ ⌜ws.length < 2 ^ 63⌝ := by
  obtain ⟨-, B0, hB0, -, -, -, hnsl, -⟩ := hloc
  rw [hB] at hB0; cases hB0
  cases hr : resolve B p with
  | none =>
    cases hw : wpageAt X.v B p with
    | none => simp [ltree, hB, hr, hw] at hl
    | some lp =>
      simp only [ltree, hB, hr, hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      iintro H; iframe; ipureintro
      rw [pageWs_length]
      have : pageCount lp.2 < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      omega
  | some l =>
    cases hn : B.ns !! l with
    | none => simp [ltree, hB, hr, hn] at hl
    | some rn =>
      simp only [ltree, hB, hr, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      exact Write.wtxW_node_len K tx r m X bl B l rn hB hn (hnsl l rn hn)

/-- The entries at a searchable position are fewer than `2^63`. -/
theorem wtxWQ_ltree_len (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc) (B : BRec)
    (p : w64) (lf : Bool) (ws : List WEntry) (hB : X.t.bs !! bl = some B) (hloc : bktLocalOK X bl)
    (hl : ltree X bl p = some (lf, ws)) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ ⌜ws.length < 2 ^ 63⌝ := by
  obtain ⟨-, B0, hB0, -, -, -, hnsl, -⟩ := hloc
  rw [hB] at hB0; cases hB0
  cases hr : resolve B p with
  | none =>
    cases hw : wpageAt X.v B p with
    | none => simp [ltree, hB, hr, hw] at hl
    | some lp =>
      simp only [ltree, hB, hr, hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      iintro H; iframe; ipureintro
      rw [pageWs_length]
      have : pageCount lp.2 < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      omega
  | some l =>
    cases hn : B.ns !! l with
    | none => simp [ltree, hB, hr, hn] at hl
    | some rn =>
      simp only [ltree, hB, hr, hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨-, rfl⟩ := hl
      exact wtxWQ_node_len K tx r m q X bl B l rn hB hn (hnsl l rn hn)

theorem Cursor.seek_w.wp_proofQ
    (hsw : Cursor.search_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_w.specQ (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Cursor.seek_w.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X bl c stk els0 key kb kr hloc hpm
  have hinl := inlSrcOK_of_bktLocalOK X bl hloc
  wp_start as ⟨Hw, Hc, Hs, Hcap, Hkey⟩
  obtain ⟨hlive, B, hB, -⟩ := id hloc
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  rw [if_pos ⟨by decide, by decide, by word⟩]
  icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 0) stk els0
    ⟨by decide, by decide, by word⟩ $$ [Hs Hcap] with ⟨-, Hs, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) els0 = ([] : List elemRef) := by
    simp [subslice]
  rw [hsub]
  wp_auto
  wp_method_call; wp_call
  icases wtxWQ_bkt_acc K tx r m q X bl B hB $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iexact Hib
  ihave Hw := Hback $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · isimp only [objOwn]; iframe
  wp_apply hsw K tx r m q X bl B c _ [] B.ib.root' key kr kb hB hloc hpm hinl
    (posOK_root X bl B hloc hB) (fun h => h) $$ [Hw Hc Hs Hcap Hkey]
    as ⟨%stk', %path, %pids, Hw, Hc, Hs, Hcap, Hkey, %Hrt⟩
  · iframe
  obtain ⟨Hp, Hr, Hpos⟩ := Hrt
  simp only [List.nil_append]
  obtain ⟨hne, hlen, hhd, hall⟩ := Hp
  obtain ⟨els', e, rfl⟩ : ∃ els' e, path = els' ++ [e] :=
    ⟨path.dropLast, path.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  obtain ⟨p, hp⟩ : ∃ p, pids[els'.length]? = some p := by
    cases h : pids[els'.length]? with
    | none => rw [List.getElem?_eq_none_iff] at h; simp at hlen; omega
    | some p => exact ⟨p, rfl⟩
  have he : (els' ++ [e])[els'.length]? = some e := by simp
  obtain ⟨hra, lf, ws, hlt, -, hlf⟩ := hall els'.length e p he hp
  have hlf' := hlf (by simp)
  subst hlf'
  have hlast : pids.getLast? = some p := by
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_append, List.length_singleton] at hlen
    rw [hlen]; simpa using hp
  have hleaf : lLeaf X bl pids = ws := by unfold lLeaf; rw [hlast]; simp only [hlt]
  have hidx := (Hr els'.length e p true ws he hp hlt).2 rfl
  have hpp : posOK X bl B p := Hpos p (List.mem_of_getElem? hp)
  icases wtxWQ_ltree_len K tx r m q X bl B p true ws hB hloc hlt $$ Hw with ⟨Hw, %Hwl⟩
  have hix : wsIdx ws kb ≤ ws.length := by unfold wsIdx; exact (List.takeWhile_sublist _).length_le
  have hsi : sint.Z e.index' = (wsIdx ws kb : Int) := by
    have := hidx; rw [← this]; word
  wp_apply hkv K tx r m q X bl B c stk' els' e p ws hB hloc hpm hinl hpp hra hlt (by omega)
    $$ [Hw Hc Hs] as %k %vl %fl ⟨Hw, Hc, Hs, Hkv⟩
  · iframe
  try wp_auto
  iapply HΦ
  iexists stk', els' ++ [e], pids
  iframe
  isplitr
  · ipureintro
    exact ⟨⟨hne, hlen, by rw [hhd]; simp [WX.rootPid, hB], hall⟩, Hr⟩
  rw [hleaf, show (sint.Z e.index').toNat = wsIdx ws kb by omega]
  unfold wKV
  iexact Hkv

/-- `seek` over the whole writer (`q = 1`). -/
theorem Cursor.seek_w.wp_proof
    (hsw : Cursor.search_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_w.specQ (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Cursor.seek_w.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl c stk els0 key kb kr hloc hpm
  have h := Cursor.seek_w.wp_proofQ hsw hkv hRP K tx r m 1 X bl c stk els0 key kb kr hloc hpm
  simp only [wtxWQ_one] at h
  exact h

end proof

end bbolt
end EtcdGrove
end Perennial
