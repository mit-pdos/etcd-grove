/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__node.lean`: not yet (U7, `notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__node
public import Spec.go_etcd_io.bbolt.Bucket__node
public import Spec.go_etcd_io.bbolt.node__childAt
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Proof.go_etcd_io.bbolt.Write.CurNodeH

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit package_sem in
private theorem wtxW_pkg (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, -⟩, -⟩
  iexact Hpkg

omit [GooseSemantics] [GooseInterp] go_gctx hos hG sem package_sem in
/-- The materialized node's position resolves to it (the root position, or any position of a
file bucket). -/
private theorem nodeAdded_resolve (Y Y' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (h : nodeAdded Y Y' bl l pgid parent) (BY : BRec) (hBY : Y.t.bs !! bl = some BY)
    (hc : parent = null ∨ BY.ib.root' ≠ W64 0) :
    ∃ BY', Y'.t.bs !! bl = some BY' ∧ resolve BY' pgid = some l := by
  obtain ⟨BY0, pa, pg, r, ns', bv', hBY0, -, -, hl0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcase, hX'⟩ := h
  rw [hBY] at hBY0; cases hBY0
  subst hX'
  refine ⟨_, GMap.lookup_insert _ _ _, ?_⟩
  unfold resolve
  simp only
  by_cases hin : BY.ib.root' = W64 0
  · rw [if_pos hin]
    rcases hc with rfl | hc
    · rcases hcase with ⟨-, rfl, -⟩ | ⟨hp, -⟩
      · simp [hl0]
      · exact absurd rfl hp
    · exact absurd hin hc
  · rw [if_neg hin, GMap.lookup_insert]

theorem Cursor.node.wp_proof (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hN : Bucket.node.spec (GF := GF) (hG := hG))
    (hC : node.childAt.spec (GF := GF) (hG := hG)) :
    Cursor.node.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B c stk els pids dq hB hloc hpath hnodes hready
  wp_start as ⟨Hw, Hc, Hs⟩
  icases (persistent_entails_left (wtxW_pkg K tx r m X)) $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hpath' := hpath
  obtain ⟨hne, hlen, hhead, hstep⟩ := hpath
  obtain ⟨eL, heL⟩ : ∃ e, els.getLast? = some e := by
    cases h : els.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some e => exact ⟨e, rfl⟩
  have hn0 : 0 < els.length := List.length_pos_iff.2 hne
  have heL' : els[els.length - 1]? = some eL := by rw [← List.getLast?_eq_getElem?]; exact heL
  obtain ⟨pL, hpL'⟩ : ∃ p, pids[els.length - 1]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hpL : pids.getLast? = some pL := by
    rw [List.getLast?_eq_getElem?, hlen]; exact hpL'
  obtain ⟨hrefL, lfL, wsL, hltL, -, hleafL⟩ := hstep _ eL pL heL' hpL'
  have hlfL := hleafL (by omega)
  subst hlfL
  have hidx : sint.Z (stk.len - W64 1) = ((els.length - 1 : Nat) : Int) := by word
  icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcn⟩
  iStructNamed Hc
  wp_auto
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z stk.len by word)]
  wp_apply hA
  try wp_auto
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) eL _ _ els (by omega)
    (by rw [hidx]; simpa using heL') $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  rw [if_pos (by word)]
  icases typedPointsto_not_null_dup _ _ _ $$ He with ⟨He, %Hen⟩
  iStructNamed He
  wp_auto
  obtain ⟨B0, hB0, hrefL⟩ := hrefL
  rw [hB] at hB0; cases hB0
  have hcB : bktClean X.v X.t.mv.pgid'.toNat bl B := by
    obtain ⟨-, B1, hB1, hc1, -⟩ := hloc; rw [hB] at hB1; cases hB1; exact hc1
  by_cases hnL : eL.node' = null
  · rw [decide_eq_true hnL]
    wp_auto
    ihave He : (sliceIndexRef elemRef (((els.length - 1 : Nat) : Int)) stk ↦{dq} eL : IProp GF) $$ [page node index]
    · iapply typedPointsto_combine _ _ _ Hen
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hs := Hsback $$ He
    rw [list_set_lookup_self _ _ _ (by simpa using heL')]
    obtain ⟨e0, he0⟩ : ∃ e, els[0]? = some e := ⟨_, List.getElem?_eq_getElem hn0⟩
    obtain ⟨p0, hp0⟩ : ∃ p, pids[0]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hp0r : p0 = B.ib.root' := by
      rw [List.head?_eq_getElem?, hp0] at hhead
      cases hhead; simp [WX.rootPid, hB]
    obtain ⟨href0, -⟩ := hstep 0 e0 p0 he0 hp0
    obtain ⟨B0, hB0, href0⟩ := href0
    rw [hB] at hB0; cases hB0
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z stk.len by
      constructor <;> word)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) e0 _ _ els (by decide) (by simpa using he0) $$ Hs
      with ⟨He0, Hs0back⟩
    icases typedPointsto_not_null_dup _ _ _ $$ He0 with ⟨He0, %He0n⟩
    iStructNamed He0
    wp_auto
    have hrn0 : ∀ l, resolve B p0 = some l → l ≠ null := by
      intro l hl
      obtain ⟨c0, hc0⟩ := Write.resolve_some_nm _ _ bl B hcB p0 l hl
      exact (hcB.2.2.2.2.1 c0 l hc0).1
    wp_join iprop(∃ (n0 : Loc) (Y : WX), n_ptr ↦ n0 ∗ c_ptr ↦ c ∗ wtxW K tx r m Y ∗
        (sliceIndexRef elemRef (sint.Z (W64 0)) stk).[elemRef, go!"page"] ↦{dq} e0.page' ∗
        (sliceIndexRef elemRef (sint.Z (W64 0)) stk).[elemRef, go!"node"] ↦{dq} e0.node' ∗
        (sliceIndexRef elemRef (sint.Z (W64 0)) stk).[elemRef, go!"index"] ↦{dq} e0.index' ∗
        c.[Cursor, go!"bucket"] ↦{dq} bl ∗ c.[Cursor, go!"stack"] ↦{dq} stk ∗
        ⌜Write.curSt X Y bl B ∧ ∃ BY, Y.t.bs !! bl = some BY ∧ BY.nm !! p0 = some n0 ∧
          resolve BY p0 = some n0⌝)
      at next with [n c Hw page node index bucket stack]
      as ⟨%n0, %Y, n, c, Hw, page, node, index, bucket, stack, %Hj⟩
    · by_cases hn0n : e0.node' = null
      · rw [decide_eq_true hn0n]
        have hres0 : resolve B p0 = none := by
          cases h : resolve B p0 with
          | none => rfl
          | some l => rw [h] at href0; exact absurd (href0 ▸ hn0n) (hrn0 l h)
        rw [hres0] at href0
        obtain ⟨-, pg, hwp0⟩ := href0
        have hmr := hready p0 (List.mem_of_getElem? hp0) hres0
        obtain ⟨pa, pg', hwp', hrd, -, -, hid, -, hsrc, hpa, -⟩ := hmr
        rw [hwp0] at hwp'
        simp only [Option.some.injEq, Prod.mk.injEq] at hwp'
        obtain ⟨rfl, rfl⟩ := hwp'
        have h16 : 16 ≤ pg.length := by have := hrd.1; unfold elemOff at this; omega
        wp_auto
        rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z stk.len by
          constructor <;> word)]
        wp_auto
        icases Write.wtxW_hdr_acc K tx r m X bl B p0 e0.page' pg hB hloc.1 hwp0 hsrc hpa h16 $$ Hw
          with ⟨%dqh, Hh, Hhb⟩
        wp_apply hId e0.page' (pageHdr pg) dqh $$ [Hh] as Hh
        · iexact Hh
        ihave Hw := Hhb $$ Hh
        rw [show (decode (List.take 8 (bytesAt pg 0 16)) : w64) = p0 from hid]
        have hrootnull := Write.resolve_root_none _ _ bl B hcB (hp0r ▸ hres0)
        have hnm0 : B.nm !! p0 = none := by
          by_cases hin : B.ib.root' = W64 0
          · rw [((hcB.2.2.1) hrootnull).2]; simp
          · rw [← Write.resolve_file B hin]; exact hres0
        wp_apply hN K tx r m X bl B p0 null hB hloc.1 hnodes (fun l h => (hcB.2.2.2.2.1 _ l h).1)
          (fun _ => ⟨hready p0 (List.mem_of_getElem? hp0) hres0, Or.inl rfl⟩) $$ [Hw]
          as %l ⟨%X', Hw, %Hpost⟩
        · iexact Hw
        try wp_auto
        have hadd : nodeAdded X X' bl l p0 null := by
          rcases Hpost with ⟨h1, -⟩ | h
          · rw [hnm0] at h1; cases h1
          · exact h
        have hpos : matPos X bl p0 null := ⟨B, hB, Or.inl ⟨rfl, hrootnull, hp0r⟩⟩
        obtain ⟨hst', BY', hBY', hnmY'⟩ := Write.curSt_step X X X' bl l p0 null B
          (Write.curSt_refl X bl B hloc hB) hadd hpos
          (fun BY hBY _ => by rw [hB] at hBY; cases hBY; exact hrootnull)
        obtain ⟨BY'', hBY'', hresY⟩ := nodeAdded_resolve X X' bl l p0 null hadd B hB (Or.inl rfl)
        rw [hBY'] at hBY''; cases hBY''
        wp_join_done
        iexists l, X'
        iframe
        ipureintro
        exact ⟨hst', BY', hBY', hnmY', hresY⟩
      · rw [decide_eq_false hn0n]
        have hres0 : resolve B p0 = some e0.node' := by
          cases h : resolve B p0 with
          | none => rw [h] at href0; exact absurd href0.1 hn0n
          | some l => rw [h] at href0; rw [href0]
        wp_auto
        wp_join_done
        iexists e0.node', X
        iframe
        ipureintro
        exact ⟨Write.curSt_refl X bl B hloc hB, B, hB,
          Write.resolve_root_nm _ _ bl B hcB _ (hp0r ▸ hres0) |> (hp0r ▸ ·), hres0⟩
    sorry
  · rw [decide_eq_false hnL]
    obtain ⟨l, hresL⟩ : ∃ l, resolve B pL = some l := by
      cases h : resolve B pL with
      | none => rw [h] at hrefL; exact absurd hrefL.1 hnL
      | some l => exact ⟨l, rfl⟩
    rw [hresL] at hrefL
    obtain ⟨cL, hcL⟩ := Write.resolve_some_nm _ _ bl B hcB pL l hresL
    obtain ⟨-, rn, hrn, -⟩ := hcB.2.2.2.2.1 cL l hcL
    have hrnL : rn.nv.isLeaf' = true := by
      unfold ltree at hltL; rw [hB] at hltL; simp only [hresL, hrn, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at hltL
      exact hltL.1
    subst hrefL
    wp_auto
    wp_method_call; wp_call
    icases Write.wtxW_node_ptr_acc K tx r m X bl B eL.node' rn hB hrn $$ Hw with ⟨Hn, Hwb⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_auto
    rw [decide_eq_false hnL]
    wp_auto
    rw [hrnL]
    wp_auto
    ihave Hn : (eL.node' ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      rw [hrnL]
      iframe
    ihave Hw := Hwb $$ Hn
    ihave He : (sliceIndexRef elemRef (((els.length - 1 : Nat) : Int)) stk ↦{dq} eL : IProp GF) $$ [page node index]
    · iapply typedPointsto_combine _ _ _ Hen
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hs := Hsback $$ He
    rw [list_set_lookup_self _ _ _ (by simpa using heL')]
    ihave Hc : (c ↦{dq} Cursor.mk bl stk : IProp GF) $$ [bucket stack]
    · iapply typedPointsto_combine _ _ _ Hcn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iexists X
    iframe
    ipureintro
    exact ⟨matGrow.refl X bl, id, B, pL, hB, hpL, hresL⟩

end proof

end bbolt
end EtcdGrove
end Perennial
