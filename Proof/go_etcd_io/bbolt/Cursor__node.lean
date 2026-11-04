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

/-- `iStructNamed` without the anonymous end-of-fields hypothesis (which `wp_for`'s frame cannot
name): split `H` and destructure it with `pat`. -/
local macro "iStructSplit " H:ident " as " pat:icasesPat : tactic =>
  `(tactic| (
    icases typedPointsto_split _ _ _ $$ $H:ident with $H:ident
    try simp only [TypedPointsto.typedPointstoDef]
    icases $H:ident with $pat))

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

omit [GooseSemantics] [GooseInterp] go_gctx hos hG sem package_sem in
/-- The node at a resolved, cached position of the loop's state: a live node of `bl`, its
logical data `X`'s at that position. -/
private theorem curSt_node (X Y : WX) (bl : Loc) (B BY : BRec) (h : Write.curSt X Y bl B)
    (hBY : Y.t.bs !! bl = some BY) (pk : w64) (nk : Loc) (hpk : BY.nm !! pk = some nk)
    (hres : resolve BY pk = some nk) (hpk0 : B.ib.root' = W64 0 → pk = W64 0) :
    ∃ rk, BY.ns !! nk = some rk ∧ rk.nv.bucket' = bl ∧ nk ∈ Y.live ∧
      Write.ldat (ltree X bl pk) = some (rk.nv.isLeaf', rk.ws.map wDat) := by
  obtain ⟨-, -, -, -, -, BY0, hBY0, -, -, -, -, -, -, -, hnm, hld⟩ := h
  rw [hBY] at hBY0; cases hBY0
  obtain ⟨-, rk, hrk, hb, hl⟩ := hnm pk nk hpk
  refine ⟨rk, hrk, hb, hl, ?_⟩
  rw [← hld pk hpk0]
  unfold ltree; rw [hBY]; simp [hres, hrk, Write.ldat]

omit [GooseExts] in
private theorem ldat_some_eq {a b : Bool} {ws1 : List WEntry} {ws2 : List (w32 × w64 × List w8 × List w8)}
    {x : Option (Bool × List WEntry)} (hx : x = some (b, ws1))
    (h : Write.ldat x = some (a, ws2)) : b = a ∧ ws1.map wDat = ws2 := by
  subst hx; simp only [Write.ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; exact h

omit [GooseExts] in
private theorem wDat_at {ws1 ws2 : List WEntry} (h : ws1.map wDat = ws2.map wDat) (i : Nat) (w2 : WEntry)
    (h2 : ws2[i]? = some w2) : ∃ w1, ws1[i]? = some w1 ∧ w1.pgid = w2.pgid := by
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, h2, Option.map_some] at e
  obtain ⟨w1, hw1, e1⟩ := Option.map_eq_some_iff.1 e
  exact ⟨w1, hw1, congrArg (fun d => d.2.1) e1⟩

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
  iStructSplit Hc as ⟨bucket, stack, -⟩
  wp_auto
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z stk.len by word)]
  wp_apply hA
  try wp_auto
  icases ownSlice_elem_acc (sint.Z (stk.len - W64 1)) eL _ _ els (by omega)
    (by rw [hidx]; simpa using heL') $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  rw [if_pos (by word)]
  icases typedPointsto_not_null_dup _ _ _ $$ He with ⟨He, %Hen⟩
  iStructSplit He as ⟨page, node, index, -⟩
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
    iStructSplit He0 as ⟨page, node, index, -⟩
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
    ihave He0 : (sliceIndexRef elemRef (sint.Z (W64 0)) stk ↦{dq} e0 : IProp GF) $$ [page node index]
    · iapply typedPointsto_combine _ _ _ He0n
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hs := Hs0back $$ He0
    rw [list_set_lookup_self _ _ _ (by simpa using he0)]
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
    try wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (stk.len - W64 1) ∧
      sint.Z (stk.len - W64 1) ≤ sint.Z stk.cap by refine ⟨by decide, by word, by word⟩)]
    icases (ownSlice_split_all (stk.len - W64 1) stk _ els ⟨by word, by word⟩).1 $$ Hs
      with ⟨Hpre, Hsuf⟩
    ihave %Hprel := ownSlice_len _ _ _ $$ Hpre
    wp_auto
    ihave IH : (∃ (j : w64) (nk : Loc) (Yj : WX) (rv : elemRef),
        "i" ∷ i_ptr ↦ j ∗ "ref" ∷ ref_ptr ↦ rv ∗ "n" ∷ n_ptr ↦ nk ∗ "Hw" ∷ wtxW K tx r m Yj ∗
        "Hpre" ∷ slice.slice stk elemRef (W64 0) (stk.len - W64 1) ↦*{dq}
          List.take (sint.nat (stk.len - W64 1)) els ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z (stk.len - W64 1) ∧ Write.curSt X Yj bl B ∧
          ∃ BY pk, Yj.t.bs !! bl = some BY ∧ pids[sint.nat j]? = some pk ∧ BY.nm !! pk = some nk ∧
            resolve BY pk = some nk⌝ : IProp GF) $$ [i ref n Hw Hpre]
    · iexists W64 0, n0, Y, zero_val elemRef
      simp only [named]
      iframe
      ipureintro
      obtain ⟨hst, BY, hBY, hnm, hres⟩ := Hj
      exact ⟨by decide, by word, hst, BY, p0, hBY, by rw [show sint.nat (W64 0) = 0 from rfl]; exact hp0,
        hnm, hres⟩
    wp_for IH
    wp_if_destruct
    · obtain ⟨Hj0, Hjk, hst, BY, pk, hBY, hpk, hnm, hres⟩ := Hj
      have Hlt : sint.Z j < sint.Z (stk.len - W64 1) := by word
      have hjl : sint.nat j + 1 < els.length := by word
      obtain ⟨ej, hej⟩ : ∃ e, els[sint.nat j]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨-, lf, ws, hlt, hbr, -⟩ := hstep _ ej pk hej hpk
      obtain ⟨hlf, w0, hw0, hpk1⟩ := hbr hjl
      subst hlf
      have hin : B.ib.root' ≠ W64 0 := fun h0 => by
        have := Write.ltree_inline_leaf X _ bl B hB hcB h0 pk false ws hlt; cases this
      obtain ⟨rk, hrk, hrkb, hrkl, hld⟩ := curSt_node X Yj bl B BY hst hBY pk nk hnm hres
        (fun h => absurd h hin)
      obtain ⟨hleafk, hwsk⟩ := ldat_some_eq hlt hld
      obtain ⟨w, hw, hwp⟩ := wDat_at hwsk.symm _ w0 hw0
      have htk : (List.take (sint.nat (stk.len - W64 1)) els)[(sint.Z j).toNat]? = some ej := by
        rw [List.getElem?_take_of_lt (by word)]; exact hej
      rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (stk.len - W64 1 - W64 0) by
        constructor <;> word)]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ ej Hj0 $$ [Hpre] as Hpre
      · iframe; ipureintro; exact htk
      try wp_auto
      icases Write.wtxW_node_len K tx r m Yj bl BY nk rk hBY hrk hrkl $$ Hw with ⟨Hw, %Hwl⟩
      icases Write.wtxW_node_ptr_acc K tx r m Yj bl BY nk rk hBY hrk $$ Hw with ⟨Hn, Hwb⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
      iStructSplit Hn as ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, -⟩
      wp_auto
      rw [← hleafk]
      wp_apply hA
      try wp_auto
      ihave Hn : (nk ↦ rk.nv : IProp GF) $$ [n1 n2 n3 n4 n5 n6 n7 n8 n9]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [← hleafk]
        iframe
      ihave Hw := Hwb $$ Hn
      icases typedPointsto_not_null_dup _ _ _ $$ ref with ⟨ref, %Hrn⟩
      iStructSplit ref as ⟨r1, r2, r3, -⟩
      try wp_auto
      have hidx : ej.index'.toNat < rk.ws.length := (List.getElem?_eq_some_iff.1 hw).1
      have hi0 : 0 ≤ sint.Z ej.index' := by word
      have hin' : sint.nat ej.index' = ej.index'.toNat := by word
      obtain ⟨-, -, -, -, hbll, BY0, hBY0, hib, hnd, -, -, -, -, hnmB, hnmok, -⟩ := id hst
      rw [hBY] at hBY0; cases hBY0
      have hnone : BY.nm !! w.pgid = none → matReady Yj BY w.pgid := by
        intro hn
        have hresB : resolve B w.pgid = none := by
          rw [Write.resolve_file B hin]
          cases h : B.nm !! w.pgid with
          | none => rfl
          | some l0 => rw [hnmB _ _ h] at hn; cases hn
        refine Write.curSt_ready X Yj bl B BY hst hBY w.pgid
          (hready w.pgid (List.mem_of_getElem? (hwp ▸ hpk1)) hresB)
      ihave ref : (ref_ptr ↦ ej : IProp GF) $$ [r1 r2 r3]
      · iapply typedPointsto_combine _ _ _ Hrn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_apply hC K tx r m Yj bl BY nk rk ej.index' w hBY hrk hrkb hleafk.symm hrkl hbll
        (by rw [hnd]; exact hnodes) hi0 (by rw [hin']; exact hw)
        (fun l h => (hnmok _ l h).1) hnone $$ [Hw] as %l ⟨%Y', Hw, %Hpost⟩
      · iexact Hw
      try wp_auto
      -- the next state
      have hnext : Write.curSt X Y' bl B ∧ ∃ BY', Y'.t.bs !! bl = some BY' ∧
          BY'.nm !! w.pgid = some l ∧ resolve BY' w.pgid = some l := by
        rcases Hpost with ⟨h1, rfl⟩ | hadd
        · exact ⟨hst, BY, hBY, h1, by rw [Write.resolve_file BY (by rw [hib]; exact hin)]; exact h1⟩
        · have hnm0 : BY.nm !! w.pgid = none := by
            obtain ⟨BY0, -, -, -, -, -, hBY0, -, h0, -⟩ := id hadd
            rw [hBY] at hBY0; cases hBY0; exact h0
          have hpos : matPos Yj bl w.pgid nk :=
            ⟨BY, hBY, Or.inr ⟨ej.index'.toNat, rk, w, hrk, hleafk.symm, hw, rfl, hnm0⟩⟩
          obtain ⟨hst', BY', hBY', hnmY'⟩ := Write.curSt_step X Yj Y' bl l w.pgid nk B hst hadd hpos
            (fun BY1 hBY1 h0 => absurd (by rw [hBY] at hBY1; cases hBY1; rw [hib] at h0; exact h0) hin)
          obtain ⟨BY'', hBY'', hresY⟩ := nodeAdded_resolve Yj Y' bl l w.pgid nk hadd BY hBY
            (Or.inr (by rw [hib]; exact hin))
          rw [hBY'] at hBY''; cases hBY''
          exact ⟨hst', BY', hBY', hnmY', hresY⟩
      wp_for_post
      iframe
      iexists j + W64 1, l, Y', ej
      iframe
      ipureintro
      obtain ⟨hst', BY', hBY', hnmY', hresY⟩ := hnext
      refine ⟨by word, by word, hst', BY', w.pgid, hBY', ?_, hnmY', hresY⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, hwp]; exact hpk1
    · obtain ⟨Hj0, Hjk, hst, BY, pk, hBY, hpk, hnm, hres⟩ := Hj
      have hje : sint.nat j = els.length - 1 := by word
      rw [hje, hpL'] at hpk
      cases hpk
      have hpk0 : B.ib.root' = W64 0 → pL = W64 0 := by
        intro h0
        by_cases h1 : els.length = 1
        · rw [h1] at hpL'
          have e : some pL = some p0 := by rw [← hp0]; exact hpL'.symm
          cases e
          exact hp0r.trans h0
        · obtain ⟨-, lf0, ws0, hlt0, hbr0, -⟩ := hstep 0 e0 p0 he0 hp0
          obtain ⟨hlf0, -⟩ := hbr0 (by omega)
          subst hlf0
          have := Write.ltree_inline_leaf X _ bl B hB hcB h0 p0 false ws0 hlt0; cases this
      obtain ⟨rk, hrk, -, -, hld⟩ := curSt_node X Yj bl B BY hst hBY pL nk hnm hres hpk0
      obtain ⟨hleafk, -⟩ := ldat_some_eq hltL hld
      icases Write.wtxW_node_ptr_acc K tx r m Yj bl BY nk rk hBY hrk $$ Hw with ⟨Hn, Hwb⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
      iStructSplit Hn as ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, -⟩
      wp_auto
      rw [← hleafk]
      wp_apply hA
      try wp_auto
      ihave Hn : (nk ↦ rk.nv : IProp GF) $$ [n1 n2 n3 n4 n5 n6 n7 n8 n9]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [← hleafk]
        iframe
      ihave Hw := Hwb $$ Hn
      ihave Hs := (ownSlice_split_all (stk.len - W64 1) stk _ els ⟨by word, by word⟩).2 $$ [Hpre Hsuf]
      · iframe
      ihave Hc : (c ↦{dq} Cursor.mk bl stk : IProp GF) $$ [bucket stack]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iapply HΦ
      iexists Yj
      iframe
      ipureintro
      exact ⟨hst.1, hst.2.1, BY, pL, hBY, hpL, hres⟩
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
