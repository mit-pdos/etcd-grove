/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/ConsensusObj__Unmarshal.lean`, run `rabia-r1wake-1`.)

`(*ConsensusObj).Unmarshal` (message.pb.go 1117-1426): decoding `encObj o` into a zero
`ConsensusObj` (prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.Internal
public import Dsverify.Proof.rabia.internal.message.ObjWire
public import Dsverify.Proof.rabia.internal.message.VarintTac

@[expose] public section

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

/-- A `ConsensusObj` being decoded: `objRep` with owned slices and their capacities. -/
noncomputable def objOwn (v : ConsensusObj) (o : ObjV) : IProp GF :=
  iprop(⌜v.ProId' = o.proId ∧ v.ProSeq' = o.proSeq ∧ v.SvrSeq' = o.svrSeq ∧ v.IsNull' = o.isNull⌝ ∗
    v.CliIds' ↦* o.cliIds ∗ ownSliceCap w32 v.CliIds' (DFrac.own 1) ∗
    v.CliSeqs' ↦* o.cliSeqs ∗ ownSliceCap w32 v.CliSeqs' (DFrac.own 1) ∗
    v.Commands' ↦* o.commands ∗ ownSliceCap GoString v.Commands' (DFrac.own 1))

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem objOwn_open (v : ConsensusObj) (o : ObjV) : objOwn (GF := GF) v o ⊢
    ⌜v.ProId' = o.proId ∧ v.ProSeq' = o.proSeq ∧ v.SvrSeq' = o.svrSeq ∧ v.IsNull' = o.isNull⌝ ∗
    v.CliIds' ↦* o.cliIds ∗ ownSliceCap w32 v.CliIds' (DFrac.own 1) ∗
    v.CliSeqs' ↦* o.cliSeqs ∗ ownSliceCap w32 v.CliSeqs' (DFrac.own 1) ∗
    v.Commands' ↦* o.commands ∗ ownSliceCap GoString v.Commands' (DFrac.own 1) := by
  unfold objOwn; exact .rfl

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem objOwn_close (v : ConsensusObj) (o : ObjV) :
    ⌜v.ProId' = o.proId ∧ v.ProSeq' = o.proSeq ∧ v.SvrSeq' = o.svrSeq ∧ v.IsNull' = o.isNull⌝ ∗
    v.CliIds' ↦* o.cliIds ∗ ownSliceCap w32 v.CliIds' (DFrac.own 1) ∗
    v.CliSeqs' ↦* o.cliSeqs ∗ ownSliceCap w32 v.CliSeqs' (DFrac.own 1) ∗
    v.Commands' ↦* o.commands ∗ ownSliceCap GoString v.Commands' (DFrac.own 1) ⊢
    objOwn (GF := GF) v o := by
  unfold objOwn; exact .rfl

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem objOwn_congr (v v' : ConsensusObj) (o1 o2 : ObjV)
    (hs : v'.CliIds' = v.CliIds' ∧ v'.CliSeqs' = v.CliSeqs' ∧ v'.Commands' = v.Commands')
    (hl : o2.cliIds = o1.cliIds ∧ o2.cliSeqs = o1.cliSeqs ∧ o2.commands = o1.commands)
    (hp : v.ProId' = o1.proId ∧ v.ProSeq' = o1.proSeq ∧ v.SvrSeq' = o1.svrSeq ∧
        v.IsNull' = o1.isNull →
      v'.ProId' = o2.proId ∧ v'.ProSeq' = o2.proSeq ∧ v'.SvrSeq' = o2.svrSeq ∧
        v'.IsNull' = o2.isNull) :
    objOwn (GF := GF) v o1 ⊢ objOwn v' o2 := by
  unfold objOwn
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨h4, h5, h6⟩ := hl
  rw [h1, h2, h3, h4, h5, h6]
  iintro ⟨%H, H2⟩
  iframe
  ipureintro; exact hp H

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem objOwn_zero (o : ObjV) : ⊢ objOwn (GF := GF) (zeroValDef : ConsensusObj) (o.upto 0) := by
  unfold objOwn
  simp only [ObjV.upto, Nat.not_lt_zero, ite_false, Nat.zero_sub, List.take_zero]
  iintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  isplitr; · iapply ownSlice_nil
  isplitr; · iapply ownSliceCap_nil
  isplitr; · iapply ownSlice_nil
  isplitr; · iapply ownSliceCap_nil
  isplitr; · iapply ownSlice_nil
  iapply ownSliceCap_nil

omit [GooseExts] in
theorem w32_ofNat_toNat' (x : w32) : BitVec.ofNat 32 x.toNat = x := by simp

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem objOwn_persist (v : ConsensusObj) (o : ObjV) : objOwn (GF := GF) v o ⊢ |==> objRep v o := by
  unfold objOwn objRep
  iintro ⟨%H, H1, -, H2, -, H3, -⟩
  imod ownSlice_persist _ _ _ $$ H1 with H1
  imod ownSlice_persist _ _ _ $$ H2 with H2
  imod ownSlice_persist _ _ _ $$ H3 with H3
  imodintro
  iframe
  ipureintro; exact H

omit [GooseExts] in
theorem subslice_of_drop' {A : Type} (a : Nat) (l X Y : List A) (h : l.drop a = X ++ Y) :
    subslice a (a + X.length) l = X := by
  rw [subslice_comm, h, Nat.add_sub_cancel_left, List.take_left]

set_option maxHeartbeats 4000000 in
theorem ConsensusObj.Unmarshal.wp_proof : ConsensusObj.Unmarshal.spec (GF := GF) := by
  intro l sl dq o
  wp_start as ⟨Hl, Hsl⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave HI : (∃ (s : Nat) (v : ConsensusObj) (idx : w64),
      "Hl" ∷ l ↦ v ∗ "Hown" ∷ objOwn v (o.upto s) ∗ "iNdEx" ∷ iNdEx_ptr ↦ idx ∗
      "%Hs" ∷ ⌜s ≤ 6 + o.commands.length ∧ 0 ≤ sint.Z idx ∧ sint.nat idx ≤ (encObj o).length ∧
        (encObj o).drop (sint.nat idx) = ((objSegs o).drop s).flatten⌝ : IProp GF)
      $$ [Hl iNdEx]
  · iexists 0, _, _
    iframe
    isplitl []
    · iapply objOwn_zero
    ipureintro
    refine ⟨by omega, by decide, by word, ?_⟩
    rw [encObj_flatten]; rfl
  wp_for HI
  obtain ⟨Hs, Hidx0, Hidxle, Hrest⟩ := Hs
  wp_if_destruct
  · -- an iteration: the next nonempty field
    replace Hif : sint.Z idx < sint.Z sl.len := by first | exact Hif | (revert Hif; simp)
    have hne : ((objSegs o).drop s).flatten ≠ [] := by
      rw [← Hrest]; intro h
      rw [List.drop_eq_nil_iff] at h; word
    obtain ⟨j, seg, hj1, hj2, hj3, hj4, hj5, hj6⟩ := next_seg _ _ hne
    rw [objSegs_length] at hj2
    rw [← o.upto_of_empty s j hj1 (by omega) hj3]
    rw [hj6] at Hrest
    clear hj6 hj3 hj1 hne Hs
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ 6 ≤ j)
      with rfl|rfl|rfl|rfl|rfl|rfl|hj6
    · -- field 1: ProId
      simp only [objSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 8 ++ (varint (o.proId.toNat) ++ ((objSegs o).drop (0 + 1)).flatten) := by
        rw [Hrest, varint_lt 8 (by decide)]; rfl
      have HNlt : 8 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 8
        (varint (o.proId.toNat) ++ ((objSegs o).drop (0 + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((8#64) >>> W64 3)) = W32 1 from rfl,
        show ((8#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : o.proId.toNat < 2 ^ 64 := by have := (o.proId).isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ ConsensusObj.mk (BitVec.ofNat 32 a) v.ProSeq' v.SvrSeq' v.IsNull' v.CliIds' v.CliSeqs' v.Commands') (o.proId.toNat) (((objSegs o).drop (0 + 1)).flatten) (encObj o) as i2
      rw [w32_ofNat_toNat']
      wp_for_post
      iframe
      iexists 1, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply objOwn_congr v (ConsensusObj.mk o.proId v.ProSeq' v.SvrSeq' v.IsNull' v.CliIds' v.CliSeqs' v.Commands') (o.upto 0) (o.upto 1) ⟨rfl, rfl, rfl⟩ ⟨by simp [ObjV.upto], by simp [ObjV.upto], by simp [ObjV.upto]⟩
          (fun h => by simp_all [ObjV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 2: ProSeq
      simp only [objSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 16 ++ (varint (o.proSeq.toNat) ++ ((objSegs o).drop (1 + 1)).flatten) := by
        rw [Hrest, varint_lt 16 (by decide)]; rfl
      have HNlt : 16 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 16
        (varint (o.proSeq.toNat) ++ ((objSegs o).drop (1 + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((16#64) >>> W64 3)) = W32 2 from rfl,
        show ((16#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : o.proSeq.toNat < 2 ^ 64 := by have := (o.proSeq).isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ ConsensusObj.mk v.ProId' (BitVec.ofNat 32 a) v.SvrSeq' v.IsNull' v.CliIds' v.CliSeqs' v.Commands') (o.proSeq.toNat) (((objSegs o).drop (1 + 1)).flatten) (encObj o) as i2
      rw [w32_ofNat_toNat']
      wp_for_post
      iframe
      iexists 2, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply objOwn_congr v (ConsensusObj.mk v.ProId' o.proSeq v.SvrSeq' v.IsNull' v.CliIds' v.CliSeqs' v.Commands') (o.upto 1) (o.upto 2) ⟨rfl, rfl, rfl⟩ ⟨by simp [ObjV.upto], by simp [ObjV.upto], by simp [ObjV.upto]⟩
          (fun h => by simp_all [ObjV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 3: SvrSeq
      simp only [objSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 24 ++ (varint (o.svrSeq.toNat) ++ ((objSegs o).drop (2 + 1)).flatten) := by
        rw [Hrest, varint_lt 24 (by decide)]; rfl
      have HNlt : 24 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 24
        (varint (o.svrSeq.toNat) ++ ((objSegs o).drop (2 + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((24#64) >>> W64 3)) = W32 3 from rfl,
        show ((24#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : o.svrSeq.toNat < 2 ^ 64 := by have := (o.svrSeq).isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ ConsensusObj.mk v.ProId' v.ProSeq' (BitVec.ofNat 32 a) v.IsNull' v.CliIds' v.CliSeqs' v.Commands') (o.svrSeq.toNat) (((objSegs o).drop (2 + 1)).flatten) (encObj o) as i2
      rw [w32_ofNat_toNat']
      wp_for_post
      iframe
      iexists 3, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply objOwn_congr v (ConsensusObj.mk v.ProId' v.ProSeq' o.svrSeq v.IsNull' v.CliIds' v.CliSeqs' v.Commands') (o.upto 2) (o.upto 3) ⟨rfl, rfl, rfl⟩ ⟨by simp [ObjV.upto], by simp [ObjV.upto], by simp [ObjV.upto]⟩
          (fun h => by simp_all [ObjV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 4: IsNull
      simp only [objSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      have hnull : o.isNull = true := by
        cases h : o.isNull <;> simp_all
      simp only [hnull, ite_true] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 32 ++ (varint 1 ++ ((objSegs o).drop (3 + 1)).flatten) := by
        rw [Hrest, varint_lt 32 (by decide), varint_lt 1 (by decide)]; rfl
      have HNlt : 32 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 32
        (varint 1 ++ ((objSegs o).drop (3 + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((32#64) >>> W64 3)) = W32 4 from rfl,
        show ((32#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : 1 < 2 ^ 64 := by decide
      clear Hpost Hpost0
      varint_loop v (fun a => v_ptr ↦ BitVec.ofNat 64 a) 1 (((objSegs o).drop (3 + 1)).flatten)
        (encObj o) as i2
      wp_for_post
      iframe
      iexists 4, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply objOwn_congr v (ConsensusObj.mk v.ProId' v.ProSeq' v.SvrSeq' true v.CliIds' v.CliSeqs'
          v.Commands') (o.upto 3) (o.upto 4) ⟨rfl, rfl, rfl⟩
          ⟨by simp [ObjV.upto], by simp [ObjV.upto], by simp [ObjV.upto]⟩
          (fun h => by simp_all [ObjV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 5: CliIds
      simp only [objSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      have hne : o.cliIds ≠ [] := fun h => hj5 (encPacked_eq_nil.mpr h)
      simp only [encPacked, hne, ite_false, encBytes] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 42 ++ (varint (o.cliIds.flatMap fun n => varint n.toNat).length ++
            (o.cliIds.flatMap fun n => varint n.toNat) ++ ((objSegs o).drop (4 + 1)).flatten) := by
        rw [Hrest, varint_lt 42 (by decide)]; simp
      have HNlt : 42 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 42
        (varint (o.cliIds.flatMap fun n => varint n.toNat).length ++
            (o.cliIds.flatMap fun n => varint n.toNat) ++ ((objSegs o).drop (4 + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((42#64) >>> W64 3)) = W32 5 from rfl,
        show ((42#64) &&& W64 7) = W64 2 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      generalize HP : (o.cliIds.flatMap fun n => varint n.toNat) = P at Hpost
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : P.length < 2 ^ 64 := by
        have := congrArg List.length Hpre
        simp only [List.length_drop, List.length_append] at this; word
      clear Hpost Hpost0
      varint_loop packedLen (fun a => packedLen_ptr ↦ BitVec.ofNat 64 a) P.length
        (P ++ ((objSegs o).drop (4 + 1)).flatten) (encObj o) as i2
      have HLlt : sint.nat i2 + P.length ≤ (encObj o).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have Hhi : sint.nat (i2 + BitVec.ofNat 64 P.length) = sint.nat i2 + P.length := by word
      rw [if_pos ⟨Hpost0, by word, by word⟩]
      have Hb : 0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ sint.Z (i2 + BitVec.ofNat 64 P.length) ∧
          sint.Z (i2 + BitVec.ofNat 64 P.length) ≤ sint.Z sl.len := ⟨Hpost0, by word, by word⟩
      icases (ownSlice_slice _ _ sl dq (encObj o) Hb).1 $$ Hsl with ⟨Hsl1, Hsl2, Hsl3⟩
      rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]
      wp_auto
      ihave %HPlen := ownSlice_len _ _ _ $$ Hsl2
      ihave HC : (∃ (ci cc : w64) (cx : w8), "i" ∷ i_ptr ↦ ci ∗ "count" ∷ count_ptr ↦ cc ∗
          "integer" ∷ integer_ptr ↦ cx ∗
          "%Hc" ∷ ⌜0 ≤ sint.Z ci ∧ sint.nat ci ≤ P.length ∧ 0 ≤ sint.Z cc ∧ sint.Z cc ≤ sint.Z ci⌝ :
          IProp GF) $$ [i count integer]
      · iexists _, _, _
        iframe
        ipureintro
        refine ⟨by decide, by word, by decide, by decide⟩
      wp_for HC
      wp_if_destruct
      · obtain ⟨Hc1, Hc2, Hc3, Hc4⟩ := Hc
        rw [if_pos ⟨Hc1, by word⟩]
        list_elem P (sint.nat ci) as pb
        wp_apply wp_load_slice_index _ (sint.Z ci) P dq pb Hc1 $$ [Hsl2] with Hsl2
        · iframe; ipureintro; rw [show (sint.Z ci).toNat = sint.nat ci by word]; exact Hpb_lookup
        wp_if_destruct
        · wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, by word, by word⟩
        · wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, by word, by word⟩
      obtain ⟨Hc1, Hc2, Hc3, Hc4⟩ := Hc
      ihave Hsl := (ownSlice_slice _ _ sl dq (encObj o) Hb).2 $$ [Hsl1 Hsl2 Hsl3]
      · rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]; iframe
      icases objOwn_open _ _ $$ Hown with ⟨%Hown, Hids, Hidscap, Hseqs, Hseqscap, Hcmds, Hcmdscap⟩
      have Hu4 : (o.upto 4).cliIds = [] := by simp [ObjV.upto]
      rw [Hu4]
      ihave %Hidslen := ownSlice_len _ _ _ $$ Hids
      wp_join iprop(∃ (cs : GoSlice), "Hl" ∷ l ↦ ConsensusObj.mk v.ProId' v.ProSeq' v.SvrSeq' v.IsNull' cs
          v.CliSeqs' v.Commands' ∗ "Hids" ∷ cs ↦* ([] : List w32) ∗
          "Hidscap" ∷ ownSliceCap w32 cs (DFrac.own 1) ∗ "m" ∷ m_ptr ↦ l ∗
          "elementCount" ∷ elementCount_ptr ↦ cc) with [Hl Hids Hidscap m elementCount]
        as ⟨%cs, Hl, Hids, Hidscap, m, elementCount⟩
      · wp_if_destruct
        · wp_apply (wp_slice_make3 (V := w32) (W64 0) cc ⟨by decide, Hc3⟩) as %ns ⟨Hns, Hnscap, %_⟩
          wp_join_done
          iexists ns
          iframe
        · exfalso
          have h0 : v.CliIds'.len = W64 0 := by
            have := Hidslen.1; simp only [List.length_nil] at this; word
          simp [h0] at Hif
      iNamed Hl; iNamed Hids; iNamed Hidscap; iNamed m; iNamed elementCount
      have Htot : sint.nat i2 + P.length + ((objSegs o).drop (4 + 1)).flatten.length =
          (encObj o).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      ihave HD : (∃ (k : Nat) (idx' : w64) (cs' : GoSlice),
          "iNdEx" ∷ iNdEx_ptr ↦ idx' ∗
          "Hl" ∷ l ↦ ConsensusObj.mk v.ProId' v.ProSeq' v.SvrSeq' v.IsNull' cs' v.CliSeqs' v.Commands' ∗
          "Hids" ∷ cs' ↦* o.cliIds.take k ∗ "Hidscap" ∷ ownSliceCap w32 cs' (DFrac.own 1) ∗
          "%Hk" ∷ ⌜k ≤ o.cliIds.length ∧ 0 ≤ sint.Z idx' ∧ sint.nat idx' ≤ (encObj o).length ∧
            (encObj o).drop (sint.nat idx') = ((o.cliIds.drop k).flatMap fun n => varint n.toNat) ++
              ((objSegs o).drop (4 + 1)).flatten⌝ : IProp GF) $$ [iNdEx Hl Hids Hidscap]
      · iexists 0, _, _
        simp only [List.take_zero, List.drop_zero, HP]
        iframe
        ipureintro
        exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
      wp_for HD
      obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hk
      have Hklen := congrArg List.length Hk4
      simp only [List.length_drop, List.length_append] at Hklen
      wp_if_destruct
      · -- one more element
        replace Hif : sint.Z idx' < sint.Z (i2 + BitVec.ofNat 64 P.length) := by
          first | exact Hif | (revert Hif; simp)
        have hk : k < o.cliIds.length := by
          apply Nat.lt_of_not_le; intro hk
          rw [List.drop_eq_nil_of_le hk] at Hklen
          simp only [List.flatMap_nil, List.length_nil, Nat.zero_add] at Hklen; word
        list_elem o.cliIds k as cv
        have Hpre0 := Hk2
        have Hpre : (encObj o).drop (sint.nat idx') = varint cv.toNat ++
            (((o.cliIds.drop (k + 1)).flatMap fun n => varint n.toNat) ++
              ((objSegs o).drop (4 + 1)).flatten) := by
          rw [Hk4, List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
          rw [List.getElem?_eq_some_iff] at Hcv_lookup
          obtain ⟨_, h⟩ := Hcv_lookup; rw [h]
        have HNlt : cv.toNat < 2 ^ 64 := by have := cv.isLt; omega
        varint_loop v (fun a => v_ptr ↦ BitVec.ofNat 32 a) cv.toNat
          (((o.cliIds.drop (k + 1)).flatMap fun n => varint n.toNat) ++
              ((objSegs o).drop (4 + 1)).flatten) (encObj o) as i3
        rw [w32_ofNat_toNat']
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint32))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w32) (t := go.uint32) [cv]
        wp_auto
        rw [show go.arrayLiteralSize
          [KeyedElement none (ElementExpression go.uint32 #cv)] = 1 from rfl]
        isplitl []
        · ipureintro; rfl
        iintro %lit_ptr ⟨Hlit, Hlitcap⟩
        wp_apply wp_slice_append $$ [Hids Hidscap Hlit] as %ns ⟨Hids, Hidscap, -⟩
        · iframe
        wp_for_post
        iframe
        iexists k + 1, _, _
        iframe
        rw [List.take_add_one, Hcv_lookup]
        simp only [Option.toList_some]
        iframe
        ipureintro
        exact ⟨hk, Hpost0, Hpostle, Hpost⟩
      -- the packed field is decoded
      replace Hif : ¬ sint.Z idx' < sint.Z (i2 + BitVec.ofNat 64 P.length) := by
        first | exact Hif | (revert Hif; simp)
      have hk : k = o.cliIds.length := by
        apply Nat.le_antisymm Hk1; apply Nat.le_of_not_lt; intro hk
        rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.length_append] at Hklen
        have := varint_length_pos (o.cliIds[k]).toNat
        word
      subst hk
      rw [List.take_length]
      rw [List.drop_length, List.flatMap_nil, List.nil_append] at Hk4
      wp_for_post
      iframe
      iexists 5, _, _
      iframe
      isplitl [Hids Hidscap Hseqs Hseqscap Hcmds Hcmdscap]
      · iapply objOwn_close
        have e1 : (o.upto 5).cliIds = o.cliIds := by simp [ObjV.upto]
        have e2 : (o.upto 5).cliSeqs = (o.upto 4).cliSeqs := by simp [ObjV.upto]
        have e3 : (o.upto 5).commands = (o.upto 4).commands := by simp [ObjV.upto]
        rw [e1, e2, e3]
        iframe
        ipureintro
        simp only [ObjV.upto, Nat.reduceLT, ite_true, ite_false] at Hown ⊢
        exact Hown
      ipureintro
      exact ⟨by omega, Hk2, Hk3, Hk4⟩
    · -- field 6: CliSeqs
      simp only [objSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      have hne : o.cliSeqs ≠ [] := fun h => hj5 (encPacked_eq_nil.mpr h)
      simp only [encPacked, hne, ite_false, encBytes] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 50 ++ (varint (o.cliSeqs.flatMap fun n => varint n.toNat).length ++
            (o.cliSeqs.flatMap fun n => varint n.toNat) ++ ((objSegs o).drop (5 + 1)).flatten) := by
        rw [Hrest, varint_lt 50 (by decide)]; simp
      have HNlt : 50 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 50
        (varint (o.cliSeqs.flatMap fun n => varint n.toNat).length ++
            (o.cliSeqs.flatMap fun n => varint n.toNat) ++ ((objSegs o).drop (5 + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((50#64) >>> W64 3)) = W32 6 from rfl,
        show ((50#64) &&& W64 7) = W64 2 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      generalize HP : (o.cliSeqs.flatMap fun n => varint n.toNat) = P at Hpost
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : P.length < 2 ^ 64 := by
        have := congrArg List.length Hpre
        simp only [List.length_drop, List.length_append] at this; word
      clear Hpost Hpost0
      varint_loop packedLen (fun a => packedLen_ptr ↦ BitVec.ofNat 64 a) P.length
        (P ++ ((objSegs o).drop (5 + 1)).flatten) (encObj o) as i2
      have HLlt : sint.nat i2 + P.length ≤ (encObj o).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have Hhi : sint.nat (i2 + BitVec.ofNat 64 P.length) = sint.nat i2 + P.length := by word
      rw [if_pos ⟨Hpost0, by word, by word⟩]
      have Hb : 0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ sint.Z (i2 + BitVec.ofNat 64 P.length) ∧
          sint.Z (i2 + BitVec.ofNat 64 P.length) ≤ sint.Z sl.len := ⟨Hpost0, by word, by word⟩
      icases (ownSlice_slice _ _ sl dq (encObj o) Hb).1 $$ Hsl with ⟨Hsl1, Hsl2, Hsl3⟩
      rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]
      wp_auto
      ihave %HPlen := ownSlice_len _ _ _ $$ Hsl2
      ihave HC : (∃ (ci cc : w64) (cx : w8), "i" ∷ i_ptr ↦ ci ∗ "count" ∷ count_ptr ↦ cc ∗
          "integer" ∷ integer_ptr ↦ cx ∗
          "%Hc" ∷ ⌜0 ≤ sint.Z ci ∧ sint.nat ci ≤ P.length ∧ 0 ≤ sint.Z cc ∧ sint.Z cc ≤ sint.Z ci⌝ :
          IProp GF) $$ [i count integer]
      · iexists _, _, _
        iframe
        ipureintro
        refine ⟨by decide, by word, by decide, by decide⟩
      wp_for HC
      wp_if_destruct
      · obtain ⟨Hc1, Hc2, Hc3, Hc4⟩ := Hc
        rw [if_pos ⟨Hc1, by word⟩]
        list_elem P (sint.nat ci) as pb
        wp_apply wp_load_slice_index _ (sint.Z ci) P dq pb Hc1 $$ [Hsl2] with Hsl2
        · iframe; ipureintro; rw [show (sint.Z ci).toNat = sint.nat ci by word]; exact Hpb_lookup
        wp_if_destruct
        · wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, by word, by word⟩
        · wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, by word, by word⟩
      obtain ⟨Hc1, Hc2, Hc3, Hc4⟩ := Hc
      ihave Hsl := (ownSlice_slice _ _ sl dq (encObj o) Hb).2 $$ [Hsl1 Hsl2 Hsl3]
      · rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]; iframe
      icases objOwn_open _ _ $$ Hown with ⟨%Hown, Hseqs, Hseqscap, Hids, Hidscap, Hcmds, Hcmdscap⟩
      have Hu4 : (o.upto 5).cliSeqs = [] := by simp [ObjV.upto]
      rw [Hu4]
      ihave %Hidslen := ownSlice_len _ _ _ $$ Hids
      wp_join iprop(∃ (cs : GoSlice), "Hl" ∷ l ↦ ConsensusObj.mk v.ProId' v.ProSeq' v.SvrSeq' v.IsNull' v.CliIds' cs
          v.Commands' ∗ "Hids" ∷ cs ↦* ([] : List w32) ∗
          "Hidscap" ∷ ownSliceCap w32 cs (DFrac.own 1) ∗ "m" ∷ m_ptr ↦ l ∗
          "elementCount" ∷ elementCount_ptr ↦ cc) with [Hl Hids Hidscap m elementCount]
        as ⟨%cs, Hl, Hids, Hidscap, m, elementCount⟩
      · wp_if_destruct
        · wp_apply (wp_slice_make3 (V := w32) (W64 0) cc ⟨by decide, Hc3⟩) as %ns ⟨Hns, Hnscap, %_⟩
          wp_join_done
          iexists ns
          iframe
        · exfalso
          have h0 : v.CliSeqs'.len = W64 0 := by
            have := Hidslen.1; simp only [List.length_nil] at this; word
          simp [h0] at Hif
      iNamed Hl; iNamed Hids; iNamed Hidscap; iNamed m; iNamed elementCount
      have Htot : sint.nat i2 + P.length + ((objSegs o).drop (5 + 1)).flatten.length =
          (encObj o).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      ihave HD : (∃ (k : Nat) (idx' : w64) (cs' : GoSlice),
          "iNdEx" ∷ iNdEx_ptr ↦ idx' ∗
          "Hl" ∷ l ↦ ConsensusObj.mk v.ProId' v.ProSeq' v.SvrSeq' v.IsNull' v.CliIds' cs' v.Commands' ∗
          "Hids" ∷ cs' ↦* o.cliSeqs.take k ∗ "Hidscap" ∷ ownSliceCap w32 cs' (DFrac.own 1) ∗
          "%Hk" ∷ ⌜k ≤ o.cliSeqs.length ∧ 0 ≤ sint.Z idx' ∧ sint.nat idx' ≤ (encObj o).length ∧
            (encObj o).drop (sint.nat idx') = ((o.cliSeqs.drop k).flatMap fun n => varint n.toNat) ++
              ((objSegs o).drop (5 + 1)).flatten⌝ : IProp GF) $$ [iNdEx Hl Hids Hidscap]
      · iexists 0, _, _
        simp only [List.take_zero, List.drop_zero, HP]
        iframe
        ipureintro
        exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
      wp_for HD
      obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hk
      have Hklen := congrArg List.length Hk4
      simp only [List.length_drop, List.length_append] at Hklen
      wp_if_destruct
      · -- one more element
        replace Hif : sint.Z idx' < sint.Z (i2 + BitVec.ofNat 64 P.length) := by
          first | exact Hif | (revert Hif; simp)
        have hk : k < o.cliSeqs.length := by
          apply Nat.lt_of_not_le; intro hk
          rw [List.drop_eq_nil_of_le hk] at Hklen
          simp only [List.flatMap_nil, List.length_nil, Nat.zero_add] at Hklen; word
        list_elem o.cliSeqs k as cv
        have Hpre0 := Hk2
        have Hpre : (encObj o).drop (sint.nat idx') = varint cv.toNat ++
            (((o.cliSeqs.drop (k + 1)).flatMap fun n => varint n.toNat) ++
              ((objSegs o).drop (5 + 1)).flatten) := by
          rw [Hk4, List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
          rw [List.getElem?_eq_some_iff] at Hcv_lookup
          obtain ⟨_, h⟩ := Hcv_lookup; rw [h]
        have HNlt : cv.toNat < 2 ^ 64 := by have := cv.isLt; omega
        varint_loop v (fun a => v_ptr ↦ BitVec.ofNat 32 a) cv.toNat
          (((o.cliSeqs.drop (k + 1)).flatMap fun n => varint n.toNat) ++
              ((objSegs o).drop (5 + 1)).flatten) (encObj o) as i3
        rw [w32_ofNat_toNat']
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint32))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w32) (t := go.uint32) [cv]
        wp_auto
        rw [show go.arrayLiteralSize
          [KeyedElement none (ElementExpression go.uint32 #cv)] = 1 from rfl]
        isplitl []
        · ipureintro; rfl
        iintro %lit_ptr ⟨Hlit, Hlitcap⟩
        wp_apply wp_slice_append $$ [Hids Hidscap Hlit] as %ns ⟨Hids, Hidscap, -⟩
        · iframe
        wp_for_post
        iframe
        iexists k + 1, _, _
        iframe
        rw [List.take_add_one, Hcv_lookup]
        simp only [Option.toList_some]
        iframe
        ipureintro
        exact ⟨hk, Hpost0, Hpostle, Hpost⟩
      -- the packed field is decoded
      replace Hif : ¬ sint.Z idx' < sint.Z (i2 + BitVec.ofNat 64 P.length) := by
        first | exact Hif | (revert Hif; simp)
      have hk : k = o.cliSeqs.length := by
        apply Nat.le_antisymm Hk1; apply Nat.le_of_not_lt; intro hk
        rw [List.drop_eq_getElem_cons hk, List.flatMap_cons, List.length_append] at Hklen
        have := varint_length_pos (o.cliSeqs[k]).toNat
        word
      subst hk
      rw [List.take_length]
      rw [List.drop_length, List.flatMap_nil, List.nil_append] at Hk4
      wp_for_post
      iframe
      iexists 6, _, _
      iframe
      isplitl [Hids Hidscap Hseqs Hseqscap Hcmds Hcmdscap]
      · iapply objOwn_close
        have e1 : (o.upto 6).cliSeqs = o.cliSeqs := by simp [ObjV.upto]
        have e2 : (o.upto 6).cliIds = (o.upto 5).cliIds := by simp [ObjV.upto]
        have e3 : (o.upto 6).commands = (o.upto 5).commands := by simp [ObjV.upto]
        rw [e1, e2, e3]
        iframe
        ipureintro
        simp only [ObjV.upto, Nat.reduceLT, ite_true, ite_false] at Hown ⊢
        exact Hown
      ipureintro
      exact ⟨by omega, Hk2, Hk3, Hk4⟩
    · -- field 7: a command
      have hjc : j - 6 < o.commands.length := by omega
      have hseg : seg = encBytes 0x3a (o.commands[j - 6]) := by
        simp only [objSegs, List.getElem?_append_right (by simp; omega : [encScalar 0x08 o.proId.toNat,
          encScalar 0x10 o.proSeq.toNat, encScalar 0x18 o.svrSeq.toNat,
          (if o.isNull then [0x20, 1] else []), encPacked 0x2a o.cliIds,
          encPacked 0x32 o.cliSeqs].length ≤ j), List.getElem?_map] at hj4
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.getElem?_eq_getElem hjc,
          Option.map_some, Option.some.injEq] at hj4
        exact hj4.symm
      subst hseg
      generalize hcmd : o.commands[j - 6] = cmd at Hrest
      simp only [encBytes] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encObj o).drop (sint.nat idx) =
          varint 58 ++ (varint cmd.length ++ cmd ++ ((objSegs o).drop (j + 1)).flatten) := by
        rw [Hrest, varint_lt 58 (by decide)]; simp
      have HNlt : 58 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 58
        (varint cmd.length ++ cmd ++ ((objSegs o).drop (j + 1)).flatten) (encObj o) as i1
      try rw [show W32 (uint.Z ((58#64) >>> W64 3)) = W32 7 from rfl,
        show ((58#64) &&& W64 7) = W64 2 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : cmd.length < 2 ^ 64 := by
        have := congrArg List.length Hpre
        simp only [List.length_drop, List.length_append] at this; word
      clear Hpost Hpost0
      varint_loop stringLen (fun a => stringLen_ptr ↦ BitVec.ofNat 64 a) cmd.length
        (cmd ++ ((objSegs o).drop (j + 1)).flatten) (encObj o) as i2
      have HLlt : sint.nat i2 + cmd.length ≤ (encObj o).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have Hhi : sint.nat (i2 + BitVec.ofNat 64 cmd.length) = sint.nat i2 + cmd.length := by word
      rw [if_pos ⟨Hpost0, by word, by word⟩]
      have Hb : 0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ sint.Z (i2 + BitVec.ofNat 64 cmd.length) ∧
          sint.Z (i2 + BitVec.ofNat 64 cmd.length) ≤ sint.Z sl.len := ⟨Hpost0, by word, by word⟩
      icases (ownSlice_slice _ _ sl dq (encObj o) Hb).1 $$ Hsl with ⟨Hsl1, Hsl2, Hsl3⟩
      rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]
      wp_apply wp_bytes_to_string $$ Hsl2 as Hsl2
      ihave Hsl := (ownSlice_slice _ _ sl dq (encObj o) Hb).2 $$ [Hsl1 Hsl2 Hsl3]
      · rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]; iframe
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoString) (t := go.string) [cmd]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.string #cmd)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, Hlitcap⟩
      icases objOwn_open _ _ $$ Hown with ⟨%Hown, Hids, Hidscap, Hseqs, Hseqscap, Hcmds, Hcmdscap⟩
      wp_apply wp_slice_append $$ [Hcmds Hcmdscap Hlit] as %ns ⟨Hcmds, Hcmdscap, -⟩
      · iframe
      wp_auto
      wp_for_post
      iframe
      iexists j + 1, _, _
      iframe
      isplitl [Hids Hidscap Hseqs Hseqscap Hcmds Hcmdscap]
      · iapply objOwn_close
        have e1 : (o.upto (j + 1)).cliIds = (o.upto j).cliIds := by
          simp only [ObjV.upto, show 4 < j by omega, show 4 < j + 1 by omega, ite_true]
        have e2 : (o.upto (j + 1)).cliSeqs = (o.upto j).cliSeqs := by
          simp only [ObjV.upto, show 5 < j by omega, show 5 < j + 1 by omega, ite_true]
        have e3 : (o.upto (j + 1)).commands = (o.upto j).commands ++ [cmd] := by
          simp only [ObjV.upto, show j + 1 - 6 = (j - 6) + 1 by omega, List.take_add_one,
            List.getElem?_eq_getElem hjc, hcmd, Option.toList_some]
        rw [e1, e2, e3]
        iframe
        ipureintro
        simp only [ObjV.upto] at Hown ⊢
        simp only [show 0 < j by omega, show 1 < j by omega, show 2 < j by omega,
          show 3 < j by omega, show 0 < j + 1 by omega, show 1 < j + 1 by omega,
          show 2 < j + 1 by omega, show 3 < j + 1 by omega, ite_true] at Hown ⊢
        exact Hown
      ipureintro
      refine ⟨by omega, by word, by word, ?_⟩
      rw [Hhi, ← List.drop_drop, Hpost, List.drop_left]
  · -- the end
    replace Hif : ¬ sint.Z idx < sint.Z sl.len := by first | exact Hif | (revert Hif; simp)
    have hnil : ((objSegs o).drop s).flatten = [] := by
      rw [← Hrest, List.drop_eq_nil_iff]; word
    have ho : o.upto s = o := by
      have := o.upto_of_empty s (6 + o.commands.length) Hs (Nat.le_refl _)
        (fun i h1 h2 => rest_nil _ _ hnil i h1 (by rw [objSegs_length]; exact h2))
      rw [o.upto_all] at this; exact this.symm
    rw [ho]
    unfold objOwn
    icases Hown with ⟨%H, H1, -, H2, -, H3, -⟩
    ipersist H1; ipersist H2; ipersist H3
    wp_if_destruct
    · exfalso; word
    wp_end
    iexists v
    iframe
    unfold objRep
    isplitl []; · ipureintro; exact H
    isplitl []; · iexact H1
    isplitl []; · iexact H2
    iexact H3

end proof
end Perennial.rabia.internal.message
