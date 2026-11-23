/-
`nextBallot`, `makeBallot` against the model's `nextBallot` (`makeBallotZ`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-- The state after `makeBallot` on `x` (record `w`, bookkeeping `lb`). -/
def makeBallotSt (σ : RState) (x : InstId) (w : InstRec) (lb : LbRec) : RState :=
  σ.setInst x { w with lb := some { lb with lastTriedBallot :=
    (nextBallot σ w.bal lb.lastTriedBallot).getD lb.lastTriedBallot } }

theorem makeBallotZ_eq (σ : RState) (bal lt : w32) : makeBallotZ σ bal lt =
    if σ.isLeader ∧ (max (max (sint.Z bal) (sint.Z lt)) 0 / 5 + 1) * 5 + σ.id <
        sint.Z σ.maxRecvBallot then
      (max (max (sint.Z bal) (sint.Z lt)) 0 / 5 + 1) * 5 + σ.id +
        5 * ((sint.Z σ.maxRecvBallot - ((max (max (sint.Z bal) (sint.Z lt)) 0 / 5 + 1) * 5 + σ.id)
          + 5 - 1) / 5)
    else (max (max (sint.Z bal) (sint.Z lt)) 0 / 5 + 1) * 5 + σ.id := rfl

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `nextBallot(inst, lastTried)` (`inst.bal` read). -/
theorem wp_nextBallot
    (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (σ : RState) (hid : σ.id = i) (pt : Loc) (y : epaxos.Instance) (dq : DFrac) (lt : w32) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ pt ↦{dq} y ∗
        efld r go!"IsLeader" ↦ σ.isLeader ∗ efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"nextBallot"))
        (Val #pt)) (Val #lt))
    {{ RET (PairV #((nextBallot σ y.bal' lt).getD (W32 0)) #(nextBallot σ y.bal' lt).isSome);
        pt ↦{dq} y ∗ efld r go!"IsLeader" ↦ σ.isLeader ∗
        efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot }} := by
  wp_start as ⟨#Hrr, #Hfro, Hpt, Hlead, Hmrb⟩
  ihave ⟨#HN, -, #HId, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
  have hL5 : L.length = nR := HLn.1
  have hi : i < 5 := by have := HLn.2; rw [hL5] at this; exact this
  rw [hL5]
  ihave %Hptnn := typedPointsto_not_null _ _ _ $$ Hpt
  iStructNamed Hpt
  wp_auto
  wp_join iprop(b_ptr ↦ W64 (max (sint.Z y.bal') (sint.Z lt))) with [b lastTried] as Hb
  · have h : sint.Z y.bal' < sint.Z lt := by word
    rw [Int.max_eq_right (Int.le_of_lt h)]
    iframe
  · have h : sint.Z lt ≤ sint.Z y.bal' := by word
    rw [Int.max_eq_left h]
    iframe
  wp_join iprop(b_ptr ↦ W64 (max (max (sint.Z y.bal') (sint.Z lt)) 0)) with [Hb] as Hb
  · have h : max (sint.Z y.bal') (sint.Z lt) < 0 := by
      have := Int.le_max_left (sint.Z y.bal') (sint.Z lt)
      have := Int.le_max_right (sint.Z y.bal') (sint.Z lt)
      word
    rw [Int.max_eq_right (Int.le_of_lt h)]
    iframe
  · have h : 0 ≤ max (sint.Z y.bal') (sint.Z lt) := by
      have := Int.le_max_left (sint.Z y.bal') (sint.Z lt)
      have := Int.le_max_right (sint.Z y.bal') (sint.Z lt)
      word
    rw [Int.max_eq_left h]
    iframe
  -- the first candidate
  have hb0 : 0 ≤ max (max (sint.Z y.bal') (sint.Z lt)) 0 := Int.le_max_right _ _
  have hb1 : max (max (sint.Z y.bal') (sint.Z lt)) 0 < 2 ^ 31 := by
    have := Int.max_le.mpr ⟨Int.max_le.mpr ⟨(show sint.Z y.bal' ≤ 2^31 - 1 by word),
      (show sint.Z lt ≤ 2^31 - 1 by word)⟩, (show (0:Int) ≤ 2^31 - 1 by decide)⟩
    omega
  have hn0 : sint.Z ((BitVec.sdiv (W64 (max (max (sint.Z y.bal') (sint.Z lt)) 0)) (W64 (nR : Int)) +
      W64 1) * W64 (nR : Int) + W64 (sint.Z (W32 (i : Int)))) =
      (max (max (sint.Z y.bal') (sint.Z lt)) 0 / 5 + 1) * 5 + i := by
    generalize max (max (sint.Z y.bal') (sint.Z lt)) 0 = bZ at hb0 hb1 ⊢
    rw [show ((nR : Nat) : Int) = 5 from rfl]; word
  generalize ((BitVec.sdiv (W64 (max (max (sint.Z y.bal') (sint.Z lt)) 0)) (W64 (nR : Int)) +
      W64 1) * W64 (nR : Int) + W64 (sint.Z (W32 (i : Int)))) = n0 at hn0 ⊢
  generalize hbz : max (max (sint.Z y.bal') (sint.Z lt)) 0 = bZ at hb0 hb1 hn0
  have hZ : makeBallotZ σ y.bal' lt =
      if σ.isLeader ∧ sint.Z n0 < sint.Z σ.maxRecvBallot then
        sint.Z n0 + 5 * ((sint.Z σ.maxRecvBallot - sint.Z n0 + 5 - 1) / 5)
      else sint.Z n0 := by
    rw [makeBallotZ_eq, hbz, hid, hn0]
  have hmrb := (show -2^31 ≤ sint.Z σ.maxRecvBallot ∧ sint.Z σ.maxRecvBallot < 2^31 by
    constructor <;> word)
  have hn0b : 0 ≤ sint.Z n0 ∧ sint.Z n0 < 2^31 + 10 := by
    rw [hn0]; constructor <;> omega
  wp_join iprop(∃ nf : w64, n_ptr ↦ nf ∗ r_ptr ↦ r ∗ efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot ∗
      ⌜sint.Z nf = makeBallotZ σ y.bal' lt⌝) at (if: _ then _ else _) with [n r Hmrb]
      as ⟨%nf, n, r, Hmrb, %Hnf⟩
  · rcases hl : σ.isLeader
    · wp_auto
      wp_join_done
      iexists n0; iframe; ipureintro; rw [hZ, hl]; simp
    · wp_auto
      ihave HL : (∃ (m : Nat) (nf : w64), "n" ∷ n_ptr ↦ nf ∗
          "%Hm" ∷ ⌜sint.Z nf = sint.Z n0 + 5 * m ∧
            (m = 0 ∨ sint.Z n0 + 5 * ((m : Int) - 1) < sint.Z σ.maxRecvBallot)⌝ : IProp GF)
          $$ [n]
      · iexists 0, n0; iframe; ipureintro; exact ⟨by omega, Or.inl rfl⟩
      wp_for HL
      wp_if_destruct
      · wp_for_post
        iframe
        iexists m + 1, nf + W64 (nR : Int)
        iframe
        ipureintro
        have he : sint.Z (W64 (sint.Z σ.maxRecvBallot)) = sint.Z σ.maxRecvBallot := by word
        rw [he] at Hif
        have hs : sint.Z (nf + W64 (nR : Int)) = sint.Z nf + 5 := by
          rw [show ((nR : Nat) : Int) = 5 from rfl]
          have := Hm.1; word
        rw [hs, Hm.1]
        constructor
        · push_cast; omega
        · right; push_cast; omega
      · wp_join_done
        iexists nf; iframe; ipureintro
        rw [hZ, hl]
        have he : sint.Z (W64 (sint.Z σ.maxRecvBallot)) = sint.Z σ.maxRecvBallot := by word
        rw [he] at Hif
        by_cases hc : sint.Z n0 < sint.Z σ.maxRecvBallot
        · rw [if_pos ⟨rfl, hc⟩, Hm.1]
          rcases Hm.2 with h | h
          · subst h; omega
          · omega
        · rw [if_neg (fun h => hc h.2), Hm.1]
          rcases Hm.2 with h | h
          · subst h; omega
          · omega
  have hm : sint.Z (W64 2147483647) = 2 ^ 31 - 1 := by word
  rw [hm]
  ihave Hpt : pt ↦{dq} y $$ [Cmds bal vbal Status Seq Deps lb Index Lowlink bfilter proposeTime id]
  · iapply typedPointsto_combine _ _ _ Hptnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_if_destruct
  · have hnb : nextBallot σ y.bal' lt = none := by
      unfold nextBallot; rw [if_pos (by rw [← Hnf]; exact Hif)]
    rw [hnb]
    simp only [Option.getD_none, Option.isSome_none]
    iapply HΦ; iframe
  · have hnb : nextBallot σ y.bal' lt = some (W32 (sint.Z nf)) := by
      unfold nextBallot; rw [if_neg (by rw [← Hnf]; exact Hif), Hnf]
    rw [hnb]
    simp only [Option.getD_some, Option.isSome_some]
    iapply HΦ; iframe

/-- `makeBallot(replica, instance)`: `lb.lastTriedBallot = nextBallot(inst, lb.lastTriedBallot)`
when it fits. -/
theorem wp_makeBallot (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (σ : RState) (hid : σ.id = i) (replica n : w32) (w : InstRec) (lb : LbRec)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hw : σ.inst ⟨toN replica, toN n⟩ = some w) (hlb : w.lb = some lb) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fwRO γ rr i L p ∗ ownRep γ i r σ }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"makeBallot"))
        (Val #replica)) (Val #n))
    {{ RET #(); ownRep γ i r (makeBallotSt σ ⟨toN replica, toN n⟩ w lb) }} := by
  wp_start as ⟨#Hrr, #Hfro, Hrep⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  have hq' : toN replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
  icases repInsts_acc γ i r σ.inst ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  rw [hw]
  unfold instAt ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  rw [hlb]
  icases Hylb with ⟨%Hlbnn, Hlb⟩
  unfold ownLb
  icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlcmds, Hldeps, Hlprs, %Hlprsl, Hlpr⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
  have e2 : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
  have hqe : (sint.Z replica).toNat = toN replica := rfl
  have hne : (sint.Z n).toNat = toN n := rfl
  wp_auto
  have h1 : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z iss.len := by
    have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row.len := by
    have := hn.1; have := hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  wp_apply (wp_nextBallot γ i r rr L p σ hid ptr y (DFrac.own 1) yl.lastTriedBallot')
    $$ [$Hrr $Hfro $Hy $Hlead $Hmrb] as ⟨Hy, Hlead, Hmrb⟩
  have hyb : y.bal' = w.bal := Hyf.1
  have hyl : yl.lastTriedBallot' = lb.lastTriedBallot := Hylf.2.2.2.2.2.2.2.1
  rw [hyb, hyl]
  have hpset : ptrs.set (toN n) ptr = ptrs := list_set_lookup_self _ _ _ Hptr.1
  rcases hnb : nextBallot σ w.bal lb.lastTriedBallot with _ | nb
  · simp only [Option.isSome_none]
    wp_auto
    have hms : makeBallotSt σ ⟨toN replica, toN n⟩ w lb = σ := by
      unfold makeBallotSt RState.setInst; rw [hnb]
      have hw' : ({ w with lb := some { lb with lastTriedBallot := lb.lastTriedBallot } } : InstRec)
          = w := by
        cases w; simp only at hlb; subst hlb; rfl
      simp only [Option.getD_none]
      rw [hw', upd_self _ _ _ hw]
    rw [hms]
    ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · rw [hpset]; iexact Hptrs
    · iexists y
      iframe Hy Hyid Hycmds Hydeps
      isplitr
      · ipureintro; exact Hyf
      rw [hlb]
      isplitr
      · ipureintro; exact Hlbnn
      iexists yl, gs, prs
      iframe
      ipureintro
      exact ⟨Hylf, Hlprsl⟩
    rw [upd_self _ _ _ hw]
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hib, Hcb⟩
  · simp only [Option.isSome_some]
    wp_auto
    have hms : makeBallotSt σ ⟨toN replica, toN n⟩ w lb = σ.setInst ⟨toN replica, toN n⟩
        { w with lb := some { lb with lastTriedBallot := nb } } := by
      unfold makeBallotSt; rw [hnb]; rfl
    rw [hms]
    ihave Hins := Hclose $$ %ptr %(some { w with lb := some { lb with lastTriedBallot := nb } })
      [Hptrs] [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlpr]
    · rw [hpset]; iexact Hptrs
    · iexists y
      iframe Hy Hyid Hycmds Hydeps
      isplitr
      · ipureintro; exact Hyf
      isplitr
      · ipureintro; exact Hlbnn
      iexists { yl with lastTriedBallot' := nb }, gs, prs
      iframe
      ipureintro
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9, h10, h11, h12⟩ := Hylf
      refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, rfl, h9, h10, h11, h12⟩, ?_⟩
      exact Hlprsl
    iapply HΦ
    simp only [RState.setInst]
    iframe
    ipureintro
    exact ⟨instBounds_upd _ _ _ Hib hq' hn.2, Hcb⟩
  done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
