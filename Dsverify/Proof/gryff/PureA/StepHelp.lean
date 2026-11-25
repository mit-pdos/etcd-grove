/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepHelp.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal (A1a): helpers for the step cases that create copies or messages (`StepRecover`,
`StepRmw`): broadcasts' receivers, ballots (`makeBallotLargerThan`), rows, and the transport of
`CInv`'s clauses when ballots only grow (`BalLe`).
-/
module

public import Dsverify.Proof.gryff.PureA.StepSim

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-! ## Broadcasts -/

/-- A broadcast from replica `a` sends one copy of `m` to each peer. -/
theorem bcast_sentTo {s : RState} {a : Fin 3} {m : Msg} {o : List Out} (hid : s.id = rid32 a)
    (h : bcast s m = some o) (d : Fin 3) : sentTo gNet d o = if d = a then [] else [m] := by
  unfold bcast peerOrder sendPeer at h
  rw [hid] at h
  revert h
  obtain ⟨a, ha⟩ := a
  obtain ⟨d, hd⟩ := d
  rcases a with _ | _ | _ | a <;> rcases d with _ | _ | _ | d <;> (try omega) <;>
    simp (config := { decide := true }) [rid32, sendTo, dstOf, List.mapM_cons, sentTo] <;>
    (intro h; subst h; rfl)

/-! ## Rows and ballots -/

theorem rowOf_rid32 (a : Fin 3) : rowOf (rid32 a) = a := by
  obtain ⟨a, ha⟩ := a
  rcases a with _ | _ | _ | a <;> (try omega) <;> rfl

theorem rid32_rowOf {q : w32} (h : rowOk q = true) : rid32 (rowOf q) = q := by
  simp only [rowOk, decide_eq_true_eq] at h
  unfold rowOf rid32
  rw [dif_pos h]
  simp only [sint.Z] at h ⊢
  word

theorem rid32_inj {a b : Fin 3} (h : rid32 a = rid32 b) : a = b := by
  rw [← rowOf_rid32 a, ← rowOf_rid32 b, h]

theorem own_uniq {b : Int} {R R' : Fin 3} (h : Own b R) (h' : Own b R') : R = R' := by
  obtain ⟨k, hk, e⟩ := h
  obtain ⟨k', hk', e'⟩ := h'
  have := R.isLt; have := R'.isLt
  apply Fin.ext; omega

theorem own_pos {b : Int} {R : Fin 3} (h : Own b R) : 0 < b := by
  obtain ⟨k, hk, e⟩ := h; omega

theorem mbl_nat (b id : BitVec 32) (hid : id.toNat < 16) (h0 : b.msb = false)
    (hm : (b.sshiftRight 4).toInt < 134217727) :
    (((b.sshiftRight 4) + 1) <<< 4 ||| id).toNat = 16 * (b.toNat / 16 + 1) + id.toNat := by
  rw [BitVec.sshiftRight_eq_of_msb_false h0] at hm ⊢
  have hy : (b >>> 4).toNat = b.toNat / 16 := by simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hmsb : (b >>> 4).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [hy, decide_eq_false_iff_not]; have := b.isLt; omega
  rw [BitVec.toInt_eq_toNat_of_msb hmsb, hy] at hm
  have h1 : ((b >>> 4) + 1).toNat = b.toNat / 16 + 1 := by
    rw [BitVec.toNat_add, hy]; simp; omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, h1]
  have e : (b.toNat / 16 + 1) <<< 4 % 2 ^ 32 = (b.toNat / 16 + 1) <<< 4 := by
    rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt; omega
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt (i := 4) (by omega), Nat.shiftLeft_eq]
  omega

/-- `makeBallotLargerThan` from replica `a`: a ballot of `a`'s, above the old one. -/
theorem makeBallot_own {b : w32} {a : Fin 3} (h0 : 0 ≤ sint.Z b)
    (hm : ¬ sge (b.sshiftRight 4) maxBallotHi = true) :
    Own (sint.Z (makeBallotLargerThan (rid32 a) b)) a ∧
      sint.Z b < sint.Z (makeBallotLargerThan (rid32 a) b) := by
  have hidn : (rid32 a).toNat = a.val := by
    have := a.isLt; simp [rid32]; omega
  have hmsb : b.msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [sint.Z] at h0
    have := BitVec.toInt_eq_toNat_cond b
    simp only [decide_eq_false_iff_not]; intro hc; split at this <;> omega
  have hsl : (b.sshiftRight 4).toInt < 134217727 := by
    have : (BitVec.sshiftRight (0x7FFFFFFF : w32) 4).toInt = 134217727 := by decide
    simp only [sge, sle, maxBallotHi, decide_eq_true_eq, sint.Z, this] at hm
    omega
  have e2 := mbl_nat b (rid32 a) (by rw [hidn]; omega) hmsb hsl
  rw [hidn] at e2
  have e1b : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_msb hmsb
  have hb16 : b.toNat / 16 < 134217727 := by
    rw [BitVec.sshiftRight_eq_of_msb_false hmsb] at hsl
    have hy : (b >>> 4).toNat = b.toNat / 16 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have : (b >>> 4).toInt = (b >>> 4).toNat := by
      apply BitVec.toInt_eq_toNat_of_msb
      rw [BitVec.msb_eq_decide]; simp only [hy, decide_eq_false_iff_not]; have := b.isLt; omega
    omega
  have e0 : makeBallotLargerThan (rid32 a) b = ((b.sshiftRight 4) + 1) <<< 4 ||| rid32 a := rfl
  have hm2 : (makeBallotLargerThan (rid32 a) b).msb = false := by
    rw [BitVec.msb_eq_decide, e0]; simp only [e2]; have := a.isLt; simp; omega
  have e3 : sint.Z (makeBallotLargerThan (rid32 a) b) = 16 * (b.toNat / 16 + 1) + a.val := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_msb hm2, e0, e2]; push_cast; rfl
  refine ⟨⟨b.toNat / 16 + 1, by omega, by rw [e3]⟩, ?_⟩
  rw [e3]; simp only [sint.Z]; rw [e1b]; omega

/-! ## Ballots that only grow -/

/-- Every acceptor's ballot only grows (and no copy disappears). -/
def BalLe (bal bal' : Fin 3 → Option Int) : Prop :=
  ∀ x B, bal x = some B → ∃ B', bal' x = some B' ∧ B ≤ B'

theorem BalLe.refl (bal : Fin 3 → Option Int) : BalLe bal bal := fun _ B h => ⟨B, h, Int.le_refl B⟩

theorem BalLe.ge {bal bal' : Fin 3 → Option Int} (h : BalLe bal bal') {x : Fin 3} {b : Int}
    (hx : ∃ B, bal x = some B ∧ b ≤ B) : ∃ B, bal' x = some B ∧ b ≤ B := by
  obtain ⟨B, hB, hle⟩ := hx
  obtain ⟨B', hB', hle'⟩ := h x B hB
  exact ⟨B', hB', Int.le_trans hle hle'⟩

theorem BalLe.pos {bal bal' : Fin 3 → Option Int} (h : BalLe bal bal') {x : Fin 3}
    (hx : ∃ B, bal x = some B ∧ 0 < B) : ∃ B, bal' x = some B ∧ 0 < B := by
  obtain ⟨B, hB, hle⟩ := hx
  obtain ⟨B', hB', hle'⟩ := h x B hB
  exact ⟨B', hB', Int.lt_of_lt_of_le hle hle'⟩

section bal
variable {g : Gh Val} {bal bal' : Fin 3 → Option Int} {L : Fin 3}

theorem evolve_bal (I : AInv g bal L) (h : BalLe bal bal') : Evolve L g bal g bal' where
  le := Gh.Le.refl g
  bal_mono := h
  acc_new _ _ _ h hn := absurd h hn
  eq_new _ h hn := absurd h hn
  fast_new _ h hn := absurd h hn
  fast_cre := I.fast_cre
  fast_eq := I.fast_eq
  fast_noprop := I.fast_noprop

theorem ainv_bal (I : AInv g bal L) (h : BalLe bal bal') : AInv g bal' L :=
  { I with
    prop_safe := fun b v hp => safeAt_evolve (evolve_bal I h) (I.prop_safe b v hp)
    rst_safe := fun b hr => safeAll_evolve (evolve_bal I h) (I.rst_safe b hr) }

theorem riOk_bal {b : Int} {R : Fin 3} {ri : Option RecoveryInstance} (h : BalLe bal bal')
    (I : RIOk g bal L b R ri) : RIOk g bal' L b R ri :=
  { mem := { I.mem with bal := h.ge I.mem.bal }
    core := { I.core with lr := fun r hr hl => ⟨h.pos (I.core.lr r hr hl).1, (I.core.lr r hr hl).2⟩ }
    cnt1 := I.cnt1 }

theorem repOk_bal {b : Int} {Y : Fin 3} {m : PrepareReplyM} (h : BalLe bal bal')
    (I : RepOk g bal L b Y m) : RepOk g bal' L b Y m :=
  { I with bal := h.ge I.bal }

end bal

theorem copyOk_bal {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (hb : BalLe (balOf c q i) (balOf c1 q i)) (h : CopyOk c G q i a cp) : CopyOk c1 G q i a cp :=
  { h with
    preparing := fun lb h1 h2 h3 h4 =>
      let k := h.preparing lb h1 h2 h3 h4
      ⟨riOk_bal hb k.1, k.2⟩ }

/-- A message keeps its facts when the ballots of its instance only grow and the receiver's copy is
the old one or has a positive ballot (and a ballot-0 PreAccept keeps its multiplicity). -/
theorem msgOk_mono {c c1 : Cfg gNet} {G : GG} {d : Fin 3} {m : Msg}
    (hb : ∀ q j, msgInst m = some (q, j) → BalLe (balOf c q j) (balOf c1 q j))
    (hcp : ∀ q j, msgInst m = some (q, j) → ∀ cp', cpOf c1 d q j = some cp' →
      cpOf c d q j = some cp' ∨ 0 < sint.Z cp'.ballot)
    (hcnt : ∀ x, m = .preAccept x → (c.inflight d).count (Msg.preAccept x : gNet.M) = 1 →
      (c1.inflight d).count (Msg.preAccept x : gNet.M) = 1)
    (h : MsgOk c G d m) : MsgOk c1 G d m := by
  cases m with
  | preAccept x =>
    have e := hcp _ _ rfl
    have ec := hcnt x rfl
    unfold MsgOk at h ⊢
    refine ⟨fun hb0 => ?_, h.2⟩
    obtain ⟨k1, k2, k3, k4, k5⟩ := h.1 hb0
    refine ⟨k1, k2, k3, fun cp' hc => ?_, ec k5⟩
    rcases e cp' hc with e | e
    · exact k4 cp' e
    · exact Or.inl e
  | prepare x =>
    have e := hb _ _ rfl
    unfold MsgOk at h ⊢
    obtain ⟨k1, R, k2, k3, k4, k5⟩ := h
    exact ⟨k1, R, k2, k3, k4, e.ge k5⟩
  | prepareReply x =>
    have e := hb _ _ rfl
    unfold MsgOk at h ⊢
    refine ⟨h.1, fun ho => ?_, h.2.2⟩
    obtain ⟨k1, Y, k2, k3, k4, k5⟩ := h.2.1 ho
    exact ⟨e.ge k1, Y, k2, k3, k4, fun hn hnp => repOk_bal e (k5 hn hnp)⟩
  | _ => exact h

/-! ## Counting appended messages -/

theorem countP_app_ite {l : List Msg} {p : Msg → Bool} {b : Prop} [Decidable b] {x : Msg}
    (hx : p x = false) : (l ++ (if b then [] else [x])).countP p = l.countP p := by
  rw [List.countP_append]; split
  · rfl
  · simp [hx]

theorem countP_app_ite_le {l : List Msg} {p : Msg → Bool} {b : Prop} [Decidable b] {x : Msg} :
    (l ++ (if b then [] else [x])).countP p ≤ l.countP p + 1 := by
  rw [List.countP_append]; split
  · simp
  · simp only [List.countP_singleton]; split <;> omega

theorem countP_app_one {l : List Msg} {p : Msg → Bool} {x : Msg} (hx : p x = true) :
    (l ++ [x]).countP p = l.countP p + 1 := by
  rw [List.countP_append]; simp [hx]

/-! ## Changing the history at other instances -/

theorem copyOk_G {c : Cfg gNet} {G G' : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (h : G' q i = G q i) (I : CopyOk c G q i a cp) : CopyOk c G' q i a cp := by
  cases I; constructor <;> (try simp only [h]) <;> assumption

theorem instOk_G {c : Cfg gNet} {G G' : GG} {q i : w32} (h : G' q i = G q i)
    (I : InstOk c G q i) : InstOk c G' q i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := I
  exact ⟨h ▸ h1, fun a cp hc => copyOk_G h (h2 a cp hc), h ▸ h3, h ▸ h4, h5, h ▸ h6, h ▸ h7⟩

theorem msgOk_G {c : Cfg gNet} {G G' : GG} {d : Fin 3} {m : Msg}
    (hG : ∀ x y, msgInst m = some (x, y) → G' x y = G x y) (heq : ∀ x y, (G' x y).eq = (G x y).eq)
    (I : MsgOk c G d m) : MsgOk c G' d m := by
  cases m with
  | preAccept x => have e := hG _ _ rfl; simp only [MsgOk, e] at I ⊢; exact I
  | preAcceptReply x => have e := hG _ _ rfl; simp only [MsgOk, e] at I ⊢; exact I
  | preAcceptOK x => simp only [MsgOk, heq] at I ⊢; exact I
  | accept x => have e := hG _ _ rfl; simp only [MsgOk, e] at I ⊢; exact I
  | acceptReply x => have e := hG _ _ rfl; simp only [MsgOk, e] at I ⊢; exact I
  | commit x => have e := hG _ _ rfl; simp only [MsgOk, e] at I ⊢; exact I
  | prepare x => exact I
  | prepareReply x => have e := hG _ _ rfl; simp only [MsgOk, e] at I ⊢; exact I
  | _ => exact I

end Perennial.gryff.pureA
