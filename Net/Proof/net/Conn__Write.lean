/-
The proof of `Net/Spec/net/Conn__Write.lean`: the interface call resolves to
`conn.Write.impl` (`*TCPConn`'s promoted `Write`), Go's loop (`model.writeLoop`); each iteration
reads the bytes of `b[nn:]` and makes the extension's `Write` of them, taking the caller's accessor
(`Net.wp_net_Write`). The loop's invariant (Löb induction): `nn` bytes written, `P (bs.take nn)
none`, and `nn = 0` or fewer than all; and (D25) after the first step, the end's write lock
(`netWLock`), which the first step took and the last gives back (`writeLast`).
-/
module

public import Net.Spec.net.Conn__Write
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem Conn.Write.wp_proof : Conn.Write.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs dq ed P
  unfold connAt
  wp_start as ⟨⟨%nw, %Hnw, #Ht, #Hla, #Hra, #Hat⟩, Hsl, #Hed, HP, #Hacc⟩
  wp_method_call
  (try unfold conn.Write.impl)
  (try unfold model.connId)
  (try rw [conn_ty_eq'])
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed conn
  icases ownSlice_len b dq bs $$ Hsl with %Hlen
  icases ownSlice_wf b dq bs $$ Hsl with %Hwf
  ihave %Hne := netConnAt_endId_ne _ cn a s $$ Hat
  (try wp_auto)
  (try (rw [show decide (endId cn s = W64 0) = false by simpa using Hne]; wp_auto))
  -- the loop's invariant: `nn` bytes written, `nn = 0` or fewer than all
  obtain ⟨nn, hnn⟩ : ∃ nn : w64, nn = W64 0 := ⟨_, rfl⟩
  rw [← hnn]
  ihave HP := (show P [] none ⊢ P (bs.take nn.toNat) none by subst hnn; exact .rfl) $$ HP
  have hle : nn.toNat ≤ bs.length := by subst hnn; exact Nat.zero_le _
  have hst : nn.toNat = 0 ∨ nn.toNat < bs.length := by subst hnn; exact .inl rfl
  -- D25: after the first step the loop holds the end's write lock
  ihave Hlk : iprop(if decide (nn = W64 0) then iprop(True) else
      netWLock (extGlobalGS netExt (G := hG.goose_globalGS)) cn s) $$ []
  · subst hnn; simp only [decide_true, ↓reduceIte]; itrivial
  clear hnn
  iloeb as IH generalizing %nn %hle %hst HP Hsl HΦ Hlk
  unfold model.writeLoop model.connId model.connErr
  wp_auto
  have hslz : sint.Z b.len = bs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hblen : b.len.toNat = bs.length ∧ bs.length < 2 ^ 63 := by
    have h := BitVec.toInt_eq_toNat_cond b.len
    simp only [sint.Z] at hslz
    split at h <;> omega
  have hbig := hblen.2
  have hnnz : sint.Z nn = nn.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nn = nn.toNat := by simp [sint.nat, hnnz]
  have hsb : 0 ≤ sint.Z nn ∧ sint.Z nn ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap := by
    exact ⟨by rw [hnnz]; omega, by rw [hnnz, hslz]; omega, Hwf.2⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsb)]
  ihave ⟨Hsl1, Hsl2⟩ := (ownSlice_split_all nn b dq bs ⟨by omega, by omega⟩).1 $$ Hsl
  rw [hnnn]
  wp_apply wp_bytes_to_string _ (bs.drop nn.toNat) dq $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_split_all nn b dq bs ⟨by omega, by omega⟩).2 $$ [Hsl1 Hsl2]
  · rw [hnnn]; iframe
  -- the step
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_Write cn s a (bs.drop nn.toNat) (decide (nn = W64 0)) $$ Hat Hlk
  imod Hacc $$ %(bs.take nn.toNat) %(bs.drop nn.toNat) %(List.take_append_drop _ _) HP
    with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %k %res %d' %Hw Hend Hdir
  imod Hk $$ %k %res %d' %Hw Hend Hdir with HP
  imodintro
  iintro Hlk
  have hkle := writeOutcome_le Hw
  simp only [List.length_drop] at hkle
  have hWk : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hnk : (nn + BitVec.ofNat 64 k).toNat = nn.toNat + k := by
    rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
  have htk : bs.take nn.toNat ++ (bs.drop nn.toNat).take k = bs.take (nn.toNat + k) :=
    (List.take_add ..).symm
  rcases res with _ | e
  · -- no failure
    wp_auto
    by_cases hfull : nn + BitVec.ofNat 64 k = b.len
    · rw [decide_eq_true hfull]
      wp_auto
      have hfk : nn.toNat + k = bs.length := by
        have := congrArg BitVec.toNat hfull; rw [hnk] at this
        have h2 : b.len.toNat = bs.length := hblen.1
        omega
      iapply HΦ
      iexists bs, none
      rw [htk, hfk, List.take_length]
      iframe HP Hsl
      isplitr
      · ipureintro
        refine ⟨List.prefix_refl _, ?_, fun _ => rfl, fun _ => .inl rfl⟩
        rw [← hfk, ← hnk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · unfold resErr; ipureintro; rfl
    · rw [decide_eq_false hfull]
      wp_pure
      have hlt : nn.toNat + k < bs.length := by
        have h2 : b.len.toNat = bs.length := hblen.1
        have : nn.toNat + k ≠ bs.length := by
          intro hc; apply hfull; apply BitVec.eq_of_toNat_eq; rw [hnk, h2]; exact hc
        omega
      have hk1 : 1 ≤ k := writeOutcome_none_pos Hw (by
        intro h; have := congrArg List.length h; simp at this; omega)
      have hwl : writeLast (bs.drop nn.toNat) k none = false := by
        simp only [writeLast, Option.isSome_none, Bool.false_or, decide_eq_false_iff_not,
          List.length_drop]; omega
      have hnz : decide (nn + BitVec.ofNat 64 k = W64 0) = false := by
        rw [decide_eq_false_iff_not]; intro h0
        have := congrArg BitVec.toNat h0; rw [hnk] at this; simp at this; omega
      rw [hwl] at *
      rw [htk] at *
      iapply IH $$ %(nn + BitVec.ofNat 64 k) %(by rw [hnk]; omega) %(.inr (by rw [hnk]; exact hlt))
        [HP] Hsl HΦ [Hlk]
      · rw [hnk]; iexact HP
      · rw [hnz]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hlk
  · -- a failure: nothing counted
    obtain rfl := writeOutcome_fail Hw
    wp_auto
    have hne : errCode (some e) ≠ W64 0 := by cases e <;> decide
    rw [decide_eq_false hne]
    wp_auto
    rw [show nn + 0#64 = nn from BitVec.add_zero nn, List.take_zero, List.append_nil]
    have hpure : bs.take nn.toNat <+: bs ∧ nn = BitVec.ofNat 64 (bs.take nn.toNat).length ∧
        (some e = none → bs.take nn.toNat = bs) ∧
        (bs.take nn.toNat = bs → some e = none ∨ bs = []) := by
      refine ⟨List.take_prefix _ _, ?_, fun h => (by cases h), fun h => .inr ?_⟩
      · rw [List.length_take, Nat.min_eq_left hle, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · have := congrArg List.length h
        rw [List.length_take] at this
        apply List.eq_nil_of_length_eq_zero
        omega
    cases e
    · wp_apply wp_kindErr .closed (some ed) go!"write" (· = go!"write") rfl rfl $$ [] as %e #He
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists bs.take nn.toNat, some .closed
      iframe HP Hsl
      isplitr; · ipureintro; exact hpure
      unfold resErr
      iexists e
      iframe Herr He
    · wp_apply wp_kindErr .timeout (some ed) go!"write" (· = go!"write") rfl rfl $$ [Hed] as %e #He
      · iexact Hed
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists bs.take nn.toNat, some .timeout
      iframe HP Hsl
      isplitr; · ipureintro; exact hpure
      unfold resErr
      iexists e
      iframe Herr He
    · wp_apply wp_kindErr .sys (some ed) go!"write" (· = go!"write") rfl rfl $$ [] as %e #He
      (try wp_auto)
      (try unfold model.connNet)
      (try wp_auto)
      wp_apply wp_opError $$ %Hnw as %err #Herr
      iapply HΦ
      iexists bs.take nn.toNat, some .sys
      iframe HP Hsl
      isplitr; · ipureintro; exact hpure
      unfold resErr
      iexists e
      iframe Herr He

end proof

end net
end Perennial
