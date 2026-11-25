/- Lean-first (no Rocq counterpart).

# The supply of `Repair`'s truncate at the end of the frames it read (P6, E4)

`Repair` truncates its registered tail (the pending token, kind `true`) at the decoder's last offset
(repair.go:86), `tg ∈ [wr, size]`: past the stream's end `wr` when the frames end in a pending run (entry
records no state record follows, since the torn-`Save` fix). `walTail_truncSupR` is `walTail_truncSup`
(`TruncSup.lean`) at that target:

* the caller's state property `P` says the size is the one `Repair` found or the target (the retries'
  states, `os.File.Truncate.specAu`), so `tg ≤ size` at every attempt; and, at `tg = wr`, `LoWr` (the
  F-Z start at `wr`, `rzStart_pureK`);
* the tie `repTie` is the key and the tail record's half, and, past `wr`, the caller's half of a nonzero
  byte of the run in `[wr, tg)` (the length word of its first frame): with F-Z (`TailZeros`) every byte
  from `wr` on is zero (`WalAbsD.zeroPast`), so F-Z and `tg > wr` cannot meet; the start from `RepOld` is
  `rzStart_pureRT`;
* the finish is `walTail_truncFin` at `tg`, the byte framed (`osAUnc_frameW`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSup

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **A resource framed into an `osAUnc`'s result** (coinduction). -/
theorem osAUnc_frameW {A : Type} (α : IProp GF) (β Q Q' : A → IProp GF) (Fr : IProp GF) :
    ⊢ □ (∀ o, Q o ∗ Fr -∗ Q' o) -∗ Fr -∗ osAUnc α β Q -∗ osAUnc α β Q' := by
  iintro #HQ HF Hau
  ihave HP : Fr ∗ osAUnc α β Q $$ [HF Hau]
  · isplitl [HF]
    · iexact HF
    · iexact Hau
  iapply osAUnc_coiter α β Q' iprop(Fr ∗ osAUnc α β Q) $$ [] HP
  iintro !> ⟨HF, Hau⟩
  ihave Hp := osAUnc_unfold α β Q $$ Hau
  unfold osAUncPre
  iintro Hnc
  imod Hp $$ Hnc with ⟨Hα, Hnc, Hcl⟩
  imodintro
  iframe Hα Hnc
  isplit
  · icases Hcl with ⟨Hcl, -⟩
    iintro Hα
    imod Hcl $$ Hα with Hau
    imodintro
    isplitl [HF]
    · iexact HF
    · iexact Hau
  · icases Hcl with ⟨-, Hcl⟩
    iintro %o Hb
    imod Hcl $$ %o Hb with HQo
    imodintro
    iapply HQ $$ [HQo HF]
    isplitl [HQo]
    · iexact HQo
    · iexact HF

/-- **A byte held at `b` is the byte a run from 0 has there.** -/
theorem osBytes_agree_at (i : Ino) (dq dq' : DFrac) (bs : List ByteG) (b : Nat) (x : ByteG)
    (hb : b < bs.length) :
    ⊢ (osBytes i 0 dq bs : IProp GF) -∗ osBytes i b dq' [x] -∗ ⌜bs[b]? = some x⌝ := by
  iintro Hbs Hx
  icases (osBytes_takeDrop i dq bs b (by omega)).1 $$ Hbs with ⟨-, Hbd⟩
  have e : bs.drop b = [bs[b]] ++ bs.drop (b + 1) := by
    rw [List.singleton_append, List.drop_eq_getElem_cons hb]
  rw [e]
  iunfold osBytes at Hbd
  icases (bytesG_append _ _ _ _ _ _).1 $$ Hbd with ⟨H1, -⟩
  ihave %hxx := osBytes_agree i dq dq' b [bs[b]] [x] rfl $$ [H1] [Hx]
  · unfold osBytes; iexact H1
  · iexact Hx
  simp only [List.cons.injEq, and_true] at hxx
  ipureintro; rw [List.getElem?_eq_getElem hb, hxx]

/-- **`Repair`'s tie** (see the file header): the pending token and the tail record's half, and, the
target past `wr`, the caller's half of a nonzero byte in `[wr, tg)`. -/
def repTie (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (tg : Nat) : IProp GF :=
  iprop(walTailKeyL (W := W) dir γ (some (k, true)) ∗ tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) ∗
    (⌜tg = wr⌝ ∨ ∃ (b : Nat) (x : ByteG), ⌜wr ≤ b ∧ b < tg ∧ x.1 ≠ 0⌝ ∗
      osBytes i b (DFrac.own (1 : Qp).half) [x]))

/-- **`Repair`'s state property**: the size it found (`S0`) or the target, and `LoWr` at `tg = wr`. -/
def RepP (wr tg S0 : Nat) (m : OsMeta) : Prop :=
  (tg = wr → LoWr m wr) ∧ (m.size = S0 ∨ m.size = tg)

/-- The caller's part of the start's update (`truncStartP` with `repTie`). -/
def truncStartPR (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (tg : Nat) (m0 : OsMeta) (xs0 : List ByteG) : IProp GF :=
  iprop(repTie (W := W) dir γ k H md cuts wr i tg ∗
    osMeta i (DFrac.own (1 : Qp).half) m0 ∗ osBytes i (min m0.size tg) (DFrac.own (1 : Qp).half) xs0)

/-- **F-Z and a nonzero byte past `wr` cannot meet** (`WalAbsD.zeroPast`). -/
theorem repTie_nz {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents} {g0 : SegG}
    {wr tg : Nat} (habs : WalAbsD C Mr d lay ents) (hg0 : lay.segs.getLast? = some g0)
    (hwr : lay.wr = wr) (htg : tg ≤ g0.bs.length) :
    ⊢ (osBytes g0.ino 0 (DFrac.own (1 : Qp).half) g0.bs : IProp GF) -∗
      (⌜tg = wr⌝ ∨ ∃ (b : Nat) (x : ByteG), ⌜wr ≤ b ∧ b < tg ∧ x.1 ≠ 0⌝ ∗
        (osBytes g0.ino b (DFrac.own (1 : Qp).half) [x] : IProp GF)) -∗
      ⌜tg = wr ∨ ¬ TailZeros lay⌝ := by
  iintro Hb HNZ
  icases HNZ with (%he | ⟨%b, %x, %hbx, Hx⟩)
  · ipureintro; exact .inl he
  · icases osBytes_agree_at (GF := GF) g0.ino _ _ g0.bs b x (by omega) $$ Hb Hx with %hgb
    ipureintro
    right
    intro hZ0
    exact hbx.2.2 (habs.zeroPast g0 hg0 hZ0 b x (by rw [hwr]; exact hbx.1) hgb)

/-- **The supply of `Repair`'s truncate at `tg ∈ [wr, S0]`** (see the file header). -/
theorem walTail_truncSupR (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (i : Ino) (tg S0 : Nat)
    (hS : wr = (tailStream Mr H md cuts).length) (hwt : wr ≤ tg) (htS : tg ≤ S0) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      os.truncSup (repTie (W := W) dir γ k H md cuts wr i tg) i tg (RepP wr tg S0) := by
  iintro #Hinv
  unfold os.truncSup
  iintro !> %m0 %xs0 %hxs0 %hP0 HK Hm Hbx
  unfold os.truncAuW
  ihave HP : truncStartPR (W := W) dir γ k H md cuts wr i tg m0 xs0 $$ [HK Hm Hbx]
  · unfold truncStartPR; iframe
  iapply osAUnc_coiter _ _ _ (truncStartPR (W := W) dir γ k H md cuts wr i tg m0 xs0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold truncStartPR repTie
  icases HP with ⟨⟨Hk, Hv, HNZ⟩, Hm, Hbx⟩
  icases walInvBody_tailW walCodec Mr R jr r s dir γ (some (k, true)) _ m0 $$ Hb Hk Hv [Hm] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hm, Hclose⟩
  · dsimp only [tailHeld]; iexact Hm
  dsimp only [tailHeld]
  obtain ⟨hd, hl, hs, htg0, hW, ⟨ents, habs⟩, hcut0, hZ, hB, -⟩ := hp
  have htgv := htg0
  simp only [tailG, Prod.mk.injEq] at htgv
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htgv
  ihave Hv' : tailVar (W := W) γ (tailG d lay g0.ino (F !! g0.ino)) $$ [Hv']
  · rw [← htg0]; iexact Hv'
  have eseg : segResF (GF := GF) F g0 = iprop(osMeta g0.ino (DFrac.own (1 : Qp).half) g0.om ∗
      osBytes g0.ino 0 (DFrac.own (1 : Qp).half) g0.bs) := by
    unfold segResF segRes; rw [← hF]
  rw [eseg]
  icases Hseg with ⟨Hm2, Hb2⟩
  subst hino
  icases osMeta_agree2 _ _ _ _ _ $$ Hm2 Hm with %hmm
  subst hmm
  have hg0m : g0 ∈ lay.segs := by rw [hs]; simp
  have hg0l : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, -, -, hhi0, -⟩ := habs.metas g0 hg0m
  obtain ⟨hso, -, -, hwb, -⟩ := habs.lastWin g0 hg0l
  have hso0 := walAbsD_so_pos habs
  have htg : tg ≤ g0.om.size := by rcases hP0.2 with h | h <;> omega
  have hmin : min g0.om.size tg = tg := Nat.min_eq_right htg
  have hwrl' : lay.wr = wr := hwrl.symm
  -- F-Z past `wr` and a nonzero byte of the run there cannot meet
  icases repTie_nz habs hg0l hwrl' (by omega) $$ Hb2 HNZ with %hZR
  icases (osBytes_takeDrop g0.ino _ g0.bs (min g0.om.size tg) (by omega)).1 $$ Hb2 with ⟨Hbt, Hbd⟩
  icases osBytes_agree g0.ino _ _ (min g0.om.size tg) (g0.bs.drop (min g0.om.size tg)) xs0
    (by rw [List.length_drop, hxs0]; omega) $$ Hbd Hbx with %hxx
  subst hxx
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  isplitl [Hm Hm2 Hbd Hbx]
  · isplitl [Hm Hm2]
    · iapply (osMeta_halves _ _).2; iframe
    · iapply (osBytes_halves _ _ _).2; iframe
  iframe Hnc
  isplit
  · -- abort
    iintro ⟨HmA, HbA⟩
    imod Hcl'
    icases (osMeta_halves _ _).1 $$ HmA with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ HbA with ⟨Hb1, Hb2⟩
    ihave Hseg : segResF F g0 $$ [Hm2 Hbt Hb2]
    · rw [eseg]
      iframe Hm2
      iapply (osBytes_takeDrop g0.ino _ g0.bs (min g0.om.size tg) (by omega)).2
      iframe
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g0 hW hl hs
      (some (k, true)) hZ.rk $$ Hclose Hseg Hv'
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    iframe
  · iintro %tn Hβ
    rcases tn with ⟨t, n⟩
    dsimp only
    icases Hβ with ⟨Htok, %hn⟩
    imod Hcl'
    have hS' : (segStream walCodec Mr d lay.cuts lay.cuts.length).length = lay.wr := by
      rw [hwrl', hS, hH, hmd, hcuts, tailStream_eq]
    have hRK : TailZeros lay ∨ RepOld lay := (hZ : TailZ0 lay ∧ (TailZeros lay ∨ RepOld lay)).2
    obtain ⟨hW', hDK', hR'⟩ : WalsOk walCodec Mr R jr s
        (<[dir := tailLay lay pre (rzSeg g0 true tg n) lay.wr]> Ls) cl nn ∧
        (∀ K c, DirKeysOk walCodec Mr jr s Ls cl nn K c →
          DirKeysOk walCodec Mr jr s (<[dir := tailLay lay pre (rzSeg g0 true tg n) lay.wr]> Ls) cl nn K c) ∧
        TailRK (some (k, true)) (tailLay lay pre (rzSeg g0 true tg n) lay.wr) := by
      rcases hRK with hZ0 | hR0
      · rcases hZR with he | hnZ
        · subst he
          have hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr := fun hx => by
            rcases hP0.1 rfl with h | h
            · exact absurd (SegExact.of_os hsz h) hx
            · rw [hwrl']; exact h
          rw [← hwrl']
          exact rzStart_pureK walCodec_ok hW hd hl hs ⟨ents, habs⟩ hcut0 hZ (fun _ => hS') hB hn.1 hn.2 hlo
        · exact absurd hZ0 hnZ
      · obtain ⟨h1, h2, h3⟩ := rzStart_pureRT walCodec_ok hW hd hl hs ⟨ents, habs⟩ hcut0 hR0 hS' hn.1 hn.2
          (by rw [hwrl']; exact hwt) htg
        exact ⟨h1, h2, Or.inr h3⟩
    rw [hwrl'] at hW' hDK' hR'
    have hFi : ∀ i, i ≠ g0.ino →
        (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! i = F !! i :=
      fun i hi => GMap.lookup_insert_ne _ _ (Ne.symm hi)
    have hFg : (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! g0.ino =
        some ⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ := GMap.lookup_insert _ _ _
    have etg : tailG d (tailLay lay pre (rzSeg g0 true tg n) wr) (rzSeg g0 true tg n).ino
        ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! (rzSeg g0 true tg n).ino) =
        ((H, md, cuts, wr, g0.ino, some ⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩) : TailG) := by
      rw [show (rzSeg g0 true tg n).ino = g0.ino from rfl, hFg]; simp [tailG, tailLay, hH, hmd, hcuts]
    imod tailVar_upd γ _ _ (tailG d (tailLay lay pre (rzSeg g0 true tg n) wr) (rzSeg g0 true tg n).ino
      ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! (rzSeg g0 true tg n).ino))
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    ihave Hb := Hclose $$ %(rzSeg g0 true tg n) %wr
      %(<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) [] [Htok Hbt] Hv'
    · ipureintro; exact ⟨rfl, rfl, hFi, Or.inl hwrl'.symm, hW', hDK', hR'⟩
    · unfold segResF
      rw [show (rzSeg g0 true tg n).ino = g0.ino from rfl, hFg]
      dsimp only
      iframe
      ipureintro
      exact rzSeg_ok hsz.symm hcut0 (by omega)
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    rw [etg]
    ihave Hfin := walTail_truncFin Mr R jr r dir γ (some (k, true)) H md cuts wr tg g0.ino t n g0.om g0.bs
      $$ Hinv [Hk Hv]
    · unfold truncFinP
      iframe
      ipureintro; exact ⟨by omega, htg, hwt⟩
    iapply osAUnc_frameW _ _ _ _ _ $$ [] HNZ Hfin
    iintro !> %e ⟨⟨Ho, Hk, Hv⟩, HNZ⟩
    iframe

end au

end WalFs
end EtcdGrove
end Perennial

end
