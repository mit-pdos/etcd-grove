/- Lean-first (no Rocq counterpart).

# The supply of the tail's truncate at its write position (I3b, `wal-tc10`)

`walTail_truncSup`: `os.truncSup` (`LinuxFs/Spec/os/File__TruncateAu.lean`) for the truncate of a WAL's
tail `i` to its write position `wr`, built from `walInv`, the caller's tie `K` its key and half of the
tail record, idle (`walTailKeyL dir γ ok ∗ tailVar γ (H, md, cuts, wr, i, none)`: its key, or the
token of the tail lent, `ZeroToEnd`'s). Each attempt:

* *the start's update* opens `walInv` (`walInvBody_tailW`), agrees the tail's halves with the caller's
  (the `OsMeta` `m0`, the bytes cut off `xs0`: `g0.om = m0`, `g0.bs.drop wr = xs0`), and lends the whole
  of both; it commits with the token: the invariant takes it (a resize in flight, `SegFl`, `segResF`), the
  layout's tail becomes `rzSeg g0 true wr n` (`rzStart_pure`), both halves of the tail record carry the
  change in flight; the caller's part of the second update is its key and half of the record (and the
  facts of the start it needs at the landing);
* *the finish's update* lends the token back; it commits with the outcome (`rsOutT`): landed, the tail
  `rzLand` (`rzLand_pure`), the caller's halves `os.ftDoneH` (its `tc` the outcome's `rsTail`, so
  `TcKnows.rsTail`); not landed, the in-flight layout kept, idle, the caller's halves `os.ftUndoneH`;
  the record back to idle, and `K`.

An abort (either update) leaves the invariant as it was (`walInvBody_tailW_same`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSupPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAccW
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Spec.os.File__TruncateAu

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

/-- A file's bytes from 0, split at `k`. -/
theorem osBytes_takeDrop (p : Ino) (dq : DFrac) (bs : List ByteG) (k : Nat) (hk : k ≤ bs.length) :
    (osBytes p 0 dq bs : IProp GF) ⊣⊢ osBytes p 0 dq (bs.take k) ∗ osBytes p k dq (bs.drop k) := by
  have e : (osBytes p 0 dq bs : IProp GF) = osBytes p 0 dq (bs.take k ++ bs.drop k) := by
    rw [List.take_append_drop]
  rw [e]
  unfold osBytes
  refine (bytesG_append _ _ _ _ _ _).trans ?_
  rw [List.length_take, Nat.min_eq_left hk, Nat.zero_add]
  exact ⟨.rfl, .rfl⟩

/-- **The tail's access, nothing changed** (an abort): `walInvBody_tailW`'s continuation at the tail,
the write position and the changes in flight it found. -/
theorem walInvBody_tailW_same (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName)
    (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (F : GMap Ino SegFl) (d : WalDur)
    (lay : WalLay) (pre : List SegG) (g0 : SegG)
    (hW : WalsOk C Mr R jr s Ls cl n) (hl : Ls !! dir = some lay) (hs : lay.segs = pre ++ [g0]) :
    ⊢ (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g0.ino ∧ g.name = g0.name ∧ (∀ i, i ≠ g0.ino → F' !! i = F !! i) ∧
            (wr' = lay.wr ∨ TailZeros lay) ∧
            WalsOk C Mr R jr s (<[dir := tailLay lay pre g wr']> Ls) cl n ∧
            (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
              DirKeysOk C Mr jr s (<[dir := tailLay lay pre g wr']> Ls) cl n K c)⌝ -∗
          segResF F' g -∗
          tailVar (W := W) γ (tailG d (tailLay lay pre g wr') g.ino (F' !! g.ino)) -∗
          walInvBody (W := W) C Mr R jr r s) -∗
      segResF F g0 -∗ tailVar (W := W) γ (tailG d lay g0.ino (F !! g0.ino)) -∗
      walInvBody (W := W) C Mr R jr r s := by
  iintro Hclose Hseg Hv
  have hp := walsOk_self (g := g0) hW hl hs
  iapply Hclose $$ %g0 %lay.wr %F [] Hseg
  · ipureintro; exact ⟨rfl, rfl, fun _ _ => rfl, Or.inl rfl, hp.1, hp.2⟩
  rw [tailLay_self hs]
  iexact Hv

theorem tailVar_upd (γ : GName) (a1 a2 b : TailG) :
    ⊢ tailVar (W := W) γ a1 -∗ tailVar (W := W) γ a2 ==∗ tailVar (W := W) γ b ∗ tailVar (W := W) γ b := by
  letI := walAllG (W := W)
  unfold tailVar
  exact ghostVar_update_halves _ _ _ _

theorem osMeta_agree2 (i : Ino) (dq1 dq2 : DFrac) (m1 m2 : OsMeta) :
    ⊢ (osMeta i dq1 m1 : IProp GF) -∗ osMeta i dq2 m2 -∗ ⌜m1 = m2⌝ := by
  unfold osMeta
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %Hv
  ipureintro; exact Hv.2

/-- Bytes from 0 joined. -/
theorem osBytes_app0 (p : Ino) (dq : DFrac) (xs ys : List ByteG) :
    (osBytes p 0 dq xs : IProp GF) ∗ osBytes p xs.length dq ys ⊢ osBytes p 0 dq (xs ++ ys) := by
  unfold osBytes
  refine Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
  rw [Nat.zero_add]

/-- The tail announced by a truncate in flight is `rzSeg` of the tail as the change found it. -/
theorem rzSeg_of_okR {g1 : SegG} {t n wr : Nat} {m0 : OsMeta} {bs0 : List ByteG}
    (hok : SegFl.OkR ⟨t, 0, [], n, m0, bs0, some (true, wr)⟩ true wr g1) :
    g1 = rzSeg ({ g1 with om := m0, bs := bs0 } : SegG) true wr n := by
  obtain ⟨-, -, hom, hbs, -⟩ := hok
  cases g1
  simp only [rzSeg] at hom hbs ⊢
  rw [hom, hbs]

/-- **The caller's part of the finish's update**: its key and half of the tail record, the truncate in
flight on it (the start's `t`, `n`, the `OsMeta` and bytes it found), and the start's facts. -/
def truncFinP (dir : GoString) (γ : GName) (ok : Option (Nat × Bool)) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (i : Ino) (t n : Nat) (m0 : OsMeta) (bs0 : List ByteG) : IProp GF :=
  iprop(walTailKeyL (W := W) dir γ ok ∗
    tailVar (W := W) γ ((H, md, cuts, wr, i, some ⟨t, 0, [], n, m0, bs0, some (true, wr)⟩) : TailG) ∗
    ⌜m0.size ≤ m0.hi ∧ wr ≤ m0.size⌝)

/-- **The finish's update** (see the file header). -/
theorem walTail_truncFin (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (ok : Option (Nat × Bool)) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat) (i : Ino)
    (t n : Nat) (m0 : OsMeta) (bs0 : List ByteG) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗ truncFinP (W := W) dir γ ok H md cuts wr i t n m0 bs0 -∗
      osAUnc (A := w64) (rsTok true t i wr m0 (bs0.drop (min m0.size wr)) n)
        (rsOutT i wr m0 (bs0.drop (min m0.size wr)) n)
        (fun e => iprop(os.truncOutH i wr m0 (bs0.drop (min m0.size wr)) n e ∗
          (walTailKeyL (W := W) dir γ ok ∗ tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG)))) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (truncFinP (W := W) dir γ ok H md cuts wr i t n m0 bs0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold truncFinP
  icases HP with ⟨Hk, Hv, %hf⟩
  obtain ⟨hhi, hwr⟩ := hf
  icases walInvBody_tailW walCodec Mr R jr r s dir γ ok _ m0 $$ Hb Hk Hv [] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g1, %hp, Hseg, Hk, Hv, Hv', -, Hclose⟩
  · dsimp only [tailHeld]; iempintro
  obtain ⟨hd, hl, hs, htg0, hW, ⟨ents, habs⟩, hcut1, hZ, hB, -⟩ := hp
  have htg := htg0
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
  ihave Hv' : tailVar (W := W) γ (tailG d lay g1.ino (F !! g1.ino)) $$ [Hv']
  · rw [← htg0]; iexact Hv'
  have eseg : segResF (GF := GF) F g1 = iprop(rsTok true t g1.ino wr m0 (bs0.drop (min m0.size wr)) n ∗
      osBytes g1.ino 0 (DFrac.own (1 : Qp).half) (bs0.take (min m0.size wr)) ∗
      ⌜SegFl.OkR ⟨t, 0, [], n, m0, bs0, some (true, wr)⟩ true wr g1⌝) := by
    unfold segResF; rw [← hF]
  rw [eseg]
  icases Hseg with ⟨Htok, Hbt, %hok⟩
  have hok' := hok
  obtain ⟨hlen0, hmcut, -, -, -⟩ := hok'
  subst hino
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  isplitl [Htok]
  · iexact Htok
  iframe Hnc
  isplit
  · -- abort
    iintro Htok
    imod Hcl'
    ihave Hseg : segResF F g1 $$ [Htok Hbt]
    · rw [eseg]; iframe; ipureintro; exact hok
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g1 hW hl hs
      $$ Hclose Hseg Hv'
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    dsimp only
    iframe Hk Hv
    ipureintro; exact ⟨hhi, hwr⟩
  · iintro %e Hout
    imod Hcl'
    have hmcut' : m0.cut = none := hmcut
    have hlen : bs0.length = m0.size := hlen0
    have hmin : min m0.size wr = wr := Nat.min_eq_right hwr
    have hg1 := rzSeg_of_okR hok
    obtain ⟨hlenOk, -, hom, hbs, -⟩ := hok
    obtain ⟨g0', hg0'⟩ : ∃ g0' : SegG, g0' = { g1 with om := m0, bs := bs0 } := ⟨_, rfl⟩
    rw [← hg0'] at hg1
    have hg0om : g0'.om = m0 := by rw [hg0']
    have hg0bs : g0'.bs = bs0 := by rw [hg0']
    have hFd : ∀ i, i ≠ g1.ino → (GMap.delete g1.ino F) !! i = F !! i :=
      fun i hi => GMap.lookup_delete_ne _ (Ne.symm hi)
    ihave Hout : rsDoneK true true g1.ino wr wr m0 (bs0.drop (min m0.size wr)) n ∨
        (⌜e ≠ 0⌝ ∗ rsUndoneK true true g1.ino wr m0 (bs0.drop (min m0.size wr)) n) $$ [Hout]
    · unfold rsOutT
      rw [show m0.cut.isNone = true by simp [hmcut']]
      icases Hout with (⟨-, Hd⟩ | ⟨%he, (Hd | Hu)⟩)
      · ileft; iexact Hd
      · ileft; iexact Hd
      · iright; iframe Hu; ipureintro; exact he
    icases Hout with (Hd | ⟨%he, Hu⟩)
    · -- landed: the tail `rzLand`
      unfold rsDoneK
      icases Hd with ⟨%zs, %hzs, Hm, -, -⟩
      icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
      have hs' : lay.segs = pre ++ [rzSeg g0' true lay.wr n] := by rw [hs, ← hwrl, ← hg1]
      obtain ⟨hW', hDK'⟩ := rzLand_pure (k := n) hW hd hl hs' (by rw [hg0om, hg0bs]; exact hlen)
        (by rw [hg0om, ← hwrl]; exact hwr) (by rw [hg0om]; exact hhi) (by rw [hg0om]; exact hmcut')
      have e1 : rzLand g0' lay.wr n = ({ g1 with
          om := rsPostK true true m0 wr wr n (bs0.drop (min m0.size wr))
          bs := bs0.take (min m0.size wr) } : SegG) := by
        subst hg0'; rw [← hwrl, hmin]; rfl
      have etg : tailG d (tailLay lay pre (rzLand g0' lay.wr n) lay.wr) (rzLand g0' lay.wr n).ino
          ((GMap.delete g1.ino F) !! (rzLand g0' lay.wr n).ino) = ((H, md, cuts, wr, g1.ino, none) : TailG) := by
        rw [e1]; simp [tailG, tailLay, GMap.lookup_delete_eq, hH, hmd, hcuts, hwrl]
      imod tailVar_upd γ _ _ (tailG d (tailLay lay pre (rzLand g0' lay.wr n) lay.wr) (rzLand g0' lay.wr n).ino
        ((GMap.delete g1.ino F) !! (rzLand g0' lay.wr n).ino)) $$ Hv Hv' with ⟨Hv, Hv'⟩
      ihave Hb := Hclose $$ %(rzLand g0' lay.wr n) %lay.wr %(GMap.delete g1.ino F) [] [Hm2 Hbt] Hv'
      · ipureintro; exact ⟨by rw [e1], by rw [e1], hFd, Or.inl rfl, hW', hDK'⟩
      · have hn : (GMap.delete g1.ino F) !! (rzLand g0' lay.wr n).ino = none := by
          rw [e1]; exact GMap.lookup_delete_eq _ _
        unfold segResF; rw [hn]; dsimp only
        unfold segRes
        rw [e1]
        iframe
      imod Hcl $$ [Hb]
      · iexists s; iexact Hb
      imodintro
      dsimp only
      rw [etg]
      iframe Hk Hv
      ihave Hdone : ∃ zs, os.ftDoneH g1.ino m0 wr zs $$ [Hm1]
      · iexists []
        unfold os.ftDoneH
        isplitr
        · ipureintro; simp only [List.length_nil]; omega
        isplitl [Hm1]
        · iexists (rsPostK true true m0 wr wr n (bs0.drop (min m0.size wr))).tc
          iexists (rsPostK true true m0 wr wr n (bs0.drop (min m0.size wr))).rz
          isplitr
          · ipureintro; exact ⟨TcKnows.rsTail m0 wr wr n _, TcFrom.rsTail m0 wr wr n _⟩
          rw [← rsPostK_withTc]; iexact Hm1
        simp only [List.map_nil]
        unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
      unfold os.truncOutH
      by_cases he0 : e = 0
      · ileft; isplitr
        · ipureintro; exact he0
        iexact Hdone
      · iright; isplitr
        · ipureintro; exact he0
        ileft; iexact Hdone
    · -- not landed: the in-flight layout kept, idle
      unfold rsUndoneK
      icases Hu with ⟨Hm, Hb, -⟩
      icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
      obtain ⟨hW', hDK'⟩ := walsOk_self (g := g1) hW hl hs
      have etg : tailG d (tailLay lay pre g1 lay.wr) g1.ino ((GMap.delete g1.ino F) !! g1.ino) =
          ((H, md, cuts, wr, g1.ino, none) : TailG) := by
        simp [tailG, tailLay, GMap.lookup_delete_eq, hH, hmd, hcuts, hwrl]
      imod tailVar_upd γ _ _ (tailG d (tailLay lay pre g1 lay.wr) g1.ino
        ((GMap.delete g1.ino F) !! g1.ino)) $$ Hv Hv' with ⟨Hv, Hv'⟩
      ihave Hb := Hclose $$ %g1 %lay.wr %(GMap.delete g1.ino F) [] [Hm2 Hbt Hb2] Hv'
      · ipureintro; exact ⟨rfl, rfl, hFd, Or.inl rfl, hW', hDK'⟩
      · unfold segResF; rw [GMap.lookup_delete_eq]; dsimp only
        unfold segRes
        have hom' : g1.om = rsUnMeta true true m0 wr n := hom
        have hbs' : g1.bs = bs0.take (min m0.size wr) ++ rsAnn n (bs0.drop (min m0.size wr)) := hbs
        rw [hom', hbs']
        iframe Hm2
        have hl1 : (bs0.take (min m0.size wr)).length = min m0.size wr := by
          rw [List.length_take]; omega
        iapply osBytes_app0
        rw [hl1]
        iframe
      imod Hcl $$ [Hb]
      · iexists s; iexact Hb
      imodintro
      dsimp only
      rw [etg]
      iframe Hk Hv
      unfold os.truncOutH
      iright; isplitr
      · ipureintro; exact he
      iright
      unfold os.ftUndoneH
      isplitl [Hm1]
      · iexists (rsTail true m0 wr m0.size n [])
        iexists (n :: m0.rz)
        isplitr
        · ipureintro; exact ⟨TcKnows.rsTail m0 wr m0.size n [], TcFrom.rsTail m0 wr m0.size n []⟩
        have eU : rsUnMeta true true m0 wr n = (m0.announce (min m0.size wr) (rsHi true m0.size wr) wr).withTc
            (rsTail true m0 wr m0.size n []) (n :: m0.rz) := rfl
        rw [← eU]; iexact Hm1
      iexact Hb1

/-- **The caller's part of the start's update**: its tie, and its halves of the tail's `OsMeta` and of
the bytes cut off. -/
def truncStartP (dir : GoString) (γ : GName) (ok : Option (Nat × Bool)) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (i : Ino) (m0 : OsMeta) (xs0 : List ByteG) : IProp GF :=
  iprop(walTailKeyL (W := W) dir γ ok ∗ tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) ∗
    osMeta i (DFrac.own (1 : Qp).half) m0 ∗ osBytes i (min m0.size wr) (DFrac.own (1 : Qp).half) xs0)

/-- **The supply of the tail's truncate at its write position** (see the file header), the caller's
property of the state it starts from the handle's `LoWr` (no window open, or `lo ≤ wr`: a window's
crash sizes from `lo` on must be the old window's; a later attempt's state has `lo ≤ wr`,
`os.truncSup`). -/
theorem walTail_truncSup (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (ok : Option (Nat × Bool)) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat) (i : Ino)
    (hok : ∀ k p, ok ≠ some (k, p)) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      os.truncSup iprop(walTailKeyL (W := W) dir γ ok ∗ tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG))
        i wr (fun m => LoWr m wr) := by
  iintro #Hinv
  unfold os.truncSup
  iintro !> %m0 %xs0 %hxs0 %hP0 ⟨Hk, Hv⟩ Hm Hbx
  unfold os.truncAuW
  ihave HP : truncStartP (W := W) dir γ ok H md cuts wr i m0 xs0 $$ [Hk Hv Hm Hbx]
  · unfold truncStartP; iframe
  iapply osAUnc_coiter _ _ _ (truncStartP (W := W) dir γ ok H md cuts wr i m0 xs0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold truncStartP
  icases HP with ⟨Hk, Hv, Hm, Hbx⟩
  icases walInvBody_tailW walCodec Mr R jr r s dir γ ok _ m0 $$ Hb Hk Hv [Hm] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hm, Hclose⟩
  · dsimp only [tailHeld]; iexact Hm
  dsimp only [tailHeld]
  obtain ⟨hd, hl, hs, htg0, hW, ⟨ents, habs⟩, hcut0, hZ, hB, -⟩ := hp
  have htg := htg0
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
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
  have hwr : wr ≤ g0.om.size := by omega
  have hmin : min g0.om.size wr = wr := Nat.min_eq_right hwr
  icases (osBytes_takeDrop g0.ino _ g0.bs (min g0.om.size wr) (by omega)).1 $$ Hb2 with ⟨Hbt, Hbd⟩
  icases osBytes_agree g0.ino _ _ (min g0.om.size wr) (g0.bs.drop (min g0.om.size wr)) xs0
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
      iapply (osBytes_takeDrop g0.ino _ g0.bs (min g0.om.size wr) (by omega)).2
      iframe
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g0 hW hl hs
      $$ Hclose Hseg Hv'
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    iframe
  · iintro %tn Hβ
    rcases tn with ⟨t, n⟩
    dsimp only
    icases Hβ with ⟨Htok, %hn⟩
    imod Hcl'
    have hwrl' : lay.wr = wr := hwrl.symm
    have hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr := fun hx => by
      rcases hP0 with h | h | h
      · rw [hwrl']; exact h
      · exact absurd (SegExact.of_os hsz h) hx
      · rw [hwrl']; exact h
    obtain ⟨hW', hDK'⟩ := rzStart_pure walCodec_ok hW hd hl hs ⟨ents, habs⟩ hcut0 (hZ.zeros hok) hB hn.1 hn.2 hlo
    rw [hwrl'] at hW' hDK'
    have hFi : ∀ i, i ≠ g0.ino →
        (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩ : SegFl)]> F) !! i = F !! i :=
      fun i hi => GMap.lookup_insert_ne _ _ (Ne.symm hi)
    have hFg : (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩ : SegFl)]> F) !! g0.ino =
        some ⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩ := GMap.lookup_insert _ _ _
    have etg : tailG d (tailLay lay pre (rzSeg g0 true wr n) wr) (rzSeg g0 true wr n).ino
        ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩ : SegFl)]> F) !! (rzSeg g0 true wr n).ino) =
        ((H, md, cuts, wr, g0.ino, some ⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩) : TailG) := by
      rw [show (rzSeg g0 true wr n).ino = g0.ino from rfl, hFg]; simp [tailG, tailLay, hH, hmd, hcuts]
    imod tailVar_upd γ _ _ (tailG d (tailLay lay pre (rzSeg g0 true wr n) wr) (rzSeg g0 true wr n).ino
      ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩ : SegFl)]> F) !! (rzSeg g0 true wr n).ino))
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    ihave Hb := Hclose $$ %(rzSeg g0 true wr n) %wr
      %(<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, wr)⟩ : SegFl)]> F) [] [Htok Hbt] Hv'
    · ipureintro; exact ⟨rfl, rfl, hFi, Or.inl hwrl'.symm, hW', hDK'⟩
    · unfold segResF
      rw [show (rzSeg g0 true wr n).ino = g0.ino from rfl, hFg]
      dsimp only
      iframe
      ipureintro
      exact rzSeg_ok hsz.symm hcut0 (by omega)
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    rw [etg]
    iapply walTail_truncFin Mr R jr r dir γ ok H md cuts wr g0.ino t n g0.om g0.bs $$ Hinv [Hk Hv]
    unfold truncFinP
    iframe
    ipureintro; exact ⟨by omega, hwr⟩

end au

end WalFs
end EtcdGrove
end Perennial

end
