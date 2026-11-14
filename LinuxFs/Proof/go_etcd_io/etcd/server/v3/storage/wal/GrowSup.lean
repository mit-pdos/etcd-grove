/- Lean-first (no Rocq counterpart).

# The supplies of the tail's growth back to its size (I3b, `wal-tc19`)

`ZeroToEnd`'s growth of the WAL's lent tail (`ReadAll`'s, after its truncate to the write position `wr`)
back to the size `tg` it had: `fallocSup` (`fallocate`) and `os.truncSup` (the fallback's truncate past
the size), built from `walInv`, the caller's tie its lent token of kind `false` and half of the tail
record, idle (`walTailKeyL dir γ (some (k, false)) ∗ tailVar γ (H, md, cuts, wr, i, none)`), as
`walTail_truncSup` (`TruncSup.lean`). The supplies are told `lo ≤ wr` of the state (the truncate's landing
left `lo := min lo wr`, which the growth's attempts only lower; `ZeroToEnd.specAu`'s `Q`), and the
truncate's also that the state is at most `tg` long. The target is at most the lent `|old|` (`htg : tg ≤
k`; `ZeroToEnd`'s: the size the registration found, `|old|`).

* *the start's update* opens `walInv` (`walInvBody_tailW`, which reads `|old| = k` off the lent token),
  agrees the `OsMeta` with the caller's (`g0.om = m0`), lends it whole (and, the truncate, the empty
  bytes cut off), and commits with the token: the layout's tail becomes `rzSeg g0 tr tg n`
  (`rzGrow_pure`: `size ≤ tg ≤ hi` from `|old| ≤ hi`, `WalAbsD.oldHi_any`, `min lo tg ≤ wr`);
* *the finish's update* lends the token back and commits with the outcome: landed with the size `w`
  (`size ≤ w ≤ tg`), the tail `rzLandG` (`rzLandG_pure`: `w ≤ |old| = k`, the bytes grown over of the
  candidates the `OsMeta` knew, `rsDoneK`'s), the caller's halves `fallocDoneH` / `os.ftDoneH`; not
  landed, the in-flight layout kept, idle, the caller's halves of the announced `OsMeta`.

An abort leaves the invariant as it was (`walInvBody_tailW_same`). No F-Z needed: a growth's crash steps
are `crashOkA_rzGrow`/`crashOkA_rzLandG`, from any tail.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailLend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzGrow
public import LinuxFs.Proof.syscall.FallocateAu

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The tail announced by a resize in flight is `rzSeg` of the tail as the change found it. -/
theorem rzSeg_of_okRG {g1 : SegG} {t n : Nat} {tr : Bool} {tg : Nat} {m0 : OsMeta} {bs0 : List ByteG}
    (hok : SegFl.OkR ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩ tr tg g1) :
    g1 = rzSeg ({ g1 with om := m0, bs := bs0 } : SegG) tr tg n := by
  obtain ⟨-, -, hom, hbs, -⟩ := hok
  cases g1
  simp only [rzSeg] at hom hbs ⊢
  rw [hom, hbs]

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **The tie of the growth supplies**: the lent token of kind `false` and the caller's half of the
tail record, idle. -/
def growTie (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) : IProp GF :=
  iprop(walTailKeyL (W := W) dir γ (some (k, false)) ∗
    tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG))

/-- **The caller's part of a growth's finish**: the tie, the growth in flight on the record (the
start's `t`, `n`, the `OsMeta` and bytes it found), and the start's facts. -/
def growFinP (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (tr : Bool) (tg t n : Nat) (m0 : OsMeta)
    (bs0 : List ByteG) : IProp GF :=
  iprop(walTailKeyL (W := W) dir γ (some (k, false)) ∗
    tailVar (W := W) γ ((H, md, cuts, wr, i, some ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩) : TailG) ∗
    ⌜min m0.lo tg ≤ wr ∧ m0.size ≤ tg ∧ tg ≤ k ∧ (∀ z, m0.zf = some z → m0.size ≤ z) ∧
      bs0.length = m0.size⌝)

/-- The invariant's part of the tail with a growth in flight (the bytes cut off none). -/
theorem segResF_grow (F : GMap Ino SegFl) (g1 : SegG) (t n : Nat) (tr : Bool) (tg : Nat)
    (m0 : OsMeta) (bs0 : List ByteG) (hF : F !! g1.ino = some ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩)
    (hlen : bs0.length = m0.size) (hgrow : m0.size ≤ tg) :
    segResF (GF := GF) F g1 = iprop(rsTok tr t g1.ino tg m0 [] n ∗
      osBytes g1.ino 0 (DFrac.own (1 : Qp).half) bs0 ∗
      ⌜SegFl.OkR ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩ tr tg g1⌝) := by
  have hmin : min m0.size tg = m0.size := Nat.min_eq_left hgrow
  have hdrop : bs0.drop (min m0.size tg) = [] := by
    rw [hmin]; exact List.drop_eq_nil_of_le (by omega)
  have htake : bs0.take (min m0.size tg) = bs0 := by
    rw [hmin]; exact List.take_of_length_le (by omega)
  unfold segResF; rw [hF]; dsimp only; rw [hdrop, htake]

/-- **A growth's landing in the invariant** (both kinds): the in-flight tail `rzSeg g0' tr tg n` (the
change found `m0`, `bs0`) replaced by `rzLandG` with the size `w`, the record idle; the caller's halves
of the landed `OsMeta` and of the bytes grown over. -/
theorem walTail_growLand (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (Ls : GMap GoString WalLay) (cl : List Claim) (nn : Nat) (F : GMap Ino SegFl) (d : WalDur)
    (lay : WalLay) (pre : List SegG) (g1 : SegG) (tr : Bool) (tg w t n : Nat) (m0 : OsMeta)
    (bs0 : List ByteG) (zs : List Cands)
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay) (hs : lay.segs = pre ++ [g1])
    (hW : WalsOk walCodec Mr R jr s Ls cl nn) (hH : H = d.H) (hmd : md = d.metadata)
    (hcuts : cuts = lay.cuts) (hwrl : wr = lay.wr)
    (hok : SegFl.OkR ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩ tr tg g1)
    (hlo : min m0.lo tg ≤ wr) (hlen : bs0.length = m0.size) (hgrow : m0.size ≤ w) (hw : w ≤ tg)
    (hzf : ∀ z, m0.zf = some z → m0.size ≤ z) (hold : w ≤ lay.old.length)
    (hzl : zs.length = w - m0.size)
    (hzc : ∀ j c, m0.pc (m0.size + j) = some c → j < zs.length → zs[j]? = some c) :
    ⊢ (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g1.ino ∧ g.name = g1.name ∧ (∀ i, i ≠ g1.ino → F' !! i = F !! i) ∧
            (wr' = lay.wr ∨ TailZeros lay) ∧
            WalsOk walCodec Mr R jr s (<[dir := tailLay lay pre g wr']> Ls) cl nn ∧
            (∀ K c, DirKeysOk walCodec Mr jr s Ls cl nn K c →
              DirKeysOk walCodec Mr jr s (<[dir := tailLay lay pre g wr']> Ls) cl nn K c) ∧
            TailRK (some (k, false)) (tailLay lay pre g wr')⌝ -∗
          segResF F' g -∗
          tailVar (W := W) γ (tailG d (tailLay lay pre g wr') g.ino (F' !! g.ino)) -∗
          walInvBody (W := W) walCodec Mr R jr r s) -∗
      tailVar (W := W) γ (tailG d lay g1.ino (F !! g1.ino)) -∗
      tailVar (W := W) γ ((H, md, cuts, wr, g1.ino, some ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩) : TailG) -∗
      osBytes g1.ino 0 (DFrac.own (1 : Qp).half) bs0 -∗
      osMeta g1.ino (DFrac.own 1) (rsPostK true tr m0 tg w n []) -∗
      osBytes g1.ino m0.size (DFrac.own 1) (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) ==∗
      walInvBody (W := W) walCodec Mr R jr r s ∗
        tailVar (W := W) γ ((H, md, cuts, wr, g1.ino, none) : TailG) ∗
        osMeta g1.ino (DFrac.own (1 : Qp).half) (rsPostK true tr m0 tg w n []) ∗
        osBytes g1.ino m0.size (DFrac.own (1 : Qp).half) (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) := by
  iintro Hclose Hv' Hv Hbt Hm Hbz
  have hmcut : m0.cut = none := hok.2.1
  have hg1 := rzSeg_of_okRG hok
  obtain ⟨g0', hg0'⟩ : ∃ g0' : SegG, g0' = { g1 with om := m0, bs := bs0 } := ⟨_, rfl⟩
  rw [← hg0'] at hg1
  have hg0om : g0'.om = m0 := by rw [hg0']
  have hg0bs : g0'.bs = bs0 := by rw [hg0']
  have hFd : ∀ i, i ≠ g1.ino → (GMap.delete g1.ino F) !! i = F !! i :=
    fun i hi => GMap.lookup_delete_ne _ (Ne.symm hi)
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hbz with ⟨Hz1, Hz2⟩
  have hs' : lay.segs = pre ++ [rzSeg g0' tr tg n] := by rw [hs, ← hg1]
  obtain ⟨hW', hDK'⟩ := rzLandG_pure (k := n) (zs := zs) (w := w) hW hd hl hs'
    (by rw [hg0om, hg0bs]; exact hlen) (by rw [hg0om]; exact hgrow) hw (by rw [hg0om]; exact hzl)
    (by rw [hg0om]; exact hmcut) (by rw [hg0om]; exact hzf)
    (fun j c h1 h2 => by rw [hg0om] at h2; exact hzc j c h2 h1) (by rw [hg0om, ← hwrl]; exact hlo) hold
  have e1 : rzLandG g0' tr tg w n zs = ({ g1 with
      om := rsPostK true tr m0 tg w n []
      bs := bs0 ++ growBytes n zs } : SegG) := by
    subst hg0'; rfl
  have etg : tailG d (tailLay lay pre (rzLandG g0' tr tg w n zs) lay.wr) (rzLandG g0' tr tg w n zs).ino
      ((GMap.delete g1.ino F) !! (rzLandG g0' tr tg w n zs).ino) = ((H, md, cuts, wr, g1.ino, none) : TailG) := by
    rw [e1]; simp [tailG, tailLay, GMap.lookup_delete_eq, hH, hmd, hcuts, hwrl]
  imod tailVar_upd γ _ _ (tailG d (tailLay lay pre (rzLandG g0' tr tg w n zs) lay.wr)
    (rzLandG g0' tr tg w n zs).ino ((GMap.delete g1.ino F) !! (rzLandG g0' tr tg w n zs).ino))
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  ihave Hb := Hclose $$ %(rzLandG g0' tr tg w n zs) %lay.wr %(GMap.delete g1.ino F) [] [Hm2 Hbt Hz2] Hv'
  · ipureintro; exact ⟨by rw [e1], by rw [e1], hFd, Or.inl rfl, hW', hDK', trivial⟩
  · have hn : (GMap.delete g1.ino F) !! (rzLandG g0' tr tg w n zs).ino = none := by
      rw [e1]; exact GMap.lookup_delete_eq _ _
    unfold segResF; rw [hn]; dsimp only
    unfold segRes
    rw [e1]
    iframe Hm2
    iapply osBytes_app0
    rw [hlen]
    iframe
  imodintro
  rw [etg]
  iframe

/-- **A growth that did not land, in the invariant** (both kinds): the in-flight layout kept, idle; the
caller's half of the announced `OsMeta`. -/
theorem walTail_growUndone (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (Ls : GMap GoString WalLay) (cl : List Claim) (nn : Nat) (F : GMap Ino SegFl) (d : WalDur)
    (lay : WalLay) (pre : List SegG) (g1 : SegG) (tr : Bool) (tg t n : Nat) (m0 : OsMeta)
    (bs0 : List ByteG)
    (hl : Ls !! dir = some lay) (hs : lay.segs = pre ++ [g1])
    (hW : WalsOk walCodec Mr R jr s Ls cl nn) (hH : H = d.H) (hmd : md = d.metadata)
    (hcuts : cuts = lay.cuts) (hwrl : wr = lay.wr)
    (hok : SegFl.OkR ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩ tr tg g1)
    (hlen : bs0.length = m0.size) (hgrow : m0.size ≤ tg) :
    ⊢ (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g1.ino ∧ g.name = g1.name ∧ (∀ i, i ≠ g1.ino → F' !! i = F !! i) ∧
            (wr' = lay.wr ∨ TailZeros lay) ∧
            WalsOk walCodec Mr R jr s (<[dir := tailLay lay pre g wr']> Ls) cl nn ∧
            (∀ K c, DirKeysOk walCodec Mr jr s Ls cl nn K c →
              DirKeysOk walCodec Mr jr s (<[dir := tailLay lay pre g wr']> Ls) cl nn K c) ∧
            TailRK (some (k, false)) (tailLay lay pre g wr')⌝ -∗
          segResF F' g -∗
          tailVar (W := W) γ (tailG d (tailLay lay pre g wr') g.ino (F' !! g.ino)) -∗
          walInvBody (W := W) walCodec Mr R jr r s) -∗
      tailVar (W := W) γ (tailG d lay g1.ino (F !! g1.ino)) -∗
      tailVar (W := W) γ ((H, md, cuts, wr, g1.ino, some ⟨t, 0, [], n, m0, bs0, some (tr, tg)⟩) : TailG) -∗
      osBytes g1.ino 0 (DFrac.own (1 : Qp).half) bs0 -∗
      osMeta g1.ino (DFrac.own 1) (rsUnMeta true tr m0 tg n) ==∗
      walInvBody (W := W) walCodec Mr R jr r s ∗
        tailVar (W := W) γ ((H, md, cuts, wr, g1.ino, none) : TailG) ∗
        osMeta g1.ino (DFrac.own (1 : Qp).half) (rsUnMeta true tr m0 tg n) := by
  iintro Hclose Hv' Hv Hbt Hm
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  obtain ⟨hW', hDK'⟩ := walsOk_self (g := g1) hW hl hs
  have hFd : ∀ i, i ≠ g1.ino → (GMap.delete g1.ino F) !! i = F !! i :=
    fun i hi => GMap.lookup_delete_ne _ (Ne.symm hi)
  have etg : tailG d (tailLay lay pre g1 lay.wr) g1.ino ((GMap.delete g1.ino F) !! g1.ino) =
      ((H, md, cuts, wr, g1.ino, none) : TailG) := by
    simp [tailG, tailLay, GMap.lookup_delete_eq, hH, hmd, hcuts, hwrl]
  imod tailVar_upd γ _ _ (tailG d (tailLay lay pre g1 lay.wr) g1.ino
    ((GMap.delete g1.ino F) !! g1.ino)) $$ Hv Hv' with ⟨Hv, Hv'⟩
  have hmin : min m0.size tg = m0.size := Nat.min_eq_left hgrow
  have hdrop : bs0.drop (min m0.size tg) = [] := by
    rw [hmin]; exact List.drop_eq_nil_of_le (by omega)
  have htake : bs0.take (min m0.size tg) = bs0 := by
    rw [hmin]; exact List.take_of_length_le (by omega)
  ihave Hb := Hclose $$ %g1 %lay.wr %(GMap.delete g1.ino F) [] [Hm2 Hbt] Hv'
  · ipureintro; exact ⟨rfl, rfl, hFd, Or.inl rfl, hW', hDK', trivial⟩
  · unfold segResF; rw [GMap.lookup_delete_eq]; dsimp only
    unfold segRes
    obtain ⟨-, -, hom, hbs, -⟩ := hok
    have hom' : g1.om = rsUnMeta true tr m0 tg n := hom
    have hbs' : g1.bs = bs0 := by
      rw [hbs]; simp only [] ; rw [hdrop, htake]; simp [rsAnn]
    rw [hom', hbs']
    iframe
  imodintro
  rw [etg]
  iframe

/-! ## `fallocate`'s growth -/

/-- **The finish's update of `fallocate`'s growth** (see the file header). -/
theorem walTail_fallocFin (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (i : Ino) (tg t n : Nat) (m0 : OsMeta) (bs0 : List ByteG) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      growFinP (W := W) dir γ k H md cuts wr i false tg t n m0 bs0 -∗
      osAUnc (A := w64) (rsTok false t i tg m0 [] n) (rsOutF i tg m0 n)
        (fun e => iprop(fallocOutH i tg m0 e ∗ (walTailKeyL (W := W) dir γ (some (k, false)) ∗
          tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG)))) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (growFinP (W := W) dir γ k H md cuts wr i false tg t n m0 bs0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold growFinP
  icases HP with ⟨Hk, Hv, %hf⟩
  obtain ⟨hlo, hgrow, htg, hzf, hlen⟩ := hf
  icases walInvBody_tailW walCodec Mr R jr r s dir γ (some (k, false)) _ m0 $$ Hb Hk Hv [] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g1, %hp, Hseg, Hk, Hv, Hv', -, Hclose⟩
  · dsimp only [tailHeld]; iempintro
  obtain ⟨hd, hl, hs, htg0, hW, -, -, -, -, hold⟩ := hp
  have hold' : lay.old.length = k := hold k false rfl
  have htgv := htg0
  simp only [tailG, Prod.mk.injEq] at htgv
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htgv
  ihave Hv' : tailVar (W := W) γ (tailG d lay g1.ino (F !! g1.ino)) $$ [Hv']
  · rw [← htg0]; iexact Hv'
  subst hino
  rw [segResF_grow F g1 t n false tg m0 bs0 hF.symm hlen hgrow]
  icases Hseg with ⟨Htok, Hbt, %hok⟩
  have hmcut : m0.cut = none := hok.2.1
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
    · rw [segResF_grow F g1 t n false tg m0 bs0 hF.symm hlen hgrow]; iframe; ipureintro; exact hok
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g1 hW hl hs (some (k, false)) trivial
      $$ Hclose Hseg Hv'
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    dsimp only
    iframe Hk Hv
    ipureintro; exact ⟨hlo, hgrow, htg, hzf, hlen⟩
  · iintro %e Hout
    imod Hcl'
    unfold rsOutF
    rw [show m0.cut.isNone = true by simp [hmcut]]
    ihave Hout : (∃ w, ⌜m0.size ≤ w ∧ w ≤ tg ∧ (e = 0 → w = tg)⌝ ∗
        rsDoneK true false g1.ino tg w m0 [] n) ∨
        (⌜e ≠ 0⌝ ∗ rsUndoneK true false g1.ino tg m0 [] n) $$ [Hout]
    · icases Hout with (⟨%he, Hd⟩ | ⟨%he, (Hu | ⟨%w, %hw, Hd⟩)⟩)
      · ileft; iexists tg; iframe Hd; ipureintro; exact ⟨hgrow, Nat.le_refl _, fun _ => rfl⟩
      · iright; iframe Hu; ipureintro; exact he
      · ileft; iexists w; iframe Hd; ipureintro; exact ⟨hw.1, hw.2, fun h => absurd h he⟩
    icases Hout with (⟨%w, %hw, Hd⟩ | ⟨%he, Hu⟩)
    · unfold rsDoneK
      icases Hd with ⟨%zs, %hzs, Hm, Hbz, -⟩
      obtain ⟨hzl, -, hzc⟩ := hzs
      imod walTail_growLand Mr R jr r s dir γ k H md cuts wr Ls cl nn F d lay pre g1 false tg w t n m0
        bs0 zs hd hl hs hW hH hmd hcuts hwrl hok (by omega) hlen hw.1 hw.2.1 hzf (by omega) hzl hzc
        $$ Hclose Hv' Hv Hbt Hm Hbz with ⟨Hb, Hv, Hm1, Hz1⟩
      imod Hcl $$ [Hb]
      · iexists s; iexact Hb
      imodintro
      dsimp only
      iframe Hk Hv
      ihave Hdone : fallocDoneH g1.ino m0 tg w $$ [Hm1 Hz1]
      · unfold fallocDoneH
        iexists (rsPostK true false m0 tg w n []).tc
        iexists (rsPostK true false m0 tg w n []).rz
        isplitr
        · ipureintro; exact TcKnowsF.rsTail m0 tg w n []
        rw [← rsPostK_withTc]
        iframe Hm1
        iapply (osZerosA_unfold _ _ _ _).2
        iexists zs.map (fun c0 => c0 ++ [((0 : w8), n)])
        isplitr
        · ipureintro; simp only [List.length_map]; exact hzl
        rw [show (zs.map (fun c0 => c0 ++ [((0 : w8), n)])).map (fun c => ((0 : w8), c)) =
          zs.map (fun c0 => ((0 : w8), c0 ++ [((0 : w8), n)])) by simp]
        iexact Hz1
      unfold fallocOutH
      by_cases he0 : e = 0
      · ileft; isplitr
        · ipureintro; exact he0
        have hwt : w = tg := hw.2.2 he0
        subst hwt
        iexact Hdone
      · iright; isplitr
        · ipureintro; exact he0
        iright; iexists w; iframe Hdone; ipureintro; exact ⟨hw.1, hw.2.1⟩
    · unfold rsUndoneK
      icases Hu with ⟨Hm, -, -⟩
      imod walTail_growUndone Mr R jr r s dir γ k H md cuts wr Ls cl nn F d lay pre g1 false tg t n m0
        bs0 hl hs hW hH hmd hcuts hwrl hok hlen hgrow $$ Hclose Hv' Hv Hbt Hm with ⟨Hb, Hv, Hm1⟩
      imod Hcl $$ [Hb]
      · iexists s; iexact Hb
      imodintro
      dsimp only
      iframe Hk Hv
      unfold fallocOutH
      iright; isplitr
      · ipureintro; exact he
      ileft
      iexists (rsTail false m0 tg m0.size n [])
      iexists (n :: m0.rz)
      isplitr
      · ipureintro; exact TcKnowsF.rsTail m0 tg m0.size n []
      have eU : rsUnMeta true false m0 tg n = (m0.announce (min m0.size tg) (rsHi false m0.size tg) tg).withTc
          (rsTail false m0 tg m0.size n []) (n :: m0.rz) := rfl
      rw [← eU]; iexact Hm1

/-- **The caller's part of a growth's start**: its tie and its half of the tail's `OsMeta`. -/
def growStartP (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (m0 : OsMeta) : IProp GF :=
  iprop(growTie (W := W) dir γ k H md cuts wr i ∗ osMeta i (DFrac.own (1 : Qp).half) m0)

/-- **The supply of `fallocate`'s growth of the lent tail to `tg ≤ k`** (see the file header), told
`lo ≤ wr` of the state (and, as `walTail_truncSupG`'s, that it is at most `tg` long). -/
theorem walTail_fallocSup (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (i : Ino) (tg : Nat) (htg : tg ≤ k) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      fallocSup (growTie (W := W) dir γ k H md cuts wr i) i tg (fun m => m.lo ≤ wr ∧ m.size ≤ tg) := by
  iintro #Hinv
  unfold fallocSup
  iintro !> %m0 %hsz0 %hP0' HK Hm
  obtain ⟨hP0, -⟩ := hP0'
  unfold fallocAuW
  ihave HP : growStartP (W := W) dir γ k H md cuts wr i m0 $$ [HK Hm]
  · unfold growStartP; iframe
  iapply osAUnc_coiter _ _ _ (growStartP (W := W) dir γ k H md cuts wr i m0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold growStartP growTie
  icases HP with ⟨⟨Hk, Hv⟩, Hm⟩
  icases walInvBody_tailW walCodec Mr R jr r s dir γ (some (k, false)) _ m0 $$ Hb Hk Hv [Hm] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hm, Hclose⟩
  · dsimp only [tailHeld]; iexact Hm
  dsimp only [tailHeld]
  obtain ⟨hd, hl, hs, htg0, hW, ⟨ents, habs⟩, hcut0, -, -, hold⟩ := hp
  have hold' : lay.old.length = k := hold k false rfl
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
  obtain ⟨hsz, -, -, -, -⟩ := habs.metas g0 hg0m
  obtain ⟨hso, -, -, hwb, -⟩ := habs.lastWin g0 hg0l
  have hso0 := walAbsD_so_pos habs
  have hhi := habs.oldHi_any g0 hg0l
  have hwr : wr ≤ g0.om.size := by omega
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  isplitl [Hm Hm2]
  · iapply (osMeta_halves _ _).2; iframe
  iframe Hnc
  isplit
  · -- abort
    iintro HmA
    imod Hcl'
    icases (osMeta_halves _ _).1 $$ HmA with ⟨Hm1, Hm2⟩
    ihave Hseg : segResF F g0 $$ [Hm2 Hb2]
    · rw [eseg]; iframe
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g0 hW hl hs (some (k, false)) trivial
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
    obtain ⟨hW', hDK'⟩ := rzGrow_pure (tr := false) (k := n) (tg := tg) hW hd hl hs ⟨ents, habs⟩ hsz0
      (by omega) (by omega) (by omega) hn.1 hn.2
    have hFi : ∀ i, i ≠ g0.ino →
        (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩ : SegFl)]> F) !! i = F !! i :=
      fun i hi => GMap.lookup_insert_ne _ _ (Ne.symm hi)
    have hFg : (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩ : SegFl)]> F) !! g0.ino =
        some ⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩ := GMap.lookup_insert _ _ _
    have etg : tailG d (tailLay lay pre (rzSeg g0 false tg n) lay.wr) (rzSeg g0 false tg n).ino
        ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩ : SegFl)]> F) !! (rzSeg g0 false tg n).ino) =
        ((H, md, cuts, wr, g0.ino, some ⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩) : TailG) := by
      rw [show (rzSeg g0 false tg n).ino = g0.ino from rfl, hFg]; simp [tailG, tailLay, hH, hmd, hcuts, hwrl]
    imod tailVar_upd γ _ _ (tailG d (tailLay lay pre (rzSeg g0 false tg n) lay.wr) (rzSeg g0 false tg n).ino
      ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩ : SegFl)]> F) !! (rzSeg g0 false tg n).ino))
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    ihave Hb := Hclose $$ %(rzSeg g0 false tg n) %lay.wr
      %(<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (false, tg)⟩ : SegFl)]> F) [] [Htok Hb2] Hv'
    · ipureintro; exact ⟨rfl, rfl, hFi, Or.inl rfl, hW', hDK', trivial⟩
    · rw [segResF_grow _ (rzSeg g0 false tg n) t n false tg g0.om g0.bs hFg hsz.symm hsz0,
        show (rzSeg g0 false tg n).ino = g0.ino from rfl]
      iframe
      ipureintro
      exact rzSeg_ok hsz.symm hcut0 (by omega)
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    rw [etg]
    iapply walTail_fallocFin Mr R jr r dir γ k H md cuts wr g0.ino tg t n g0.om g0.bs $$ Hinv [Hk Hv]
    unfold growFinP
    iframe
    ipureintro; exact ⟨by omega, hsz0, htg, hn.2.1, hsz.symm⟩


/-! ## The fallback's truncate past the size -/

/-- **The finish's update of the fallback's truncate past the size** (see the file header). -/
theorem walTail_truncGFin (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (i : Ino) (tg t n : Nat) (m0 : OsMeta) (bs0 : List ByteG) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      growFinP (W := W) dir γ k H md cuts wr i true tg t n m0 bs0 -∗
      osAUnc (A := w64) (rsTok true t i tg m0 [] n) (rsOutT i tg m0 [] n)
        (fun e => iprop(os.truncOutH i tg m0 [] n e ∗ (walTailKeyL (W := W) dir γ (some (k, false)) ∗
          tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG)))) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (growFinP (W := W) dir γ k H md cuts wr i true tg t n m0 bs0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold growFinP
  icases HP with ⟨Hk, Hv, %hf⟩
  obtain ⟨hlo, hgrow, htg, hzf, hlen⟩ := hf
  icases walInvBody_tailW walCodec Mr R jr r s dir γ (some (k, false)) _ m0 $$ Hb Hk Hv [] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g1, %hp, Hseg, Hk, Hv, Hv', -, Hclose⟩
  · dsimp only [tailHeld]; iempintro
  obtain ⟨hd, hl, hs, htg0, hW, -, -, -, -, hold⟩ := hp
  have hold' : lay.old.length = k := hold k false rfl
  have htgv := htg0
  simp only [tailG, Prod.mk.injEq] at htgv
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htgv
  ihave Hv' : tailVar (W := W) γ (tailG d lay g1.ino (F !! g1.ino)) $$ [Hv']
  · rw [← htg0]; iexact Hv'
  subst hino
  rw [segResF_grow F g1 t n true tg m0 bs0 hF.symm hlen hgrow]
  icases Hseg with ⟨Htok, Hbt, %hok⟩
  have hmcut : m0.cut = none := hok.2.1
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
    · rw [segResF_grow F g1 t n true tg m0 bs0 hF.symm hlen hgrow]; iframe; ipureintro; exact hok
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g1 hW hl hs (some (k, false)) trivial
      $$ Hclose Hseg Hv'
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    dsimp only
    iframe Hk Hv
    ipureintro; exact ⟨hlo, hgrow, htg, hzf, hlen⟩
  · iintro %e Hout
    imod Hcl'
    unfold rsOutT
    rw [show m0.cut.isNone = true by simp [hmcut]]
    ihave Hout : (rsDoneK true true g1.ino tg tg m0 [] n) ∨
        (⌜e ≠ 0⌝ ∗ rsUndoneK true true g1.ino tg m0 [] n) $$ [Hout]
    · icases Hout with (⟨%he, Hd⟩ | ⟨%he, (Hd | Hu)⟩)
      · ileft; iexact Hd
      · ileft; iexact Hd
      · iright; iframe Hu; ipureintro; exact he
    icases Hout with (Hd | ⟨%he, Hu⟩)
    · unfold rsDoneK
      icases Hd with ⟨%zs, %hzs, Hm, Hbz, -⟩
      obtain ⟨hzl, -, hzc⟩ := hzs
      imod walTail_growLand Mr R jr r s dir γ k H md cuts wr Ls cl nn F d lay pre g1 true tg tg t n m0
        bs0 zs hd hl hs hW hH hmd hcuts hwrl hok (by omega) hlen hgrow (Nat.le_refl _) hzf (by omega) hzl hzc
        $$ Hclose Hv' Hv Hbt Hm Hbz with ⟨Hb, Hv, Hm1, Hz1⟩
      imod Hcl $$ [Hb]
      · iexists s; iexact Hb
      imodintro
      dsimp only
      iframe Hk Hv
      ihave Hdone : ∃ zs', os.ftDoneH g1.ino m0 tg zs' $$ [Hm1 Hz1]
      · iexists zs.map (fun c0 => c0 ++ [((0 : w8), n)])
        unfold os.ftDoneH
        isplitr
        · ipureintro; simp only [List.length_map]; exact hzl
        isplitl [Hm1]
        · iexists (rsPostK true true m0 tg tg n []).tc
          iexists (rsPostK true true m0 tg tg n []).rz
          isplitr
          · ipureintro; exact ⟨TcKnows.rsTail m0 tg tg n _, TcFrom.rsTail m0 tg tg n _⟩
          rw [← rsPostK_withTc]; iexact Hm1
        rw [show (zs.map (fun c0 => c0 ++ [((0 : w8), n)])).map (fun c => ((0 : w8), c)) =
          zs.map (fun c0 => ((0 : w8), c0 ++ [((0 : w8), n)])) by simp]
        iexact Hz1
      unfold os.truncOutH
      by_cases he0 : e = 0
      · ileft; isplitr
        · ipureintro; exact he0
        iexact Hdone
      · iright; isplitr
        · ipureintro; exact he0
        ileft; iexact Hdone
    · unfold rsUndoneK
      icases Hu with ⟨Hm, -, -⟩
      imod walTail_growUndone Mr R jr r s dir γ k H md cuts wr Ls cl nn F d lay pre g1 true tg t n m0
        bs0 hl hs hW hH hmd hcuts hwrl hok hlen hgrow $$ Hclose Hv' Hv Hbt Hm with ⟨Hb, Hv, Hm1⟩
      imod Hcl $$ [Hb]
      · iexists s; iexact Hb
      imodintro
      dsimp only
      iframe Hk Hv
      unfold os.truncOutH
      iright; isplitr
      · ipureintro; exact he
      iright
      unfold os.ftUndoneH
      isplitl [Hm1]
      · iexists (rsTail true m0 tg m0.size n [])
        iexists (n :: m0.rz)
        isplitr
        · ipureintro; exact ⟨TcKnows.rsTail m0 tg m0.size n [], TcFrom.rsTail m0 tg m0.size n []⟩
        have eU : rsUnMeta true true m0 tg n = (m0.announce (min m0.size tg) (rsHi true m0.size tg) tg).withTc
            (rsTail true m0 tg m0.size n []) (n :: m0.rz) := rfl
        rw [← eU]; iexact Hm1
      rw [show rsAnn n ([] : List ByteG) = [] from rfl]
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro


/-- **The supply of the fallback's truncate of the lent tail past its size, to `tg ≤ k`** (see the file
header), told `lo ≤ wr` of the state and that it is at most `tg` long. -/
theorem walTail_truncSupG (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (i : Ino) (tg : Nat) (htg : tg ≤ k) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      os.truncSup (growTie (W := W) dir γ k H md cuts wr i) i tg (fun m => m.lo ≤ wr ∧ m.size ≤ tg) := by
  iintro #Hinv
  unfold os.truncSup
  iintro !> %m0 %xs0 %hxs0 %hP0' HK Hm -
  obtain ⟨hP0, hsz0⟩ := hP0'
  obtain rfl : xs0 = [] := List.eq_nil_of_length_eq_zero (by omega)
  unfold os.truncAuW
  ihave HP : growStartP (W := W) dir γ k H md cuts wr i m0 $$ [HK Hm]
  · unfold growStartP; iframe
  iapply osAUnc_coiter _ _ _ (growStartP (W := W) dir γ k H md cuts wr i m0) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold growStartP growTie
  icases HP with ⟨⟨Hk, Hv⟩, Hm⟩
  icases walInvBody_tailW walCodec Mr R jr r s dir γ (some (k, false)) _ m0 $$ Hb Hk Hv [Hm] with
    ⟨%Ls, %cl, %nn, %F, %d, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hm, Hclose⟩
  · dsimp only [tailHeld]; iexact Hm
  dsimp only [tailHeld]
  obtain ⟨hd, hl, hs, htg0, hW, ⟨ents, habs⟩, hcut0, -, -, hold⟩ := hp
  have hold' : lay.old.length = k := hold k false rfl
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
  obtain ⟨hsz, -, -, -, -⟩ := habs.metas g0 hg0m
  obtain ⟨hso, -, -, hwb, -⟩ := habs.lastWin g0 hg0l
  have hso0 := walAbsD_so_pos habs
  have hhi := habs.oldHi_any g0 hg0l
  have hwr : wr ≤ g0.om.size := by omega
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  isplitl [Hm Hm2]
  · isplitl [Hm Hm2]
    · iapply (osMeta_halves _ _).2; iframe
    · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  iframe Hnc
  isplit
  · -- abort
    iintro ⟨HmA, -⟩
    imod Hcl'
    icases (osMeta_halves _ _).1 $$ HmA with ⟨Hm1, Hm2⟩
    ihave Hseg : segResF F g0 $$ [Hm2 Hb2]
    · rw [eseg]; iframe
    ihave Hb := walInvBody_tailW_same walCodec Mr R jr r s dir γ Ls cl nn F d lay pre g0 hW hl hs (some (k, false)) trivial
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
    obtain ⟨hW', hDK'⟩ := rzGrow_pure (tr := true) (k := n) (tg := tg) hW hd hl hs ⟨ents, habs⟩ hsz0
      (by omega) (by omega) (by omega) hn.1 hn.2
    have hFi : ∀ i, i ≠ g0.ino →
        (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! i = F !! i :=
      fun i hi => GMap.lookup_insert_ne _ _ (Ne.symm hi)
    have hFg : (<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! g0.ino =
        some ⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ := GMap.lookup_insert _ _ _
    have etg : tailG d (tailLay lay pre (rzSeg g0 true tg n) lay.wr) (rzSeg g0 true tg n).ino
        ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! (rzSeg g0 true tg n).ino) =
        ((H, md, cuts, wr, g0.ino, some ⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩) : TailG) := by
      rw [show (rzSeg g0 true tg n).ino = g0.ino from rfl, hFg]; simp [tailG, tailLay, hH, hmd, hcuts, hwrl]
    imod tailVar_upd γ _ _ (tailG d (tailLay lay pre (rzSeg g0 true tg n) lay.wr) (rzSeg g0 true tg n).ino
      ((<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) !! (rzSeg g0 true tg n).ino))
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    ihave Hb := Hclose $$ %(rzSeg g0 true tg n) %lay.wr
      %(<[g0.ino := (⟨t, 0, [], n, g0.om, g0.bs, some (true, tg)⟩ : SegFl)]> F) [] [Htok Hb2] Hv'
    · ipureintro; exact ⟨rfl, rfl, hFi, Or.inl rfl, hW', hDK', trivial⟩
    · rw [segResF_grow _ (rzSeg g0 true tg n) t n true tg g0.om g0.bs hFg hsz.symm hsz0,
        show (rzSeg g0 true tg n).ino = g0.ino from rfl]
      iframe
      ipureintro
      exact rzSeg_ok hsz.symm hcut0 (by omega)
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    rw [etg]
    iapply walTail_truncGFin Mr R jr r dir γ k H md cuts wr g0.ino tg t n g0.om g0.bs $$ Hinv [Hk Hv]
    unfold growFinP
    iframe
    ipureintro; exact ⟨by omega, hsz0, htg, hn.2.1, hsz.symm⟩

end au

end WalFs
end EtcdGrove
end Perennial

end
