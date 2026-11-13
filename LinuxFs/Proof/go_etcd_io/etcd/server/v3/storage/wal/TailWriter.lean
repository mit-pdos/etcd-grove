/- Lean-first (no Rocq counterpart).

# The crash-aware tail write (W6 of `notes/wal-fsext-plan.md`; "W6 implementation log")

The WAL's tail is crash-tracked: the invariant (`walInv`, `Inv.lean`) holds half of its `OsMeta` and
bytes, the handle the other half (`walTailW`, `Handle.lean`). A `pwrite` on it is two steps of the
extension (`PWriteStart`, `PWriteFinish`, `GooseLang/Ext/Fs/Write.lean`); each opens `walInv`, with
`notCrashed` (`wp_atomic_nc`, `GooseLang/Ext/Fs/NotCrashedAcc.lean`), and keeps its crash condition:

* **the start** (`wp_tailPWriteStart`): the handle's halves and the invariant's make the file's
  `OsMeta` and the written range whole; the step's token goes into the invariant with the halves of
  the bytes around it (a write in flight, `SegFl`, `segResF`), the layout's tail becoming the
  segment as the write announced it (`SegFl.Ok`: each byte of the range gets the candidate of its
  intended value, `ByteOk`'s announced case). The program keeps its halves of the bytes around the
  range and its half of the tail record, now with the write in flight;
* **the finish** (`wp_tailPWriteFinish`): the token back, the file idle again as the `k` bytes
  written leave it (`pwPost`, `finBytes`), the write position `wr + k`, halves split again.

Both rest on the pure layout lemmas `walsOk_announce`/`walsOk_finish`: the static relation and the
crash condition of the tail after the step, its bytes past `wr` the intended stream's (the record ties
the program's history to the invariant's), over zeros (F-Z, `TailZeros`). **The crash condition of
an append is the hard part** (any image mixing the old zeros and the new frames, under W1, decodes
to an image of the history: the encoding layer's prefix lemma).

The contract (`wal.tailWriter`): `walTailW` is an `io.writerStreamP` with the guard `tailOk` (a prefix
of the intended stream inside the preallocated size). Its proof: `(*os.File).Write` over a
`WriteAt` whose attempts are the two steps above (the loop of `os.File.WriteAt.wp_proof_crash`,
`LinuxFs/Proof/os/Crash.lean`, with these steps in place of `cfInv`'s; `os.File.Write.wp_spec`,
`Off.lean`, generalized over its `WriteAt` contract).

**Writes past the preallocated size are not covered** (`tailOk`'s second clause, `SegFl.Ok`'s first):
the layout's `wr ≤ old.length`, and a write in flight past the size has no ghost candidates for the
bytes it extends the file with (`cfMeta`'s zeros move to the write's end; the step's `OsMeta.pc`
past the size would be the source). The `Save` that crosses `SegmentSizeBytes` writes there.

Status: the two steps proved (over `walInvBody_tail`, `TailAcc.lean`, and the pure `walsOk_tail`,
`walAbsD_announce`/`walAbsD_finish`, `TailStepPure.lean`); the program's tail facts `TailMeta` (no
mappings, zeros past the size: `MetaOk`'s, which the invariant does not keep) come with `walTailW`.
`wal.tailWriter` is `sorry` (plan above).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.os.CrashWrite
public import LinuxFs.Proof.os.CrashOps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The program's part of the tail `i` while the write `fl` is in flight on it**: its key and half
of the tail record (with the write), and its halves of the bytes around the written range. -/
def walTailFl (dir : GoString) (γ : GName) (tg : TailG) (i : Ino) (fl : SegFl) : IProp GF :=
  iprop(walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
    osBytes i 0 (DFrac.own (1 : Qp).half) (fl.bs.take fl.off) ∗
    osBytes i (fl.off + fl.data.length) (DFrac.own (1 : Qp).half)
      (fl.bs.drop (fl.off + fl.data.length)))

theorem tailVar_update (γ : GName) (a1 a2 b : TailG) :
    ⊢ tailVar (W := W) γ a1 -∗ tailVar (W := W) γ a2 ==∗ tailVar (W := W) γ b ∗ tailVar (W := W) γ b := by
  letI := walAllG (W := W)
  unfold tailVar
  exact ghostVar_update_halves _ _ _ _

theorem osMeta_agree' (i : Ino) (dq1 dq2 : DFrac) (m1 m2 : OsMeta) :
    ⊢ (osMeta i dq1 m1 : IProp GF) -∗ osMeta i dq2 m2 -∗ ⌜m1 = m2⌝ := by
  unfold osMeta
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %Hv
  ipureintro; exact Hv.2

/-- **The first step of a `pwrite` on the tail** (see the file header): at `off`, at or below the
write position `wr` (a retry rewrites what an earlier attempt wrote: then the byte at `off` carries
that attempt's candidate, stamped positive, so `off` is past the synced bytes), of the intended
bytes from there, inside the file. -/
theorem wp_tailPWriteStart (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (Φ : val → IProp GF)
    (hwr : d.writable = true) (hoff0 : 0 ≤ off.toInt) (hoffw : off.toNat ≤ wr)
    (hre : off.toNat = wr ∨ ∃ q ∈ (bs.getD off.toNat (0, [])).2, 0 < q.2) (hd : data ≠ [])
    (hin : off.toNat + data.length ≤ m.size)
    (hS : data <+: (tailStream Mr H md cuts).drop off.toNat) (hm : TailMeta m bs) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ t : Nat, ∀ n : Nat, ⌜0 < n ∧ 0 < off.toNat⌝ -∗ osFd fd dq d -∗
        walTailFl dir γ (H, md, cuts, wr, d.ino, some ⟨t, off.toNat, data, n, m, bs, none⟩) d.ino
          ⟨t, off.toNat, data, n, m, bs, none⟩ -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  iintro #Harea Hfd Hk Hv Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  obtain ⟨x, xs, hxs⟩ : ∃ x xs, bs = x :: xs := by
    cases h : bs with
    | nil => have := hm.1; rw [h] at this; simp at this; have := List.length_pos_iff.2 hd; omega
    | cons x xs => exact ⟨x, xs, rfl⟩
  ihave Hb1 := (show osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs ⊢
    osBytes (((H, md, cuts, wr, d.ino, none) : TailG).2.2.2.2.1) 0 (DFrac.own (1 : Qp).half)
      (x :: xs) by rw [hxs]) $$ Hb1
  icases walInvBody_tail walCodec walCodec_ok Mr R jr r s dir γ _ x xs $$ Hb Hk Hv Hb1 with
    ⟨%F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hb1, Hclose⟩
  ihave Hb1 := (show osBytes (((H, md, cuts, wr, d.ino, none) : TailG).2.2.2.2.1) 0
    (DFrac.own (1 : Qp).half) (x :: xs) ⊢ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs
      by rw [hxs]) $$ Hb1
  obtain ⟨hdw, hs, htg, ⟨ents, habs⟩, hcut0⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, -, -, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  unfold segResF segRes
  rw [← hF]
  dsimp only
  icases Hseg with ⟨Hm2, Hb2⟩
  rw [← hino]
  icases osMeta_agree' _ _ _ _ _ $$ Hm1 Hm2 with %hmm
  subst hmm
  icases osBytes_agree d.ino _ _ 0 bs g0.bs (by rw [hm.1, hsz]) $$ Hb1 Hb2 with %hbb
  subst hbb
  have hlen : g0.bs.length = g0.om.size := hm.1
  -- the write is past the synced bytes
  have hso : lay.so ≤ off.toNat := by
    obtain ⟨hso', -, -, -, hB, -⟩ := habs.last g0 hg0
    rcases hre with he | ⟨q, hq, hq0⟩
    · omega
    · refine Nat.le_of_not_lt fun hlt => ?_
      have hbl : off.toNat < g0.bs.length := by
        have := List.length_pos_iff.2 hd; omega
      have hy : g0.bs[off.toNat]? = some (g0.bs.getD off.toNat (0, [])) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]; rfl
      have hold := hB off.toNat _ hy
      rw [decide_eq_true hlt] at hold
      have := hold.synced_stamps q hq
      omega
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (osBytes_split3 d.ino g0.om g0.bs off.toNat data.length _ hlen).1 $$ Hb1 with ⟨Hp1, Hr1, Hs1⟩
  icases (osBytes_split3 d.ino g0.om g0.bs off.toNat data.length _ hlen).1 $$ Hb2 with ⟨Hp2, Hr2, Hs2⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  have hin' : off.toNat + data.length ≤ g0.om.size := hin
  have hlo : cfLo g0.om off.toNat = off.toNat := cfLo_in hin'
  have hhi : cfHi g0.om off.toNat data.length = off.toNat + data.length := cfHi_in hin'
  ihave Hrg := (show osBytes d.ino (cfLo g0.om off.toNat) (DFrac.own 1)
      (cfRange g0.om g0.bs off.toNat data.length) ⊢ osBytes d.ino off.toNat
      (DFrac.own 1) (cfRange g0.om g0.bs off.toNat data.length) by rw [hlo]) $$ Hrg
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osPWriteStart fd off data dq d g0.om (cfRange g0.om g0.bs off.toNat data.length)
    osN_sub_nwal hwr hoff0 (by omega) hd
    (by rw [cfRange_length hin' hlen]; omega)
    $$ Hos Hfd Hm Hrg []
  · rw [hm.2.1]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
  iintro %t %n %hfr Hfd Htok
  have hn : 0 < n := hfr.2.2
  let fl : SegFl := ⟨t, off.toNat, data, n, g0.om, g0.bs, none⟩
  let g' := segAnn g0 off.toNat data n
  let F' : GMap Ino SegFl := <[g0.ino := fl]> F
  have hpre' : data <+: (segStream walCodec Mr dw lay.cuts lay.cuts.length).drop off.toNat := by
    rw [← hcuts]; rw [hH, hmd] at hS; exact hS
  have hoff1 : 0 < off.toNat := by have h1 := walAbsD_so_pos habs; omega
  imod tailVar_update γ _ _ (tailG dw (tailLay lay pre g' lay.wr) g'.ino (F' !! g'.ino)) $$ Hv Hv'
    with ⟨Hv, Hv'⟩
  ihave Hb := Hclose $$ %g' %lay.wr %F' [] [Htok Hp2 Hs2] Hv'
  · ipureintro
    refine ⟨hino.symm, rfl, by simp [g', segAnn, cfMeta, hcut0], segAnn_length hin' hlen, ?_, ?_, ?_⟩
    · intro z hz; rw [hlen]; exact hm.2.2 z hz
    · intro ents' habs'; exact walAbsD_announce habs' hs hso hin' hpre' hn
    · intro i hi; exact GMap.lookup_insert_ne _ _ (fun h => hi (h.symm.trans hino.symm))
  · rw [show F' !! g'.ino = some fl from GMap.lookup_insert _ _ _]
    dsimp only [fl]
    rw [show g'.ino = d.ino from hino.symm]
    iframe Htok Hp2 Hs2
    ipureintro
    exact segAnn_ok hin' hd hlen hcut0 hoff1
  imod Hid
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  have e : tailG dw (tailLay lay pre g' lay.wr) g'.ino (F' !! g'.ino) =
      ((H, md, cuts, wr, d.ino, some fl) : TailG) := by
    rw [show F' !! g'.ino = some fl from GMap.lookup_insert _ _ _]
    simp only [tailG, tailLay, g', segAnn]
    rw [hH, hmd, hcuts, hwrl, hino]
  rw [e, hlo, hhi]
  iapply HΦ $$ %t %n %(⟨hn, hoff1⟩ : 0 < n ∧ 0 < off.toNat) Hfd
  unfold walTailFl
  iframe Hk Hv Hp1 Hs1

/-- **The second step of a `pwrite` on the tail** (see the file header): the `k` bytes written, the
write position past them (or where it was, for a retry below it), the file idle; the write's range
carries its candidate, stamped positive (a retry from it is past the synced bytes). -/
theorem wp_tailPWriteFinish (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat) (i : Ino)
    (fl : SegFl) (Φ : val → IProp GF) (hrz : fl.rz = none) (hn : 0 < fl.n) (hm : TailMeta fl.m fl.bs)
    (hoff : 0 < fl.off) (hoffl : fl.off ≤ fl.bs.length) (hwrf : fl.off ≤ wr) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      walTailFl dir γ (H, md, cuts, wr, i, some fl) i fl -∗
      (∀ (k : Nat) (e : w64) (zs : List Cands),
        ⌜k ≤ fl.data.length ∧ ((k = fl.data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          TailMeta (pwPost fl.m fl.off fl.data.length k) (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) ∧
          (pwPost fl.m fl.off fl.data.length k).size = fl.m.size ∧
          (∀ b, fl.off ≤ b → b < fl.off + fl.data.length →
            ∃ q ∈ ((finBytes fl.m fl.bs fl.off fl.data k fl.n zs).getD b (0, [])).2, 0 < q.2)⌝ -∗
        walTailKey (W := W) dir γ -∗
        tailVar (W := W) γ ((H, md, cuts, max wr (fl.off + k), i, none) : TailG) -∗
        osMeta i (DFrac.own (1 : Qp).half) (pwPost fl.m fl.off fl.data.length k) -∗
        osBytes i 0 (DFrac.own (1 : Qp).half) (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV fl.t))) {{ Φ }} := by
  iintro #Harea Hfl HΦ
  unfold walTailFl
  icases Hfl with ⟨Hk, Hv, Hp1, Hs1⟩
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  obtain ⟨x, xs, hxs⟩ : ∃ x xs, fl.bs.take fl.off = x :: xs := by
    cases h : fl.bs.take fl.off with
    | nil => have := congrArg List.length h; simp only [List.length_take, List.length_nil] at this; omega
    | cons x xs => exact ⟨x, xs, rfl⟩
  ihave Hp1 := (show osBytes i 0 (DFrac.own (1 : Qp).half) (fl.bs.take fl.off) ⊢
    osBytes (((H, md, cuts, wr, i, some fl) : TailG).2.2.2.2.1) 0 (DFrac.own (1 : Qp).half)
      (x :: xs) by rw [hxs]) $$ Hp1
  icases walInvBody_tail walCodec walCodec_ok Mr R jr r s dir γ _ x xs $$ Hb Hk Hv Hp1 with
    ⟨%F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hp1, Hclose⟩
  ihave Hp1 := (show osBytes (((H, md, cuts, wr, i, some fl) : TailG).2.2.2.2.1) 0
    (DFrac.own (1 : Qp).half) (x :: xs) ⊢ osBytes i 0 (DFrac.own (1 : Qp).half) (fl.bs.take fl.off)
      by rw [hxs]) $$ Hp1
  obtain ⟨hdw, hs, htg, ⟨ents, habs⟩, hcut0⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
  unfold segResF
  rw [← hF]
  dsimp only
  rw [hrz]
  dsimp only
  icases Hseg with ⟨Htok, Hp2, Hs2, %hok⟩
  have hok' := hok
  obtain ⟨hin, hd, hl, hmc, hom, hbs, hoff0⟩ := hok'
  have hlo : cfLo fl.m fl.off = fl.off := cfLo_in hin
  have hhi : cfHi fl.m fl.off fl.data.length = fl.off + fl.data.length := cfHi_in hin
  subst hino
  unfold pwTok
  icases Htok with ⟨Htok, %hgap⟩
  obtain ⟨hgap, -, -⟩ := hgap
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osPWriteFinish fl.t g0.ino fl.off fl.data fl.m (cfRange fl.m fl.bs fl.off fl.data.length)
    fl.n osN_sub_nwal $$ Hos [Htok]
  · unfold pwTok; iframe; ipureintro
    exact ⟨hgap, hd, by rw [cfRange_length hin hl]; omega⟩
  iintro %k %e %zs %hke %- Hm Hrg -
  have hk := hke.1
  have hps : pwSize fl.m.size fl.off k = fl.m.size := by unfold pwSize; split <;> omega
  have hflen : (finBytes fl.m fl.bs fl.off fl.data k fl.n zs).length = fl.m.size := by
    rw [finBytes_length hl hgap hk, hps]
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  have hl1 : 0 + (fl.bs.take (cfLo fl.m fl.off)).length = fl.off := by
    simp only [List.length_take]; rw [hlo]; omega
  have hl2 : fl.off + (pwBytes fl.m.size fl.off fl.data k fl.n (cfRange fl.m fl.bs fl.off fl.data.length) zs).length =
      cfHi fl.m fl.off fl.data.length ∨ fl.bs.drop (cfHi fl.m fl.off fl.data.length) = [] := by
    left; rw [pwBytes_length, hps, hhi]; omega
  ihave Hb1 := osBytes_join3 g0.ino 0 fl.off (cfHi fl.m fl.off fl.data.length) _ _ _ _ hl1 hl2
    $$ [Hp1 Hr1 Hs1]
  · rw [hlo, hhi]; iframe
  ihave Hb2 := osBytes_join3 g0.ino 0 fl.off (cfHi fl.m fl.off fl.data.length) _ _ _ _ hl1 hl2
    $$ [Hp2 Hr2 Hs2]
  · iframe
  have hfb : ∀ dq, (osBytes g0.ino 0 dq (fl.bs.take (cfLo fl.m fl.off) ++
      pwBytes fl.m.size fl.off fl.data k fl.n (cfRange fl.m fl.bs fl.off fl.data.length) zs ++
      fl.bs.drop (cfHi fl.m fl.off fl.data.length)) : IProp GF) ⊢
      osBytes g0.ino 0 dq (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) := fun _ => by
    unfold finBytes; exact .rfl
  ihave Hb1 := hfb _ $$ Hb1
  ihave Hb2 := hfb _ $$ Hb2
  let g' := segFin fl g0 k zs
  let F' : GMap Ino SegFl := GMap.delete g0.ino F
  imod tailVar_update γ _ _ (tailG dw (tailLay lay pre g' (max lay.wr (fl.off + k))) g'.ino
    (F' !! g'.ino)) $$ Hv Hv' with ⟨Hv, Hv'⟩
  have hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z := by
    intro z hz
    rw [hom] at hz
    simp only [cfMeta, announce_zf, Option.map_eq_some_iff] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    have h1 := hm.2.2 z0 hz0
    have h2 : g0.bs.length = fl.m.size := by
      rw [hbs]; simp only [List.length_append, List.length_take, List.length_drop, pwAnn_length]
      rw [cfRange_length hin hl, hlo, hhi]; omega
    rw [h2]; split <;> omega
  ihave Hb := Hclose $$ %g' %(max lay.wr (fl.off + k)) %F' [] [Hm2 Hb2] Hv'
  · ipureintro
    refine ⟨rfl, rfl, by simp [g', segFin, pwPost, hmc], segFin_length hok hk, hzf0, ?_, ?_⟩
    · intro ents' habs'; exact walAbsD_finish habs' hs hok (by omega) hk hn
    · intro i' hi; exact GMap.lookup_delete_ne _ (Ne.symm hi)
  · rw [show F' !! g'.ino = none from GMap.lookup_delete_eq _ _]
    dsimp only
    unfold segRes
    dsimp only [g', segFin]
    iframe Hm2 Hb2
  imod Hid
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  have htm : TailMeta (pwPost fl.m fl.off fl.data.length k) (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) := by
    refine ⟨by rw [hflen]; simp [pwPost, hps], by simp [pwPost, hm.2.1], ?_⟩
    intro z hz
    simp only [pwPost, announce_zf, Option.map_eq_some_iff] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    have := hm.2.2 z0 hz0
    simp only [pwPost, hps]; split <;> omega
  have hpost : k ≤ fl.data.length ∧ ((k = fl.data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
      TailMeta (pwPost fl.m fl.off fl.data.length k) (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) ∧
      (pwPost fl.m fl.off fl.data.length k).size = fl.m.size ∧
      (∀ b, fl.off ≤ b → b < fl.off + fl.data.length →
        ∃ q ∈ ((finBytes fl.m fl.bs fl.off fl.data k fl.n zs).getD b (0, [])).2, 0 < q.2) :=
    ⟨hk, hke.2.1, htm, by simp [pwPost, hps], fun b h1 h2 => segFin_cand (zs := zs) hok hk hn b h1 h2⟩
  have htv : tailG dw (tailLay lay pre g' (max lay.wr (fl.off + k))) g'.ino (F' !! g'.ino) =
      ((H, md, cuts, max wr (fl.off + k), g0.ino, none) : TailG) := by
    rw [show F' !! g'.ino = none from GMap.lookup_delete_eq _ _]
    simp only [tailG, tailLay, g', segFin]
    rw [hH, hmd, hcuts, hwrl]
  rw [htv]
  iapply HΦ $$ %k %e %zs %hpost Hk Hv Hm1
  iexact Hb1

/-- **`(*os.File).WriteAt` on the tail** (the model's loop, `TrustedCode/os.lean`'s
`File.WriteAt.impl`): its attempts are the two steps above, in chunks of at most `maxRW`, each from
where the bytes written so far end (after a short write) or from where the last attempt started
(after `EINTR`: the bytes it wrote are rewritten, the record's write position staying past them).
On success the record's write position is past `data`, the tail as the steps left it; on an error
the handle's parts of the tail are lost (the invariant keeps the bytes as written). -/
theorem wp_tailWriteAt (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (bs : List ByteG)
    (hwr : d.writable = true) (hoff0 : 0 ≤ off.toInt) (hn : 0 < data.length)
    (hin : off.toNat + data.length ≤ m.size) (hbig : off.toNat + data.length < 2 ^ 63)
    (hS : data <+: (tailStream Mr H md cuts).drop off.toNat) (hm : TailMeta m bs) :
    {{ walAreaOk walCodec Mr R jr r ∗ os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗
        osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ ((H, md, cuts, off.toNat, d.ino, none) : TailG) ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
        (Val #off))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗
        ((⌜err = interface.nil ∧ n = sl.len⌝ ∗ osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
            tailVar (W := W) γ ((H, md, cuts, off.toNat + data.length, d.ino, none) : TailG) ∗
            ∃ (m' : OsMeta) (bs' : List ByteG), osMeta d.ino (DFrac.own (1 : Qp).half) m' ∗
              osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs' ∗ ⌜TailMeta m' bs' ∧ m'.size = m.size⌝) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  unfold os.ownFile
  wp_start as ⟨#Harea, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hk, Hv, Hm, Hb⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwfs
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff0
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  -- the loop's state: `nn` bytes written, the record's write position `wr` (at most one chunk
  -- past them: an attempt that `EINTR` stopped may have written past `nn`), the tail `m'`, `bs'`
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  obtain ⟨wr, hwr0⟩ : ∃ wr : Nat, wr = off.toNat := ⟨_, rfl⟩
  have hW0 : (W64 0).toNat = 0 := rfl
  have hnn : nnv.toNat < data.length := by subst hnnv; rw [hW0]; exact hn
  have hwa : off.toNat + nnv.toNat ≤ wr := by subst hnnv hwr0; rw [hW0]; omega
  have hwc : wr ≤ off.toNat + nnv.toNat + min (data.length - nnv.toNat) 1073741824 := by
    subst hnnv hwr0; rw [hW0]; omega
  have hre : off.toNat + nnv.toNat = wr ∨
      ∃ q ∈ (bs'.getD (off.toNat + nnv.toNat) (0, [])).2, 0 < q.2 := by
    subst hnnv hwr0; left; rw [hW0]; rfl
  have hm2 : TailMeta m' bs' ∧ m'.size = m.size := by subst hm' hbs'; exact ⟨hm, rfl⟩
  ihave Hm := (show osMeta d.ino (DFrac.own (1 : Qp).half) m ⊢
    osMeta d.ino (DFrac.own (1 : Qp).half) m' by rw [hm']) $$ Hm
  ihave Hb := (show osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs ⊢
    osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs' by rw [hbs']) $$ Hb
  ihave Hv := (show tailVar (W := W) γ ((H, md, cuts, off.toNat, d.ino, none) : TailG) ⊢
    tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) by rw [hwr0]) $$ Hv
  clear hm' hbs' hnnv hwr0
  iloeb as IH generalizing %m' %bs' %nnv %wr %hnn %hwa %hwc %hre %hm2 Hm Hb Hv Hk Hosfd Hsl Hfd HΦ
  -- one attempt, from `nn`
  have hnnz : sint.Z nnv = nnv.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  have hsub : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by
    have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
    have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
    word
  wp_auto
  by_cases hA : 1073741824 < data.length - nnv.toNat
  rw [decide_eq_true (show sint.Z (W64 1073741824) < sint.Z (sl.len - nnv) by
    rw [hsub, hslz, hnnz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega)]
  wp_auto
  have hmx : sint.Z (nnv + W64 1073741824) = nnv.toNat + 1073741824 := by
    have : sint.Z nnv + 1073741824 < 2 ^ 63 := by rw [hnnz]; omega
    have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
    rw [← hnnz]; simp only [sint.Z] at *; word
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z (nnv + W64 1073741824) ∧
      sint.Z (nnv + W64 1073741824) ≤ sint.Z sl.cap := by
    rw [hnnz, hmx]; have := Hwfs.2; rw [hslz] at this; omega
  rw [if_pos hsb]
  have hsb' : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z (nnv + W64 1073741824) ∧
      sint.Z (nnv + W64 1073741824) ≤ sint.Z sl.len := by
    rw [hnnz, hmx, hslz]; omega
  ihave ⟨Hs0, Hs1, Hs2⟩ := (ownSlice_slice nnv (nnv + W64 1073741824) sl dqs data hsb').1 $$ Hsl
  wp_apply wp_bytes_to_string _ _ dqs $$ Hs1 as Hs1
  ihave Hsl := (ownSlice_slice nnv (nnv + W64 1073741824) sl dqs data hsb').2 $$ [Hs0 Hs1 Hs2]
  · iframe
  have hcl : (subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data).length =
      min (data.length - nnv.toNat) 1073741824 := by
    have : sint.nat (nnv + W64 1073741824) = nnv.toNat + 1073741824 := by
      show (sint.Z _).toNat = _; rw [hmx]; omega
    simp only [subslice, List.length_drop, List.length_take, hnnn, this]
    exact (fun a L (h : 1073741824 < L - a) => show min (a + 1073741824) L - a = min (L - a) 1073741824
      by omega) _ _ hA
  have hcp : subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data <+:
      data.drop nnv.toNat := by
    simp only [subslice, hnnn]; rw [List.drop_take]; exact List.take_prefix _ _
  generalize subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data = chunk at hcl hcp ⊢
  rotate_left
  rw [decide_eq_false (show ¬ sint.Z (W64 1073741824) < sint.Z (sl.len - nnv) by
    rw [hsub, hslz, hnnz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega)]
  wp_auto
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [hnnz, hslz]; have := Hwfs.2; omega
  rw [if_pos hsb]
  have hsb' : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.len := by
    rw [hnnz, hslz]; omega
  ihave ⟨Hs0, Hs1, Hs2⟩ := (ownSlice_slice nnv sl.len sl dqs data hsb').1 $$ Hsl
  wp_apply wp_bytes_to_string _ _ dqs $$ Hs1 as Hs1
  ihave Hsl := (ownSlice_slice nnv sl.len sl dqs data hsb').2 $$ [Hs0 Hs1 Hs2]
  · iframe
  have hcl : (subslice (sint.nat nnv) (sint.nat sl.len) data).length =
      min (data.length - nnv.toNat) 1073741824 := by
    have : sint.nat sl.len = data.length := by show (sint.Z _).toNat = _; rw [hslz]; omega
    simp only [subslice, List.length_drop, List.length_take, hnnn, this]
    exact (fun a L (h : ¬ 1073741824 < L - a) => show min L L - a = min (L - a) 1073741824
      by omega) _ _ hA
  have hcp : subslice (sint.nat nnv) (sint.nat sl.len) data <+: data.drop nnv.toNat := by
    simp only [subslice, hnnn]; rw [List.drop_take]; exact List.take_prefix _ _
  generalize subslice (sint.nat nnv) (sint.nat sl.len) data = chunk at hcl hcp ⊢
  all_goals
    have hc0 : 0 < chunk.length := by rw [hcl]; omega
    have hcne : chunk ≠ [] := List.ne_nil_of_length_pos hc0
    have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
      rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
    have hoffv' : 0 ≤ (off + nnv).toInt := by
      rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
    have hin' : (off + nnv).toNat + chunk.length ≤ m'.size := by rw [hoffv, hm2.2]; omega
    have hS' : chunk <+: (tailStream Mr H md cuts).drop (off + nnv).toNat := by
      obtain ⟨t, ht⟩ := hS
      have e : (tailStream Mr H md cuts).drop (off + nnv).toNat = data.drop nnv.toNat ++ t := by
        have e1 : ((tailStream Mr H md cuts).drop off.toNat).drop nnv.toNat =
            (tailStream Mr H md cuts).drop (off + nnv).toNat := by
          rw [List.drop_drop, hoffv]; try (congr 1; omega)
        rw [← e1, ← ht, List.drop_append_of_le_length (by omega)]
      rw [e]; exact hcp.trans (List.prefix_append _ _)
    wp_apply wp_tailPWriteStart Mr R jr r dir γ H md cuts wr m' bs' fd (off + nnv) chunk dq d _ hwr
      hoffv' (by rw [hoffv]; exact hwa) (by rw [hoffv]; exact hre) hcne hin' hS' hm2.1
      $$ Harea Hosfd Hk Hv Hm Hb as %t %nst %hfr Hosfd Hfl
    wp_apply wp_tailPWriteFinish Mr R jr r dir γ H md cuts wr d.ino
      ⟨t, (off + nnv).toNat, chunk, nst, m', bs', none⟩ _ rfl hfr.1 hm2.1 hfr.2
      (by show (off + nnv).toNat ≤ bs'.length; rw [hoffv, hm2.1.1, hm2.2]; omega)
      (by show (off + nnv).toNat ≤ wr; rw [hoffv]; exact hwa)
      $$ Harea Hfl as %k %e %zs %hke Hk Hv Hm Hb
    dsimp only at hke
    obtain ⟨hk, hke2, htm, hsz, hcand⟩ := hke
    have hm2' : TailMeta (pwPost m' (off + nnv).toNat chunk.length k)
        (finBytes m' bs' (off + nnv).toNat chunk k nst zs) ∧
        (pwPost m' (off + nnv).toNat chunk.length k).size = m.size := ⟨htm, hsz.trans hm2.2⟩
    wp_auto
    by_cases he4 : e = W64 4
    · -- `EINTR`: the attempt again, from `nn`
      rw [decide_eq_true he4]
      wp_pure
      have hre' : off.toNat + nnv.toNat = max wr ((off + nnv).toNat + k) ∨
          ∃ q ∈ ((finBytes m' bs' (off + nnv).toNat chunk k nst zs).getD
            (off.toNat + nnv.toNat) (0, [])).2, 0 < q.2 := by
        right; rw [← hoffv]; exact hcand _ (Nat.le_refl _) (by omega)
      iapply IH $$ %(pwPost m' (off + nnv).toNat chunk.length k)
        %(finBytes m' bs' (off + nnv).toNat chunk k nst zs) %nnv %(max wr ((off + nnv).toNat + k))
        %hnn %(by omega) %(by rw [hoffv]; omega) %hre' %hm2' Hm Hb Hv Hk Hosfd Hsl Hfd HΦ
    · rw [decide_eq_false he4]
      wp_auto
      have hWk : (W64 k).toNat = k := by
        simp only [W64]; rw [BitVec.toNat_ofInt]; omega
      have hnk : (nnv + W64 k).toNat = nnv.toNat + k := by
        rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
      by_cases hfull : nnv + W64 k = sl.len
      · rw [decide_eq_true hfull]
        wp_auto
        have hfk : nnv.toNat + k = data.length := by
          have := congrArg BitVec.toNat hfull; rw [hnk, hsln] at this
          simp only [W64] at this; rw [BitVec.toNat_ofInt] at this; omega
        by_cases he0 : e = W64 0
        · rw [decide_eq_true he0]
          wp_auto
          have ew : max wr ((off + nnv).toNat + k) = off.toNat + data.length := by
            rw [hoffv]; omega
          ihave Hv := (show tailVar (W := W) γ
              ((H, md, cuts, max wr ((off + nnv).toNat + k), d.ino, none) : TailG) ⊢
            tailVar (W := W) γ ((H, md, cuts, off.toNat + data.length, d.ino, none) : TailG)
              by rw [ew]) $$ Hv
          iapply HΦ
          iframe Hsl
          isplitl [Hfd]
          · iexists inner; iframe; isplitl [] <;> iassumption
          ileft
          iframe Hosfd Hk Hv
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          iexists _, _
          iframe Hm Hb
          ipureintro; exact hm2'
        · rw [decide_eq_false he0]
          wp_auto
          simp only [decide_eq_false he0, Bool.not_false]
          wp_auto
          wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
          iapply HΦ
          iframe Hsl
          isplitl [Hfd]
          · iexists inner; iframe; isplitl [] <;> iassumption
          iright
          ipureintro; intro h; cases h
      · rw [decide_eq_false hfull]
        wp_auto
        by_cases he0 : e = W64 0
        · -- a short write: the next attempt from `nn + k`
          rw [decide_eq_true he0]
          simp only [Bool.not_true]
          wp_pure
          have hk0 : 0 < k := by
            rcases hke2 with ⟨h | h, -⟩ | h
            · omega
            · exact h
            · exact absurd he0 h
          have hne : nnv.toNat + k ≠ data.length := by
            intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
            rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
          have hre' : off.toNat + (nnv + W64 k).toNat = max wr ((off + nnv).toNat + k) ∨
              ∃ q ∈ ((finBytes m' bs' (off + nnv).toNat chunk k nst zs).getD
                (off.toNat + (nnv + W64 k).toNat) (0, [])).2, 0 < q.2 := by
            rw [hnk]
            by_cases hlt : off.toNat + (nnv.toNat + k) < max wr ((off + nnv).toNat + k)
            · right
              rw [show off.toNat + (nnv.toNat + k) = (off + nnv).toNat + k by rw [hoffv]; omega]
              exact hcand _ (by omega) (by rw [hoffv] at hlt ⊢; omega)
            · left; rw [hoffv] at hlt ⊢; omega
          iapply IH $$ %(pwPost m' (off + nnv).toNat chunk.length k)
            %(finBytes m' bs' (off + nnv).toNat chunk k nst zs) %(nnv + W64 k)
            %(max wr ((off + nnv).toNat + k)) %(by rw [hnk]; omega) %(by rw [hnk, hoffv]; omega)
            %(by rw [hnk, hoffv]; omega) %hre' %hm2' Hm Hb Hv Hk Hosfd Hsl Hfd HΦ
        · rw [decide_eq_false he0]
          simp only [Bool.not_false]
          wp_auto
          wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
          iapply HΦ
          iframe Hsl
          isplitl [Hfd]
          · iexists inner; iframe; isplitl [] <;> iassumption
          iright
          ipureintro; intro h; cases h

/-- **The tail's writer** (see the file header): the tail file `f` of inode `i`, written from the
encoder's start `o0`, is a guarded stream of its intended bytes (`tailOk`); a failed write leaves
nothing the program keeps (the invariant holds what it wrote; the handle is lost). -/
theorem wal.tailWriter (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64)
    (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o0 sz : Nat) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      io.writerStreamP (wal.fileWi f) (tailOk Mr H md cuts o0 sz)
        (walTailW (W := W) f fd name dir γ i H md cuts o0 sz) (fun _ _ => iprop(True)) := by
  sorry

end tail

end WalFs
end EtcdGrove
end Perennial

end
