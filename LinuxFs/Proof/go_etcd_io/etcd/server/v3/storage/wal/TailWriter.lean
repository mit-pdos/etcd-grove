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
`wp_tailWriteAt` (the model's `WriteAt` loop over the two steps; its arithmetic through the small
`Nat` lemmas `tw_*`), `wp_tailWrite` and `wal.tailWriter` proved, no `sorry`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.os.CrashWrite
public import LinuxFs.Proof.os.CrashOps
public import LinuxFs.Proof.os.WriterStream
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
  icases walInvBody_tail walCodec walCodec_ok Mr R jr r s dir γ _ m $$ Hb Hk Hv [Hm1] with
    ⟨%F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hm1, Hclose⟩
  · dsimp only [tailHeld]; iexact Hm1
  dsimp only [tailHeld]
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
  have hex0 : SegExact g0 := ⟨by rw [hm.2.2.2.1, hlen], by rw [hm.2.2.2.2, hlen]⟩
  -- the write is past the synced bytes
  have hso : lay.so ≤ off.toNat := by
    obtain ⟨hso', -, -, -, hB, -⟩ := (habs.last g0 hg0).1 hex0
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
    refine ⟨hino.symm, by simp [g', segAnn, cfMeta, hcut0], segAnn_length hin' hlen, ?_, ?_, ?_⟩
    · refine ⟨fun z hz => by rw [hlen]; exact hm.2.2.1 z hz, hex0, ?_⟩
      have hT : max g0.om.size (off.toNat + data.length) = g0.om.size := by omega
      have e1 := hex0.1
      have e2 := hex0.2
      refine ⟨?_, ?_⟩ <;> rw [show g'.bs.length = g0.bs.length from segAnn_length hin' hlen] <;>
        simp only [g', segAnn, cfMeta, announce_lo, announce_hi, hT] <;> omega
    · intro ents' habs'; exact walAbsD_announce habs' hs hex0 hso hin' hpre' hn
    · exact ⟨fun i hi => GMap.lookup_insert_ne _ _ (fun h => hi (h.symm.trans hino.symm)), rfl⟩
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
  icases walInvBody_tail walCodec walCodec_ok Mr R jr r s dir γ _ fl.m $$ Hb Hk Hv [] with
    ⟨%F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', -, Hclose⟩
  · dsimp only [tailHeld]; iempintro
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
    have h1 := hm.2.2.1 z0 hz0
    have h2 : g0.bs.length = fl.m.size := by
      rw [hbs]; simp only [List.length_append, List.length_take, List.length_drop, pwAnn_length]
      rw [cfRange_length hin hl, hlo, hhi]; omega
    rw [h2]; split <;> omega
  have hgl : g0.bs.length = fl.m.size := by
    rw [hbs]; simp only [List.length_append, List.length_take, List.length_drop, pwAnn_length]
    rw [cfRange_length hin hl, hlo, hhi]; omega
  have hmlo := hm.2.2.2.1
  have hmhi := hm.2.2.2.2
  have hT : max fl.m.size (fl.off + fl.data.length) = fl.m.size := by omega
  have hex0 : SegExact g0 := by
    refine ⟨?_, ?_⟩ <;> rw [hom, hgl] <;> simp only [cfMeta, announce_lo, announce_hi, hT] <;> omega
  have hexF : SegExact g' := by
    refine ⟨?_, ?_⟩ <;> simp only [g', segFin, hflen, pwPost, announce_lo, announce_hi, hT] <;> omega
  ihave Hb := Hclose $$ %g' %(max lay.wr (fl.off + k)) %F' [] [Hm2 Hb2] Hv'
  · ipureintro
    refine ⟨rfl, by simp [g', segFin, pwPost, hmc], segFin_length hok hk, ⟨hzf0, hex0, ?_⟩, ?_, ?_⟩
    · exact hexF
    · intro ents' habs'; exact walAbsD_finish habs' hs hex0 hok (by omega) hk hn
    · exact ⟨fun i' hi => GMap.lookup_delete_ne _ (Ne.symm hi), rfl⟩
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
    refine ⟨by rw [hflen]; simp [pwPost, hps], by simp [pwPost, hm.2.1], ?_, ?_, ?_⟩
    rotate_left
    · have := hm.2.2.2.1; simp only [pwPost, announce_lo, hps]; omega
    · have := hm.2.2.2.2; simp only [pwPost, announce_hi, hps]; omega
    intro z hz
    simp only [pwPost, announce_zf, Option.map_eq_some_iff] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    have := hm.2.2.1 z0 hz0
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

/-! The arithmetic of `wp_tailWriteAt`'s loop, as small lemmas over `Nat` (an `omega` in the loop's
context, next to its `BitVec` facts, blew up past 14 GB: W6 log, sixth session). -/

theorem tw_toInt (x : w64) (h : x.toNat < 2 ^ 63) : sint.Z x = (x.toNat : Int) := by
  simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]

theorem tw_nat (x : w64) (h : x.toNat < 2 ^ 63) : sint.nat x = x.toNat := by
  simp [sint.nat, tw_toInt x h]

theorem tw_len (len : w64) (L : Nat) (h : sint.Z len = (L : Int)) (hL : L < 2 ^ 63) :
    len = W64 (L : Int) := by
  apply BitVec.eq_of_toInt_eq
  simp only [sint.Z] at h
  rw [h, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega

theorem tw_addk (x : w64) (k : Nat) (h : x.toNat + k < 2 ^ 63) :
    (x + W64 (k : Int)).toNat = x.toNat + k := by
  have hk : (W64 (k : Int)).toNat = k := by simp only [W64]; rw [BitVec.toNat_ofInt]; omega
  rw [BitVec.toNat_add, hk]; exact Nat.mod_eq_of_lt (by omega)

theorem tw_Wk (k : Nat) (h : k < 2 ^ 63) : (W64 (k : Int)).toNat = k := by
  simp only [W64]; rw [BitVec.toNat_ofInt]; omega

theorem tw_sub (len x : w64) (L : Nat) (hl : sint.Z len = (L : Int)) (hx : x.toNat ≤ L)
    (hL : L < 2 ^ 63) : sint.Z (len - x) = (L : Int) - (x.toNat : Int) := by
  have hxz := tw_toInt x (by omega)
  have h1 : sint.Z x ≤ sint.Z len := by rw [hxz, hl]; omega
  have h2 : 0 ≤ sint.Z x := by rw [hxz]; omega
  rw [← hxz, ← hl]; clear hxz hl hx; word

theorem tw_addMax (x : w64) (h : x.toNat + 1073741824 < 2 ^ 63) :
    sint.Z (x + W64 1073741824) = (x.toNat : Int) + 1073741824 := by
  have e := tw_addk x 1073741824 h
  rw [show (W64 1073741824 : w64) = W64 ((1073741824 : Nat) : Int) from rfl,
    tw_toInt _ (by rw [e]; omega), e]
  omega

theorem tw_offAdd (off x : w64) (h : off.toNat + x.toNat < 2 ^ 63) :
    (off + x).toNat = off.toNat + x.toNat ∧ 0 ≤ (off + x).toInt := by
  have e : (off + x).toNat = off.toNat + x.toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  refine ⟨e, ?_⟩
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [e]; omega)]; omega

theorem tw_full_iff (x : w64) (k L : Nat) (hx : x.toNat + k < 2 ^ 63) (hL : L < 2 ^ 63) :
    x + W64 (k : Int) = W64 (L : Int) ↔ x.toNat + k = L := by
  constructor
  · intro h; have e := congrArg BitVec.toNat h; rw [tw_addk x k hx, tw_Wk L hL] at e; exact e
  · intro h; apply BitVec.eq_of_toNat_eq; rw [tw_addk x k hx, tw_Wk L hL]; exact h

theorem tw_dec (L a : Nat) : ((1073741824 : Int) < (L : Int) - (a : Int)) ↔ 1073741824 < L - a := by
  omega

theorem tw_sbBig (a L : Nat) (cap : Int) (hcap : (L : Int) ≤ cap) (h : 1073741824 < L - a) :
    0 ≤ (a : Int) ∧ (a : Int) ≤ (a : Int) + 1073741824 ∧ (a : Int) + 1073741824 ≤ cap ∧
      (a : Int) + 1073741824 ≤ (L : Int) := by omega

theorem tw_sbSmall (a L : Nat) (cap : Int) (hcap : (L : Int) ≤ cap) (h : a < L) :
    0 ≤ (a : Int) ∧ (a : Int) ≤ (L : Int) ∧ (L : Int) ≤ cap := by omega

theorem tw_toNat_int (a : Int) (b : Nat) (h : a = (b : Int) + 1073741824) : a.toNat = b + 1073741824 := by
  omega

theorem tw_lenBig (a L : Nat) (h : 1073741824 < L - a) : min (a + 1073741824) L - a = 1073741824 := by
  omega

theorem tw_lenSmall (a L : Nat) (h : ¬ 1073741824 < L - a) : min L L - a = L - a := by omega

theorem tw_max (wr x : Nat) : wr ≤ max wr x ∧ x ≤ max wr x ∧ (max wr x = wr ∨ max wr x = x) := by
  omega

/-- The loop's invariant after an attempt that `EINTR` stopped (`nn` unchanged). -/
theorem tw_eintr (o a L wr k c w' : Nat) (h2 : o + a ≤ wr) (h3 : wr ≤ o + L)
    (h4 : wr ≤ o + a + 1073741824) (hc1 : c ≤ L - a) (hc3 : c ≤ 1073741824) (hk : k ≤ c)
    (hw1 : wr ≤ w') (hw2 : o + a + k ≤ w') (hw3 : w' = wr ∨ w' = o + a + k) (hc0 : 0 < c) :
    o + a ≤ w' ∧ w' ≤ o + L ∧ w' ≤ o + a + 1073741824 ∧ o + a < o + a + c := by omega

/-- The loop's invariant after a short write (`nn + k` written). -/
theorem tw_short (o a L wr k c w' : Nat) (h1 : a < L) (h2 : o + a ≤ wr) (h3 : wr ≤ o + L)
    (h4 : wr ≤ o + a + 1073741824) (hc1 : c ≤ L - a) (hc2 : c = L - a ∨ c = 1073741824)
    (hk : k ≤ c) (hne : a + k ≠ L)
    (hw1 : wr ≤ w') (hw2 : o + a + k ≤ w') (hw3 : w' = wr ∨ w' = o + a + k) :
    a + k < L ∧ o + (a + k) ≤ w' ∧ w' ≤ o + L ∧ w' ≤ o + (a + k) + 1073741824 ∧
      (o + (a + k) = w' ∨ (o + a ≤ o + a + k ∧ o + a + k < o + a + c)) := by omega

/-- The write position after the last attempt. -/
theorem tw_full (o a L wr k w' : Nat) (h3 : wr ≤ o + L) (hfk : a + k = L) (hw1 : wr ≤ w')
    (hw2 : o + a + k ≤ w') (hw3 : w' = wr ∨ w' = o + a + k) : w' = o + L := by omega

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
  have hslz : sint.Z sl.len = (data.length : Int) := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hL63 : data.length < 2 ^ 63 := by omega
  have hsln : sl.len = W64 (data.length : Int) := tw_len sl.len data.length hslz hL63
  have hcap : (data.length : Int) ≤ sint.Z sl.cap := by rw [← hslz]; exact Hwfs.2
  clear Hlen Hwfs h0 hl0
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
  have hwb : wr ≤ off.toNat + data.length := by subst hwr0; omega
  have hwc : wr ≤ off.toNat + nnv.toNat + 1073741824 := by subst hnnv hwr0; rw [hW0]; omega
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
  clear hm' hbs' hnnv hwr0 hW0
  iloeb as IH generalizing %m' %bs' %nnv %wr %hnn %hwa %hwb %hwc %hre %hm2 Hm Hb Hv Hk Hosfd Hsl
    Hfd HΦ
  -- one attempt, from `nn`
  have hnn63 : nnv.toNat < 2 ^ 63 := Nat.lt_trans hnn hL63
  have hnnz := tw_toInt nnv hnn63
  have hnnn := tw_nat nnv hnn63
  have hsub := tw_sub sl.len nnv data.length hslz (Nat.le_of_lt hnn) hL63
  wp_auto
  by_cases hA : 1073741824 < data.length - nnv.toNat
  rw [decide_eq_true (show sint.Z (W64 1073741824) < sint.Z (sl.len - nnv) by
    rw [hsub, show sint.Z (W64 1073741824) = 1073741824 from rfl]; exact (tw_dec _ _).2 hA)]
  wp_auto
  have hmx := tw_addMax nnv (by omega)
  obtain ⟨hs1, hs2, hs3, hs4⟩ := tw_sbBig nnv.toNat data.length _ hcap hA
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z (nnv + W64 1073741824) ∧
      sint.Z (nnv + W64 1073741824) ≤ sint.Z sl.cap := by
    rw [hnnz, hmx]; exact ⟨hs1, hs2, hs3⟩
  rw [if_pos hsb]
  have hsb' : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z (nnv + W64 1073741824) ∧
      sint.Z (nnv + W64 1073741824) ≤ sint.Z sl.len := by
    rw [hnnz, hmx, hslz]; exact ⟨hs1, hs2, hs4⟩
  ihave ⟨Hs0, Hs1, Hs2⟩ := (ownSlice_slice nnv (nnv + W64 1073741824) sl dqs data hsb').1 $$ Hsl
  wp_apply wp_bytes_to_string _ _ dqs $$ Hs1 as Hs1
  ihave Hsl := (ownSlice_slice nnv (nnv + W64 1073741824) sl dqs data hsb').2 $$ [Hs0 Hs1 Hs2]
  · iframe
  have hc : 0 < (subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data).length ∧
      (subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data).length ≤
        data.length - nnv.toNat ∧
      ((subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data).length =
        data.length - nnv.toNat ∨
       (subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data).length = 1073741824) ∧
      (subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data).length ≤ 1073741824 := by
    have e : sint.nat (nnv + W64 1073741824) = nnv.toNat + 1073741824 := by
      show (sint.Z _).toNat = _; exact tw_toNat_int _ _ hmx
    simp only [subslice, List.length_drop, List.length_take, hnnn, e]
    rw [tw_lenBig _ _ hA]
    exact ⟨by decide, Nat.le_of_lt hA, Or.inr rfl, Nat.le_refl _⟩
  have hcp : subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data <+:
      data.drop nnv.toNat := by
    simp only [subslice, hnnn]; rw [List.drop_take]; exact List.take_prefix _ _
  clear hmx hs1 hs2 hs3 hs4 hsb hsb'
  generalize subslice (sint.nat nnv) (sint.nat (nnv + W64 1073741824)) data = chunk at hc hcp ⊢
  rotate_left
  rw [decide_eq_false (show ¬ sint.Z (W64 1073741824) < sint.Z (sl.len - nnv) by
    rw [hsub, show sint.Z (W64 1073741824) = 1073741824 from rfl]; exact mt (tw_dec _ _).1 hA)]
  wp_auto
  obtain ⟨hs1, hs2, hs3⟩ := tw_sbSmall nnv.toNat data.length _ hcap hnn
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [hnnz, hslz]; exact ⟨hs1, hs2, hs3⟩
  rw [if_pos hsb]
  have hsb' : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.len := by
    rw [hnnz, hslz]; exact ⟨hs1, hs2, Int.le_refl _⟩
  ihave ⟨Hs0, Hs1, Hs2⟩ := (ownSlice_slice nnv sl.len sl dqs data hsb').1 $$ Hsl
  wp_apply wp_bytes_to_string _ _ dqs $$ Hs1 as Hs1
  ihave Hsl := (ownSlice_slice nnv sl.len sl dqs data hsb').2 $$ [Hs0 Hs1 Hs2]
  · iframe
  have hc : 0 < (subslice (sint.nat nnv) (sint.nat sl.len) data).length ∧
      (subslice (sint.nat nnv) (sint.nat sl.len) data).length ≤ data.length - nnv.toNat ∧
      ((subslice (sint.nat nnv) (sint.nat sl.len) data).length = data.length - nnv.toNat ∨
       (subslice (sint.nat nnv) (sint.nat sl.len) data).length = 1073741824) ∧
      (subslice (sint.nat nnv) (sint.nat sl.len) data).length ≤ 1073741824 := by
    have e : sint.nat sl.len = data.length := by
      show (sint.Z _).toNat = _; rw [hslz]; exact Int.toNat_natCast _
    simp only [subslice, List.length_drop, List.length_take, hnnn, e]
    rw [tw_lenSmall _ _ hA]
    exact ⟨Nat.sub_pos_of_lt hnn, Nat.le_refl _, Or.inl rfl, Nat.le_of_not_lt hA⟩
  have hcp : subslice (sint.nat nnv) (sint.nat sl.len) data <+: data.drop nnv.toNat := by
    simp only [subslice, hnnn]; rw [List.drop_take]; exact List.take_prefix _ _
  clear hs1 hs2 hs3 hsb hsb'
  generalize subslice (sint.nat nnv) (sint.nat sl.len) data = chunk at hc hcp ⊢
  all_goals
    obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
    have hcne : chunk ≠ [] := List.ne_nil_of_length_pos hc0
    obtain ⟨hoffv, hoffv'⟩ := tw_offAdd off nnv (by omega)
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
    clear htm hsz hS' hin' hfr
    rw [hoffv] at hcand hm2' ⊢
    obtain ⟨hx1, hx2, hx3⟩ := tw_max wr (off.toNat + nnv.toNat + k)
    generalize max wr (off.toNat + nnv.toNat + k) = w' at hx1 hx2 hx3 ⊢
    try wp_auto
    by_cases he4 : e = W64 4
    · -- `EINTR`: the attempt again, from `nn`
      rw [decide_eq_true he4]
      wp_pure
      obtain ⟨i1, i2, i3, i4⟩ := tw_eintr _ _ _ _ _ _ _ hwa hwb hwc hc1 hc3 hk hx1 hx2 hx3 hc0
      have hre' : off.toNat + nnv.toNat = w' ∨
          ∃ q ∈ ((finBytes m' bs' (off.toNat + nnv.toNat) chunk k nst zs).getD
            (off.toNat + nnv.toNat) (0, [])).2, 0 < q.2 :=
        Or.inr (hcand _ (Nat.le_refl _) i4)
      iapply IH $$ %(pwPost m' (off.toNat + nnv.toNat) chunk.length k)
        %(finBytes m' bs' (off.toNat + nnv.toNat) chunk k nst zs) %nnv %w'
        %hnn %i1 %i2 %i3 %hre' %hm2' Hm Hb Hv Hk Hosfd Hsl Hfd HΦ
    · rw [decide_eq_false he4]
      wp_auto
      have hnk := tw_addk nnv k (by omega)
      by_cases hfull : nnv.toNat + k = data.length
      · rw [decide_eq_true (show nnv + W64 (k : Int) = sl.len by
          rw [hsln]; exact (tw_full_iff nnv k data.length (by omega) hL63).2 hfull)]
        wp_auto
        by_cases he0 : e = W64 0
        · rw [decide_eq_true he0]
          wp_auto
          have ew := tw_full _ _ _ _ _ _ hwb hfull hx1 hx2 hx3
          subst ew
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
      · rw [decide_eq_false (show ¬ nnv + W64 (k : Int) = sl.len by
          rw [hsln]; exact mt (tw_full_iff nnv k data.length (by omega) hL63).1 hfull)]
        wp_auto
        by_cases he0 : e = W64 0
        · -- a short write: the next attempt from `nn + k`
          rw [decide_eq_true he0]
          simp only [Bool.not_true]
          wp_pure
          obtain ⟨s1, s2, s3, s4, s5⟩ :=
            tw_short _ _ _ _ _ _ _ hnn hwa hwb hwc hc1 hc2 hk hfull hx1 hx2 hx3
          have hre' : off.toNat + (nnv + W64 (k : Int)).toNat = w' ∨
              ∃ q ∈ ((finBytes m' bs' (off.toNat + nnv.toNat) chunk k nst zs).getD
                (off.toNat + (nnv + W64 (k : Int)).toNat) (0, [])).2, 0 < q.2 := by
            rw [hnk]
            rcases s5 with h | ⟨h1, h2⟩
            · exact Or.inl h
            · right; rw [← Nat.add_assoc]; exact hcand _ h1 h2
          iapply IH $$ %(pwPost m' (off.toNat + nnv.toNat) chunk.length k)
            %(finBytes m' bs' (off.toNat + nnv.toNat) chunk k nst zs) %(nnv + W64 (k : Int)) %w'
            %(by rw [hnk]; exact s1) %(by rw [hnk]; exact s2) %s3 %(by rw [hnk]; exact s4)
            %hre' %hm2' Hm Hb Hv Hk Hosfd Hsl Hfd HΦ
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

/-- **`(*os.File).Write` on the tail** (`Off.lean`'s `os.File.Write.wp_long` with
`wp_tailWriteAt` for its `WriteAt`): a non-empty `b` at the offset `o`, the record's write position
`wr`; on success `len(b)`, the offset and the write position past `b`; on an error the handle's
parts of the tail are lost. -/
theorem wp_tailWrite [os.file.FieldAssumptions] (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (data : List w8) (dqs : DFrac) (o : w64) (wr : Nat) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (bs : List ByteG) (hfd : 0 ≤ fd.toInt) (hwr : d.writable = true) (h0 : 0 ≤ o.toInt)
    (hwrn : o.toNat = wr) (hn : 0 < data.length) (hin : wr + data.length ≤ m.size)
    (hmax : o.toInt + data.length < 2 ^ 62)
    (hS : data <+: (tailStream Mr H md cuts).drop wr) (hm : TailMeta m bs) :
    {{ walAreaOk walCodec Mr R jr r ∗ os.ownFile f fd name dqf ∗ os.ownOff f o ∗
        sl ↦*{dqs} data ∗ osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Write")) (Val #sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗
        ((⌜err = interface.nil ∧ n = W64 data.length⌝ ∗ os.ownOff f (o + W64 data.length) ∗
            osFd fd dq d ∗ walTailKey (W := W) dir γ ∗
            tailVar (W := W) γ ((H, md, cuts, wr + data.length, d.ino, none) : TailG) ∗
            ∃ (m' : OsMeta) (bs' : List ByteG), osMeta d.ino (DFrac.own (1 : Qp).half) m' ∗
              osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs' ∗ ⌜TailMeta m' bs' ∧ m'.size = m.size⌝) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  subst hwrn
  unfold os.ownOff
  wp_start as ⟨#Harea, Hf, ⟨%inner, #Hfi, Ho⟩, Hsl, Hosfd, Hk, Hv, Hm, Hbs⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hfi
  iStructNamed Hf2
  icases ownSlice_len sl _ data $$ Hsl with %Hlen
  iunfold os.ownFile at Hf
  icases Hf with ⟨%inner0, #Hf0, Hfd0, #Hn0⟩
  icombine Hfi Hf0 gives %hin0
  cases hin0
  wp_auto
  have hsl : sl.len = W64 data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  rw [decide_eq_false (show ¬ sint.Z fd < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd)]
  wp_auto
  rw [decide_eq_false (show ¬ sl.len = W64 0 by
    rw [hsl]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofInt] at this; omega)]
  wp_auto
  ihave Hf : os.ownFile f fd name dqf $$ [Hfd0]
  · unfold os.ownFile; iexists inner; iframe; isplitl [] <;> iassumption
  rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega)]
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl, hsl]
  try wp_auto
  have hsum : sint.Z (o + W64 (data.length : Int)) = o.toInt + data.length := by
    simp only [sint.Z]; word
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (o + W64 (data.length : Int)) by
    rw [hsum, show sint.Z (W64 0x4000000000000000) = 2 ^ 62 from rfl]; omega)]
  wp_auto
  have h63 : o.toNat + data.length < 2 ^ 63 := by
    have := BitVec.toInt_eq_toNat_cond o; split at this <;> omega
  wp_apply wp_tailWriteAt Mr R jr r dir γ H md cuts f fd name dqf sl data dqs o dq d m bs hwr h0 hn
      hin h63 hS hm
    $$ [Harea Hf Hsl Hosfd Hk Hv Hm Hbs] as %n %err ⟨Hf, Hsl, Hres⟩
  · iframe; iexact Harea
  cases err with
  | nil =>
    icases Hres with (⟨%hres, Hosfd, Hk, Hv, %m', %bs', Hm, Hbs, %hmb⟩ | %herr)
    rotate_left
    · exact absurd rfl herr
    obtain ⟨-, rfl⟩ := hres
    wp_auto
    iapply HΦ
    iframe Hf Hsl
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, hsl⟩
    iframe Hosfd Hk Hv
    isplitl [Ho]
    · iexists inner; iframe; iassumption
    iexists m', bs'
    iframe Hm Hbs
    ipureintro; exact hmb
  | ok ie =>
    wp_auto
    wp_apply wp_ArbitraryInt as %x _
    iapply HΦ
    iframe Hf Hsl
    iright
    ipureintro; intro h; cases h

/-- **The tail's writer** (see the file header): the tail file `f` of inode `i`, written from the
encoder's start `o0`, is a guarded stream of its intended bytes (`tailOk`); a failed write leaves
nothing the program keeps (the invariant holds what it wrote; the handle is lost). -/
theorem wal.tailWriter [os.file.FieldAssumptions] (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      io.writerStreamP (wal.fileWi f) (tailOk Mr H md cuts o0 sz)
        (walTailW (W := W) f fd name dir γ i H md cuts o0 sz) (fun _ _ => iprop(True)) := by
  iintro #Harea
  unfold io.writerStreamP
  iintro !> %out %p %xs %dqp %hok
  iintro !> %Φ ⟨HW, Hp⟩ HΦ
  iunfold walTailW at HW
  icases HW with ⟨Hf, ⟨%rd, Hfd⟩, Ho, Hk, %m, %bs, Hm, Hb, %hmb, Hv⟩
  obtain ⟨hsz, hm, hsz62, hfd0⟩ := hmb
  obtain ⟨hpre, hle⟩ := hok
  simp only [List.length_append] at hle
  by_cases hx : xs = []
  · subst hx
    wp_apply os.File.Write.wp_empty f fd name _ p dqp _ hfd0 $$ [Hf Ho Hp] as %n %err ⟨%hn, Hf, Ho, Hp⟩
    · iframe
    iapply HΦ
    iframe Hp
    rcases err with ei | _
    · iright
      isplitr
      · ipureintro; intro h; cases h
      ipureintro; trivial
    · ileft
      isplitr
      · ipureintro; exact ⟨rfl, by rw [hn]; rfl⟩
      iunfold walTailW
      simp only []
      rw [List.append_nil]
      iframe Hf Ho Hk
      isplitl [Hfd]
      · iexists rd; iexact Hfd
      iexists m, bs
      iframe Hm Hb Hv
      ipureintro; exact ⟨hsz, hm, hsz62, hfd0⟩
  have hn : 0 < xs.length := List.length_pos_iff.2 hx
  have hoN := os.W64_nat_toNat (o0 + out.length) (by omega)
  have hoI := os.W64_nat_toInt (o0 + out.length) (by omega)
  have hS : xs <+: (tailStream Mr H md cuts).drop (o0 + out.length) := by
    obtain ⟨t, ht⟩ := hpre
    have e1 : ((tailStream Mr H md cuts).drop o0).drop out.length =
        (tailStream Mr H md cuts).drop (o0 + out.length) := by
      rw [List.drop_drop]; try (congr 1; omega)
    rw [← e1, ← ht, List.append_assoc, List.drop_left]
    exact List.prefix_append _ _
  wp_apply (wp_tailWrite Mr R jr r dir γ H md cuts f fd name (DFrac.own 1) p xs dqp
      (W64 ((o0 + out.length : Nat) : Int)) (o0 + out.length) (DFrac.own 1) ⟨i, rd, true⟩ m bs hfd0
      rfl (by rw [hoI]; omega) hoN hn (by omega) (by rw [hoI]; omega) hS hm)
    $$ [Harea Hf Ho Hp Hfd Hk Hv Hm Hb] as %n %err ⟨Hf, Hp, Hres⟩
  · unfold tailVar; iframe; iexact Harea
  iapply HΦ
  iframe Hp
  icases Hres with (⟨%hres, Ho, Hfd, Hk, Hv, %m', %bs', Hm, Hb, %hmb⟩ | %herr)
  · ileft
    isplitr
    · ipureintro
      refine ⟨hres.1, ?_⟩
      rw [hres.2]; simp only [sint.Z]; rw [os.W64_nat_toInt xs.length (by omega)]
    iunfold walTailW
    simp only []
    iframe Hf Hk
    isplitl [Hfd]
    · iexists rd; iexact Hfd
    isplitl [Ho]
    · rw [show W64 ((o0 + out.length : Nat) : Int) + W64 (xs.length : Int) =
          W64 ((o0 : Int) + ((out ++ xs).length : Int)) by
        rw [List.length_append]; simp only [W64]; push_cast; rw [← BitVec.ofInt_add]; congr 1; omega]
      iexact Ho
    iexists m', bs'
    iframe Hm Hb
    isplitr
    · ipureintro; exact ⟨by rw [hmb.2, hsz], hmb.1, hsz62, hfd0⟩
    rw [List.length_append, ← Nat.add_assoc]
    unfold tailVar
    try dsimp only
    iexact Hv
  · iright
    isplitr
    · ipureintro; exact herr
    ipureintro; trivial

end tail

end WalFs
end EtcdGrove
end Perennial

end
