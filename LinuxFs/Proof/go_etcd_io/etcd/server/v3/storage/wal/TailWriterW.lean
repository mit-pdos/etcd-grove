/- Lean-first (no Rocq counterpart).

# The tail's writer past the preallocated size (W6 of `notes/wal-fsext-plan.md`; W6 log, twenty-fifth session)

`TailWriter.lean`'s steps for any write from inside the file (a `Save` crossing `SegmentSizeBytes`, and the
writes in a resize window): the tail exact or in a window before and after.

* **the start** (`wp_tailPWriteStartW`): as `wp_tailPWriteStart`, the layout's tail `segAnnW` (the candidates
  announced past the size, `wrMeta`), its static relation `walAbsD_announceW`;
* **the finish** (`wp_tailPWriteFinishW`): `wp_osPWriteFinishK true` (the candidates past the new size
  kept), the layout's tail `segFinW`, its static relation `walAbsD_finishW`.

Both keep the crash condition by `crashOkA_tailAny` (`tailCrashStep_any`), through `walInvBody_tailW`
(`walsOk_tailA`, `dirKeysOk_tailA`). Between the attempts of a `WriteAt` the program's tail facts are
`TailMetaL` (`TailMetaPw.lean`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriter
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFinW
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAccW
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzWals

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **Any tail step whose new static relation is proved is a crash step** (`crashOkA_tailAny`). -/
theorem tailCrashStep_any {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents0 ents : Ents} {pre : List SegG} {g0 g : SegG} {wr' : Nat} {cl : List Claim} {n : Nat}
    (habs0 : WalAbsD C Mr d lay ents0) (habs : WalAbsD C Mr d (tailLay lay pre g wr') ents)
    (hZ : TailZeros lay) (hB : TailBound C Mr d lay) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino)
    (hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hzf : ∀ z, g.om.zf = some z → g.bs.length ≤ z) :
    TailCrashStep C Mr d lay pre g0 g wr' cl n := by
  intro alt halt hok
  have hnd' : ((tailLay lay pre g wr').segs.map (·.ino)).Nodup := by
    rw [hs] at hnd; simpa [tailLay, hino] using hnd
  exact crashOkA_tailAny hC habs0 habs hZ hB hnd' hs rfl hino rfl rfl rfl rfl rfl hzf0 hzf
    (fun la h g' hg' => by rw [hino]; exact halt la h g' hg') hok

/-- The announced tail's bytes, from the write in flight (`SegFl.Ok`). -/
theorem SegFl.Ok.getElem? {fl : SegFl} {g0 : SegG} (hok : fl.Ok g0) (b : Nat) :
    g0.bs[b]? = if fl.off ≤ b ∧ b < fl.off + fl.data.length then
      fl.bs[b]?.map (fun x => (x.1, x.2 ++ [(fl.data.getD (b - fl.off) 0, fl.n)])) else fl.bs[b]? := by
  have hok' := hok
  obtain ⟨hoff, -, hl, -⟩ := hok'
  rw [hok.eq_ann]; exact segAnnW_getElem? (g0 := ⟨g0.name, g0.ino, fl.m, fl.bs⟩) hoff hl

/-- **A finished write's range carries its candidate** (stamped positive), at each byte of the file
after it (any write from inside the file): a retry from a byte of the range starts past the synced
bytes. -/
theorem segFinW_candW {fl : SegFl} {g0 : SegG} {k : Nat} {zs : List Cands} (hok : fl.Ok g0)
    (hk : k ≤ fl.data.length) (b : Nat) (h1 : fl.off ≤ b) (h2 : b < fl.off + fl.data.length)
    (h3 : b < pwSize fl.m.size fl.off k) :
    (fl.data.getD (b - fl.off) 0, fl.n) ∈ ((segFinW fl g0 k zs).bs.getD b (0, [])).2 := by
  have hl := hok.2.2.1
  have hoff := hok.1
  rw [List.getD_eq_getElem?_getD, segFinW_getElem? hok hk]
  by_cases hr : fl.off ≤ b ∧ b < fl.off + k
  · rw [if_pos hr]
    by_cases hb : b < fl.m.size
    · rw [if_pos hb, hok.getElem?, if_pos ⟨h1, h2⟩, List.getElem?_eq_getElem (by omega)]
      simp
    · rw [if_neg hb]; simp
  · rw [if_neg hr]
    have hb : b < fl.m.size := by
      rcases Nat.lt_or_ge b fl.m.size with h | h
      · exact h
      · rcases pwSize_past hoff h h3 with h' | h'
        · exact absurd h' hr
        · exact h'.elim
    rw [hok.getElem?, if_pos ⟨h1, h2⟩, List.getElem?_eq_getElem (by omega)]
    simp

end pure

section tail
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The program's part of the tail `i` while the write `fl` is in flight on it** (any write from
inside the file): `walTailFl` with the halves of the bytes around the range below the size
(`cfLo`, `cfHi`: a write past the size has none after it). -/
def walTailFlW (dir : GoString) (γ : GName) (tg : TailG) (i : Ino) (fl : SegFl) : IProp GF :=
  iprop(walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
    osBytes i 0 (DFrac.own (1 : Qp).half) (fl.bs.take (cfLo fl.m fl.off)) ∗
    osBytes i (cfHi fl.m fl.off fl.data.length) (DFrac.own (1 : Qp).half)
      (fl.bs.drop (cfHi fl.m fl.off fl.data.length)))

/-- **The first step of a `pwrite` on the tail, from inside the file** (see the file header): as
`wp_tailPWriteStart`, the write possibly past the size, the tail exact or in a window; the program's tail
facts between the attempts of a `WriteAt` ending at `E` (`TailMetaL`). -/
theorem wp_tailPWriteStartW (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd) (E : Nat)
    (Φ : val → IProp GF)
    (hwr : d.writable = true) (hoff0 : 0 ≤ off.toInt) (hoffw : off.toNat ≤ wr)
    (hre : off.toNat = wr ∨ ∃ q ∈ (bs.getD off.toNat (0, [])).2, 0 < q.2) (hd : data ≠ [])
    (hin : off.toNat ≤ m.size)
    (hS : data <+: (tailStream Mr H md cuts).drop off.toNat) (hm : TailMetaL m bs E) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ t : Nat, ∀ n : Nat, ⌜0 < n ∧ 0 < off.toNat⌝ -∗ osFd fd dq d -∗
        walTailFlW dir γ (H, md, cuts, wr, d.ino, some ⟨t, off.toNat, data, n, m, bs, none⟩) d.ino
          ⟨t, off.toNat, data, n, m, bs, none⟩ -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  iintro #Harea Hfd Hk Hv Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  ihave Hk := (show walTailKey (W := W) dir γ ⊢ walTailKeyL (W := W) dir γ none by
    rw [walTailKeyL_none]) $$ Hk
  icases walInvBody_tailW walCodec Mr R jr r s dir γ none _ m $$ Hb Hk Hv [Hm1] with
    ⟨%Ls, %cl, %nn, %F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', Hm1, Hclose⟩
  · dsimp only [tailHeld]; iexact Hm1
  dsimp only [tailHeld]
  ihave Hk := (show walTailKeyL (W := W) dir γ none ⊢ walTailKey (W := W) dir γ by
    rw [walTailKeyL_none]) $$ Hk
  obtain ⟨hdw, hl, hs, htg, hW, ⟨ents, habs⟩, hcut0, hZ, hB, -⟩ := hp
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
    obtain ⟨hso', -, -, hwb, -⟩ := habs.lastWin g0 hg0
    rcases hre with he | ⟨q, hq, hq0⟩
    · omega
    · refine Nat.le_of_not_lt fun hlt => ?_
      have hbl : off.toNat < g0.bs.length := by omega
      have hy : g0.bs[off.toNat]? = some (g0.bs.getD off.toNat (0, [])) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]; rfl
      rcases habs.low g0 hg0 off.toNat _ hy (by omega) with ⟨-, hold⟩ | ⟨-, h2, -⟩
      · rw [decide_eq_true hlt] at hold
        have := hold.synced_stamps q hq
        omega
      · omega
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (osBytes_split3 d.ino g0.om g0.bs off.toNat data.length _ hlen).1 $$ Hb1 with ⟨Hp1, Hr1, Hs1⟩
  icases (osBytes_split3 d.ino g0.om g0.bs off.toNat data.length _ hlen).1 $$ Hb2 with ⟨Hp2, Hr2, Hs2⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  have hlo : cfLo g0.om off.toNat = off.toNat := by unfold cfLo; omega
  ihave Hrg := (show osBytes d.ino (cfLo g0.om off.toNat) (DFrac.own 1)
      (cfRange g0.om g0.bs off.toNat data.length) ⊢ osBytes d.ino off.toNat
      (DFrac.own 1) (cfRange g0.om g0.bs off.toNat data.length) by rw [hlo]) $$ Hrg
  have hrl : (cfRange g0.om g0.bs off.toNat data.length).length =
      min (off.toNat + data.length) g0.om.size - off.toNat := by
    unfold cfRange; rw [hlo]; simp only [List.length_take, List.length_drop, cfHi]; omega
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osPWriteStart fd off data dq d g0.om (cfRange g0.om g0.bs off.toNat data.length)
    osN_sub_nwal hwr hoff0 hin hd hrl $$ Hos Hfd Hm Hrg []
  · rw [hm.2.1]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
  iintro %t %n %hfr Hfd Htok
  have hn : 0 < n := hfr.2.2
  let fl : SegFl := ⟨t, off.toNat, data, n, g0.om, g0.bs, none⟩
  let g' := segAnnW g0 off.toNat data n
  let F' : GMap Ino SegFl := <[g0.ino := fl]> F
  have hpre' : data <+: (segStream walCodec Mr dw lay.cuts lay.cuts.length).drop off.toNat := by
    rw [← hcuts]; rw [hH, hmd] at hS; exact hS
  have hoff1 : 0 < off.toNat := by have h1 := walAbsD_so_pos habs; omega
  have habs' : ∀ ents', WalAbsD walCodec Mr dw lay ents' →
      WalAbsD walCodec Mr dw (tailLay lay pre g' lay.wr) ents' := fun ents' h =>
    walAbsD_announceW h hs hso hin hpre' hn hZ (fun b hb => hm.2.2.1.pc_isSome hb) hm.2.2.2.2.2
  have hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z := fun z hz => by
    rw [hlen]; exact hm.2.2.1.ge z hz
  have hzf' : ∀ z, g'.om.zf = some z → g'.bs.length ≤ z := by
    intro z hz
    rw [show g'.bs.length = g0.bs.length from segAnnW_length hin hlen]
    simp only [g', segAnnW_om, wrMeta_zf, cfMeta, announce_zf, Option.map_eq_some_iff] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    have := hzf0 z0 hz0
    split <;> omega
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  have hstep : TailCrashStep walCodec Mr dw lay pre g0 g' lay.wr cl nn :=
    tailCrashStep_any walCodec_ok habs (habs' ents habs) hZ hB hnd hs rfl hzf0 hzf'
  imod tailVar_update γ _ _ (tailG dw (tailLay lay pre g' lay.wr) g'.ino (F' !! g'.ino)) $$ Hv Hv'
    with ⟨Hv, Hv'⟩
  ihave Hb := Hclose $$ %g' %lay.wr %F' [] [Htok Hp2 Hs2] Hv'
  · ipureintro
    exact ⟨hino.symm, rfl, fun i hi => GMap.lookup_insert_ne _ _ (fun h => hi (h.symm.trans hino.symm)),
      Or.inl rfl,
      walsOk_tailA hW hdw hl hs rfl (by simp [g', segAnnW_om, hcut0]) habs' hstep,
      fun K c h => dirKeysOk_tailA hdw hl hstep h⟩
  · rw [show F' !! g'.ino = some fl from GMap.lookup_insert _ _ _]
    dsimp only [fl]
    rw [show g'.ino = d.ino from hino.symm]
    iframe Htok Hp2 Hs2
    ipureintro
    exact segAnnW_ok hin hd hlen hcut0 hoff1
  imod Hid
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  have e : tailG dw (tailLay lay pre g' lay.wr) g'.ino (F' !! g'.ino) =
      ((H, md, cuts, wr, d.ino, some fl) : TailG) := by
    rw [show F' !! g'.ino = some fl from GMap.lookup_insert _ _ _]
    simp only [tailG, tailLay, g', segAnnW, segAnn]
    rw [hH, hmd, hcuts, hwrl, hino]
  rw [e]
  iapply HΦ $$ %t %n %(⟨hn, hoff1⟩ : 0 < n ∧ 0 < off.toNat) Hfd
  unfold walTailFlW
  iframe Hk Hv Hp1 Hs1

/-- **The second step of a `pwrite` on the tail, from inside the file** (see the file header): the `k`
bytes written (`wp_osPWriteFinishK true`), the write position past them (or where it was), the file idle;
the size `pwSize` (below `maxBytes` if it grew: `PwCut`); the program's tail facts `TailMetaL`, and
`TailMetaW` after a write of all of its data up to `E`; the write's range carries its candidate on every
byte the file has after it. -/
theorem wp_tailPWriteFinishW (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat) (i : Ino)
    (fl : SegFl) (E : Nat) (Φ : val → IProp GF) (hrz : fl.rz = none) (hn : 0 < fl.n)
    (hm : TailMetaL fl.m fl.bs E) (hoffl : fl.off ≤ fl.m.size) (hwrf : fl.off ≤ wr)
    (hE : fl.off + fl.data.length ≤ E) (hS : fl.data <+: (tailStream Mr H md cuts).drop fl.off) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      walTailFlW dir γ (H, md, cuts, wr, i, some fl) i fl -∗
      (∀ (k : Nat) (e : w64) (zs : List Cands),
        ⌜k ≤ fl.data.length ∧ ((k = fl.data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          (k = 0 ∨ fl.off + k ≤ maxBytes) ∧
          TailMetaL (pwPostK true fl.m fl.off fl.data k fl.n)
            (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) E ∧
          (k = fl.data.length → fl.off + fl.data.length = E →
            TailMetaW (pwPostK true fl.m fl.off fl.data k fl.n)
              (finBytes fl.m fl.bs fl.off fl.data k fl.n zs)) ∧
          (pwPostK true fl.m fl.off fl.data k fl.n).size = pwSize fl.m.size fl.off k ∧
          (∀ b, fl.off ≤ b → b < fl.off + fl.data.length → b < pwSize fl.m.size fl.off k →
            (fl.data.getD (b - fl.off) 0, fl.n) ∈
              ((finBytes fl.m fl.bs fl.off fl.data k fl.n zs).getD b (0, [])).2)⌝ -∗
        walTailKey (W := W) dir γ -∗
        tailVar (W := W) γ ((H, md, cuts, max wr (fl.off + k), i, none) : TailG) -∗
        osMeta i (DFrac.own (1 : Qp).half) (pwPostK true fl.m fl.off fl.data k fl.n) -∗
        osBytes i 0 (DFrac.own (1 : Qp).half) (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV fl.t))) {{ Φ }} := by
  iintro #Harea Hfl HΦ
  unfold walTailFlW
  icases Hfl with ⟨Hk, Hv, Hp1, Hs1⟩
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  ihave Hk := (show walTailKey (W := W) dir γ ⊢ walTailKeyL (W := W) dir γ none by
    rw [walTailKeyL_none]) $$ Hk
  icases walInvBody_tailW walCodec Mr R jr r s dir γ none _ fl.m $$ Hb Hk Hv [] with
    ⟨%Ls, %cl, %nn, %F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hv', -, Hclose⟩
  · dsimp only [tailHeld]; iempintro
  ihave Hk := (show walTailKeyL (W := W) dir γ none ⊢ walTailKey (W := W) dir γ by
    rw [walTailKeyL_none]) $$ Hk
  obtain ⟨hdw, hl, hs, htg, hW, ⟨ents, habs⟩, hcut0, hZ, hB, -⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
  unfold segResF
  rw [← hF]
  dsimp only
  rw [hrz]
  dsimp only
  icases Hseg with ⟨Htok, Hp2, Hs2, %hok⟩
  have hok' := hok
  obtain ⟨-, hd, hl', hmc, hom, -, -⟩ := hok'
  subst hino
  unfold pwTok
  icases Htok with ⟨Htok, %hgap⟩
  obtain ⟨hgap, -, -⟩ := hgap
  have hlo : cfLo fl.m fl.off = fl.off := by unfold cfLo; omega
  have hrl : (cfRange fl.m fl.bs fl.off fl.data.length).length =
      min (fl.off + fl.data.length) fl.m.size - fl.off := by
    unfold cfRange; rw [hlo]; simp only [List.length_take, List.length_drop, cfHi]; omega
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osPWriteFinishK true fl.t g0.ino fl.off fl.data fl.m (cfRange fl.m fl.bs fl.off fl.data.length)
    fl.n osN_sub_nwal $$ Hos [Htok]
  · unfold pwTok; iframe; ipureintro
    exact ⟨hgap, hd, hrl⟩
  iintro %k %e %zs %hke %hzc %hcut Hm Hrg -
  obtain ⟨hk, hke2, hzl, -⟩ := hke
  have hdl : 0 < fl.data.length := List.length_pos_iff.2 hd
  have hps := pwSize_ge_off (k := k) hoffl
  have hps2 := pwSize_le_max' (sz := fl.m.size) (off := fl.off) hk
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  have hl1 : 0 + (fl.bs.take (cfLo fl.m fl.off)).length = fl.off := by
    simp only [List.length_take]; rw [hlo]; omega
  have hl2 : fl.off + (pwBytes fl.m.size fl.off fl.data k fl.n
      (cfRange fl.m fl.bs fl.off fl.data.length) zs).length =
      cfHi fl.m fl.off fl.data.length ∨ fl.bs.drop (cfHi fl.m fl.off fl.data.length) = [] := by
    by_cases hin : fl.off + fl.data.length ≤ fl.m.size
    · left; rw [pwBytes_length]; unfold cfHi; unfold pwSize; split <;> omega
    · right; apply List.drop_eq_nil_of_le; unfold cfHi; omega
  ihave Hb1 := osBytes_join3 g0.ino 0 fl.off (cfHi fl.m fl.off fl.data.length) _ _ _ _ hl1 hl2
    $$ [Hp1 Hr1 Hs1]
  · iframe
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
  let g' := segFinW fl g0 k zs
  let F' : GMap Ino SegFl := GMap.delete g0.ino F
  imod tailVar_update γ _ _ (tailG dw (tailLay lay pre g' (max lay.wr (fl.off + k))) g'.ino
    (F' !! g'.ino)) $$ Hv Hv' with ⟨Hv, Hv'⟩
  have hpre' : fl.data <+: (segStream walCodec Mr dw lay.cuts lay.cuts.length).drop fl.off := by
    rw [← hcuts]; rw [hH, hmd] at hS; exact hS
  have hmL := hm.fin (n := fl.n) (zs := zs) hoffl hdl hE hk
  have habs' : ∀ ents', WalAbsD walCodec Mr dw lay ents' →
      WalAbsD walCodec Mr dw (tailLay lay pre g' (max lay.wr (fl.off + k))) ents' := fun ents' h =>
    walAbsD_finishW h hs hok (by omega) hk hn hpre' hzl hzc
  have hgl0 : g0.bs.length = fl.m.size := by
    have := (habs.metas g0 (by rw [hs]; simp)).1
    rw [← this, hom, wrMeta_size]
  have hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z := fun z hz => by
    have := hmL.1.2.2.1.ge z (by rw [hom] at hz; exact hz)
    rw [pwPostK_size] at this; omega
  have hzf' : ∀ z, g'.om.zf = some z → g'.bs.length ≤ z := fun z hz => by
    rw [show g'.bs.length = (pwPostK true fl.m fl.off fl.data k fl.n).size from hmL.1.1]
    exact hmL.1.2.2.1.ge z hz
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  have hstep : TailCrashStep walCodec Mr dw lay pre g0 g' (max lay.wr (fl.off + k)) cl nn :=
    tailCrashStep_any walCodec_ok habs (habs' ents habs) hZ hB hnd hs rfl hzf0 hzf'
  ihave Hb := Hclose $$ %g' %(max lay.wr (fl.off + k)) %F' [] [Hm2 Hb2] Hv'
  · ipureintro
    exact ⟨rfl, rfl, fun i' hi => GMap.lookup_delete_ne _ (Ne.symm hi), Or.inr hZ,
      walsOk_tailA hW hdw hl hs rfl (by simp only [g', segFinW]; rw [pwPostK_cut]; exact hmc) habs' hstep,
      fun K c h => dirKeysOk_tailA hdw hl hstep h⟩
  · rw [show F' !! g'.ino = none from GMap.lookup_delete_eq _ _]
    dsimp only
    unfold segRes
    dsimp only [g', segFinW]
    iframe Hm2 Hb2
  imod Hid
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  have hpost : k ≤ fl.data.length ∧ ((k = fl.data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
      (k = 0 ∨ fl.off + k ≤ maxBytes) ∧
      TailMetaL (pwPostK true fl.m fl.off fl.data k fl.n)
        (finBytes fl.m fl.bs fl.off fl.data k fl.n zs) E ∧
      (k = fl.data.length → fl.off + fl.data.length = E →
        TailMetaW (pwPostK true fl.m fl.off fl.data k fl.n)
          (finBytes fl.m fl.bs fl.off fl.data k fl.n zs)) ∧
      (pwPostK true fl.m fl.off fl.data k fl.n).size = pwSize fl.m.size fl.off k ∧
      (∀ b, fl.off ≤ b → b < fl.off + fl.data.length → b < pwSize fl.m.size fl.off k →
        (fl.data.getD (b - fl.off) 0, fl.n) ∈
          ((finBytes fl.m fl.bs fl.off fl.data k fl.n zs).getD b (0, [])).2) :=
    ⟨hk, hke2, hcut.2, hmL.1, hmL.2, pwPostK_size _ _ _ _ _,
      fun b h1 h2 h3 => segFinW_candW (zs := zs) hok hk b h1 h2 h3⟩
  have htv : tailG dw (tailLay lay pre g' (max lay.wr (fl.off + k))) g'.ino (F' !! g'.ino) =
      ((H, md, cuts, max wr (fl.off + k), g0.ino, none) : TailG) := by
    rw [show F' !! g'.ino = none from GMap.lookup_delete_eq _ _]
    simp only [tailG, tailLay, g', segFinW]
    rw [hH, hmd, hcuts, hwrl]
  rw [htv]
  iapply HΦ $$ %k %e %zs %hpost Hk Hv Hm1
  iexact Hb1

end tail

end WalFs
end EtcdGrove
end Perennial

end
