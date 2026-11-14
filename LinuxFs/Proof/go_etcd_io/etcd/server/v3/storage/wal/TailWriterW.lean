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

/-! The arithmetic of `wp_tailWriteAtW`'s loop, as small lemmas over `Nat` (as `TailWriter.lean`'s
`tw_*`: no `omega` in the loop's context). The loop keeps the size at `max m.size wr` (a write that
lands bytes moves both to its end; one that lands none neither) and `wr` below `max off maxBytes`. -/

theorem twW_init (s o : Nat) (h : o ≤ s) : s = max s o := by omega

theorem twW_in (o wr S s0 : Nat) (h : o ≤ wr) (hS : S = max s0 wr) : o ≤ S := by omega

theorem twW_E (o a L c : Nat) (hc : c ≤ L - a) (ha : a < L) : o + a + c ≤ o + L := by omega

theorem twW_step (s0 wr o k S M o0 : Nat) (hS : S = max s0 wr) (ho : o ≤ wr) (hwM : wr ≤ max o0 M)
    (hkM : k = 0 ∨ o + k ≤ M) :
    pwSize S o k = max s0 (max wr (o + k)) ∧ max wr (o + k) ≤ max o0 M ∧ wr ≤ pwSize S o k := by
  subst hS; unfold pwSize; split <;> omega

theorem twW_cand (o wr S s0 k : Nat) (ho : o ≤ wr) (hS : S = max s0 wr) :
    o = max wr (o + k) ∨ o < pwSize S o k := by
  subst hS; unfold pwSize; split <;> omega

theorem twW_cand2 (b wr S' w' : Nat) (hwr : wr ≤ S') (hb : b ≤ w') (hw3 : w' = wr ∨ w' = b) :
    b = w' ∨ b < S' := by omega

theorem twW_full (o a L k c : Nat) (hfk : a + k = L) (hk : k ≤ c) (hc : c ≤ L - a) :
    k = c ∧ o + a + c = o + L := by omega

theorem twW_end (s0 o0 M E : Nat) (h : E ≤ max o0 M) (ho : o0 ≤ s0) : E ≤ max s0 M := by omega

/-- The writer's state after a write past `max sz (o0 + |out|)`: its size, its bounds. -/
theorem twW_post (sz a b S S' M : Nat) (hS : S = max sz a) (hS' : S' = max S (a + b))
    (h62 : S < 2 ^ 62) (hab : a + b < 2 ^ 62) (hE : a + b ≤ max S M) (ha : a ≤ max sz M) :
    S' = max sz (a + b) ∧ max sz (a + b) < 2 ^ 62 ∧ a + b ≤ max sz M := by omega

/-- **The guard of the tail's writer past the size** (`wal.tailWriterW`): `tailOk` without its size
clause; the stream's end below the model's `Write` bound (`os.model.offMax`, 2^62: a write reaching it
is not modelled). -/
def tailOkW (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 : Nat)
    (ys : List w8) : Prop :=
  ys <+: (tailStream Mr H md cuts).drop o0 ∧ o0 + ys.length < 2 ^ 62

theorem tailOkW_prefix {Mr : WalMarshal} {H : List (WalOpG WalEnt)} {md : List w8}
    {cuts : List Nat} {o0 : Nat} {xs ys : List w8} (h : xs <+: ys)
    (hy : tailOkW Mr H md cuts o0 ys) : tailOkW Mr H md cuts o0 xs :=
  ⟨h.trans hy.1, Nat.lt_of_le_of_lt (Nat.add_le_add_left h.length_le _) hy.2⟩

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

/-- **`(*os.File).WriteAt` on the tail, from inside the file** (`wp_tailWriteAt` over
`wp_tailPWriteStartW`/`wp_tailPWriteFinishW`; the model's loop, `TrustedCode/os.lean`'s
`File.WriteAt.impl`): its attempts are the two steps above, in chunks of at most `maxRW`, each from
where the bytes written so far end (after a short write) or from where the last attempt started
(after `EINTR`: the bytes it wrote are rewritten, the record's write position staying past them).
On success the record's write position is past `data`, the tail as the steps left it (`TailMetaW`, its
size grown to the write's end, below `maxBytes` if it grew, no window or its least crash size at most the
write position); on an error the handle's parts of the tail are lost (the invariant keeps the bytes as
written). -/
theorem wp_tailWriteAtW (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (bs : List ByteG)
    (hwr : d.writable = true) (hoff0 : 0 ≤ off.toInt) (hn : 0 < data.length)
    (hin : off.toNat ≤ m.size) (hbig : off.toNat + data.length < 2 ^ 63)
    (hS : data <+: (tailStream Mr H md cuts).drop off.toNat) (hm : TailMetaW m bs)
    (hlw : LoWr m off.toNat) :
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
              osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs' ∗ ⌜TailMetaW m' bs' ∧
                m'.size = max m.size (off.toNat + data.length) ∧
                off.toNat + data.length ≤ max m.size maxBytes ∧ LoWr m' (off.toNat + data.length)⌝) ∨
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
  have hm2 : TailMetaL m' bs' (off.toNat + data.length) ∧ m'.size = max m.size wr ∧
      wr ≤ max off.toNat maxBytes ∧ LoWr m' (off.toNat + data.length) := by
    subst hm' hbs' hwr0
    exact ⟨hm.tailMetaL _, twW_init _ _ hin, Nat.le_max_left _ _, hlw.mono (Nat.le_add_right _ _)⟩
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
    have hin' : (off + nnv).toNat ≤ m'.size := by rw [hoffv]; exact twW_in _ _ _ _ hwa hm2.2.1
    have hE' : (off + nnv).toNat + chunk.length ≤ off.toNat + data.length := by
      rw [hoffv]; exact twW_E _ _ _ _ hc1 hnn
    have hS' : chunk <+: (tailStream Mr H md cuts).drop (off + nnv).toNat := by
      obtain ⟨t, ht⟩ := hS
      have e : (tailStream Mr H md cuts).drop (off + nnv).toNat = data.drop nnv.toNat ++ t := by
        have e1 : ((tailStream Mr H md cuts).drop off.toNat).drop nnv.toNat =
            (tailStream Mr H md cuts).drop (off + nnv).toNat := by
          rw [List.drop_drop, hoffv]; try (congr 1; omega)
        rw [← e1, ← ht, List.drop_append_of_le_length (by omega)]
      rw [e]; exact hcp.trans (List.prefix_append _ _)
    wp_apply wp_tailPWriteStartW Mr R jr r dir γ H md cuts wr m' bs' fd (off + nnv) chunk dq d
      (off.toNat + data.length) _ hwr
      hoffv' (by rw [hoffv]; exact hwa) (by rw [hoffv]; exact hre) hcne hin' hS' hm2.1
      $$ Harea Hosfd Hk Hv Hm Hb as %t %nst %hfr Hosfd Hfl
    wp_apply wp_tailPWriteFinishW Mr R jr r dir γ H md cuts wr d.ino
      ⟨t, (off + nnv).toNat, chunk, nst, m', bs', none⟩ (off.toNat + data.length) _ rfl hfr.1 hm2.1 hin'
      (by show (off + nnv).toNat ≤ wr; rw [hoffv]; exact hwa) hE' hS'
      $$ Harea Hfl as %k %e %zs %hke Hk Hv Hm Hb
    dsimp only at hke
    obtain ⟨hk, hke2, hkM, hmL, hmW, hsz, hcand⟩ := hke
    have hnst : 0 < nst := hfr.1
    clear hS' hfr
    rw [hoffv] at hkM hmL hmW hsz hcand hin' hE' ⊢
    obtain ⟨hst1, hst2, hst3⟩ := twW_step m.size wr (off.toNat + nnv.toNat) k m'.size maxBytes off.toNat
      hm2.2.1 hwa hm2.2.2.1 hkM
    have hm2' : TailMetaL (pwPostK true m' (off.toNat + nnv.toNat) chunk k nst)
        (finBytes m' bs' (off.toNat + nnv.toNat) chunk k nst zs) (off.toNat + data.length) ∧
        (pwPostK true m' (off.toNat + nnv.toNat) chunk k nst).size =
          max m.size (max wr (off.toNat + nnv.toNat + k)) ∧
        max wr (off.toNat + nnv.toNat + k) ≤ max off.toNat maxBytes ∧
        LoWr (pwPostK true m' (off.toNat + nnv.toNat) chunk k nst) (off.toNat + data.length) :=
      ⟨hmL, hsz.trans hst1, hst2, hm2.2.2.2.pwK hin' hE' hk⟩
    have hcI := twW_cand (off.toNat + nnv.toNat) wr m'.size m.size k hwa hm2.2.1
    clear hmL hsz hkM
    obtain ⟨hx1, hx2, hx3⟩ := tw_max wr (off.toNat + nnv.toNat + k)
    generalize max wr (off.toNat + nnv.toNat + k) = w' at hx1 hx2 hx3 hm2' hcI ⊢
    try wp_auto
    by_cases he4 : e = W64 4
    · -- `EINTR`: the attempt again, from `nn`
      rw [decide_eq_true he4]
      wp_pure
      obtain ⟨i1, i2, i3, i4⟩ := tw_eintr _ _ _ _ _ _ _ hwa hwb hwc hc1 hc3 hk hx1 hx2 hx3 hc0
      have hre' : off.toNat + nnv.toNat = w' ∨
          ∃ q ∈ ((finBytes m' bs' (off.toNat + nnv.toNat) chunk k nst zs).getD
            (off.toNat + nnv.toNat) (0, [])).2, 0 < q.2 :=
        hcI.imp id fun h => ⟨_, hcand _ (Nat.le_refl _) i4 h, hnst⟩
      iapply IH $$ %(pwPostK true m' (off.toNat + nnv.toNat) chunk k nst)
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
          have hfu := twW_full off.toNat nnv.toNat data.length k chunk.length hfull hk hc1
          ipureintro
          exact ⟨hmW hfu.1 hfu.2, hm2'.2.1, twW_end _ _ _ _ hm2'.2.2.1 hin, hm2'.2.2.2⟩
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
            · rcases twW_cand2 (off.toNat + nnv.toNat + k) wr _ w' hst3 hx2 hx3 with h3 | h3
              · left; rw [← Nat.add_assoc]; exact h3
              · right; rw [← Nat.add_assoc]; exact ⟨_, hcand _ h1 h2 h3, hnst⟩
          iapply IH $$ %(pwPostK true m' (off.toNat + nnv.toNat) chunk k nst)
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

/-- **`(*os.File).Write` on the tail, from inside the file** (`wp_tailWrite` with `wp_tailWriteAtW`): a non-empty `b` at the offset `o`, the record's write position
`wr`; on success `len(b)`, the offset and the write position past `b`; on an error the handle's
parts of the tail are lost. -/
theorem wp_tailWriteW [os.file.FieldAssumptions] (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (dir : GoString) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (data : List w8) (dqs : DFrac) (o : w64) (wr : Nat) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (bs : List ByteG) (hfd : 0 ≤ fd.toInt) (hwr : d.writable = true) (h0 : 0 ≤ o.toInt)
    (hwrn : o.toNat = wr) (hn : 0 < data.length) (hin : wr ≤ m.size)
    (hmax : o.toInt + data.length < 2 ^ 62)
    (hS : data <+: (tailStream Mr H md cuts).drop wr) (hm : TailMetaW m bs) (hlw : LoWr m wr) :
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
              osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs' ∗ ⌜TailMetaW m' bs' ∧
                m'.size = max m.size (wr + data.length) ∧
                wr + data.length ≤ max m.size maxBytes ∧ LoWr m' (wr + data.length)⌝) ∨
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
  wp_apply wp_tailWriteAtW Mr R jr r dir γ H md cuts f fd name dqf sl data dqs o dq d m bs hwr h0 hn
      hin h63 hS hm hlw
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

/-- **The tail writer's state past the size** (`wal.tailWriterW`): `walTailW` with the tail's size the
larger of `sz` and the stream's end, a resize window possibly open (`TailMetaW`), the stream's end below
`max sz maxBytes` (a write lands nothing past `maxBytes`). At `o0 + |out| ≤ sz`, `walTailW … sz out
TailMetaW` and that bound. -/
def walTailWS (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8) :
    IProp GF :=
  iprop(walTailW (W := W) f fd name dir γ i H md cuts o0 (max sz (o0 + out.length)) out TailMetaW ∗
    ⌜o0 + out.length ≤ max sz maxBytes⌝)

/-- **The tail's writer, from inside the file** (`wal.tailWriter` over `wp_tailWriteW`): the tail file
`f` of inode `i`, written from the encoder's start `o0`, is a guarded stream of its intended bytes
(`tailOkW`: no size clause), the tail growing past its size `sz` as needed (`walTailWS`); a failed write
leaves nothing the program keeps. -/
theorem wal.tailWriterW [os.file.FieldAssumptions] (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      io.writerStreamP (wal.fileWi f) (tailOkW Mr H md cuts o0)
        (walTailWS (W := W) f fd name dir γ i H md cuts o0 sz) (fun _ _ => iprop(True)) := by
  iintro #Harea
  unfold io.writerStreamP
  iintro !> %out %p %xs %dqp %hok
  iintro !> %Φ ⟨HW, Hp⟩ HΦ
  iunfold walTailWS at HW
  icases HW with ⟨HW, %hob⟩
  iunfold walTailW at HW
  icases HW with ⟨Hf, ⟨%rd, Hfd⟩, Ho, Hk, %m, %bs, Hm, Hb, %hmb, Hv⟩
  obtain ⟨hsz, hm, hsz62, hfd0, hlw⟩ := hmb
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
      iunfold walTailWS
      rw [List.append_nil]
      isplitl [Hf Ho Hk Hfd Hm Hb Hv]
      · iunfold walTailW
        iframe Hf Ho Hk
        isplitl [Hfd]
        · iexists rd; iexact Hfd
        iexists m, bs
        iframe Hm Hb Hv
        ipureintro; exact ⟨hsz, hm, hsz62, hfd0, hlw⟩
      · ipureintro; exact hob
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
  have hin : o0 + out.length ≤ m.size := by rw [hsz]; exact Nat.le_max_right _ _
  wp_apply (wp_tailWriteW Mr R jr r dir γ H md cuts f fd name (DFrac.own 1) p xs dqp
      (W64 ((o0 + out.length : Nat) : Int)) (o0 + out.length) (DFrac.own 1) ⟨i, rd, true⟩ m bs hfd0
      rfl (by rw [hoI]; omega) hoN hn hin (by rw [hoI]; omega) hS hm hlw)
    $$ [Harea Hf Ho Hp Hfd Hk Hv Hm Hb] as %n %err ⟨Hf, Hp, Hres⟩
  · unfold tailVar; iframe; iexact Harea
  iapply HΦ
  iframe Hp
  icases Hres with (⟨%hres, Ho, Hfd, Hk, Hv, %m', %bs', Hm, Hb, %hmb⟩ | %herr)
  · ileft
    obtain ⟨hmW, hsz', hmax, hlw'⟩ := hmb
    obtain ⟨p1, p2, p3⟩ := twW_post sz (o0 + out.length) xs.length m.size m'.size maxBytes hsz hsz'
      (by rw [hsz]; exact hsz62) (by rw [Nat.add_assoc]; exact hle) hmax hob
    isplitr
    · ipureintro
      refine ⟨hres.1, ?_⟩
      rw [hres.2]; simp only [sint.Z]; rw [os.W64_nat_toInt xs.length (by omega)]
    iunfold walTailWS
    rw [List.length_append, ← Nat.add_assoc]
    isplitl [Hf Hk Hfd Ho Hm Hb Hv]
    · iunfold walTailW
      rw [List.length_append, ← Nat.add_assoc]
      iframe Hf Hk
      isplitl [Hfd]
      · iexists rd; iexact Hfd
      isplitl [Ho]
      · rw [show W64 ((o0 + out.length : Nat) : Int) + W64 (xs.length : Int) =
            W64 ((o0 : Int) + ((out.length + xs.length : Nat) : Int)) by
          simp only [W64]; push_cast; rw [← BitVec.ofInt_add]; congr 1; omega]
        iexact Ho
      iexists m', bs'
      iframe Hm Hb
      isplitr
      · ipureintro; exact ⟨p1, hmW, p2, hfd0, hlw'⟩
      unfold tailVar
      try dsimp only
      iexact Hv
    · ipureintro; exact p3
  · iright
    isplitr
    · ipureintro; exact herr
    ipureintro; trivial

end tail

end WalFs
end EtcdGrove
end Perennial

end
