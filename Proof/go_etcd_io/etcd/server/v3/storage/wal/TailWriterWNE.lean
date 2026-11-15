/- Lean-first (no Rocq counterpart).

# The tail's `pwrite` end with no errno (`NoIoErr`, `notes/wal-units/noioerr.md`)

`wp_tailPWriteFinishWNE`: `wp_tailPWriteFinishW` (`TailWriterW.lean`) over a semantics whose steps satisfy
the premise **no I/O error on chosen files** (every inode covered), at an offset below `maxBytes`: the
same proof with `wp_osPWriteFinishKNE` in place of `wp_osPWriteFinishK`, the errno 0. The first brick of
an error-free tail writer (the rest: `notes/wal-units/noioerr.md`, "What is left").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriterW
public import GooseLang.Ext.Fs.NoIoErrSpecs

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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- **`wp_tailPWriteFinishW` with no errno** (`NoIoErr`, every inode covered; the write's offset below
`maxBytes`): as `wp_tailPWriteFinishW`, the `k`
bytes written (`wp_osPWriteFinishK true`), the write position past them (or where it was), the file idle;
the size `pwSize` (below `maxBytes` if it grew: `PwCut`); the program's tail facts `TailMetaL`, and
`TailMetaW` after a write of all of its data up to `E`; the write's range carries its candidate on every
byte the file has after it. -/
theorem wp_tailPWriteFinishWNE (hS0 : ∀ st i, Sio.ino st i) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat) (i : Ino)
    (fl : SegFl) (E : Nat) (Φ : val → IProp GF) (hrz : fl.rz = none) (hn : 0 < fl.n)
    (hm : TailMetaL fl.m fl.bs E) (hoffl : fl.off ≤ fl.m.size) (hwrf : fl.off ≤ wr)
    (hE : fl.off + fl.data.length ≤ E) (hoffM : fl.off < maxBytes) (hS : fl.data <+: (tailStream Mr H md cuts).drop fl.off) :
    ⊢ walAreaOk walCodec Mr R jr r -∗
      walTailFlW dir γ (H, md, cuts, wr, i, some fl) i fl -∗
      (∀ (k : Nat) (zs : List Cands),
        ⌜k ≤ fl.data.length ∧ (k = fl.data.length ∨ 0 < k) ∧
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
        Φ (PairV (#(W64 k)) (#(0 : w64)))) -∗
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
  iapply wp_osPWriteFinishKNE hS0 true fl.t g0.ino fl.off fl.data fl.m (cfRange fl.m fl.bs fl.off fl.data.length)
    fl.n hoffM osN_sub_nwal $$ Hos [Htok]
  · unfold pwTok; iframe; ipureintro
    exact ⟨hgap, hd, hrl⟩
  iintro %k %zs %hke %hzc %hcut Hm Hrg -
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
      fun K c h => dirKeysOk_tailA hdw hl hstep h, trivial⟩
  · rw [show F' !! g'.ino = none from GMap.lookup_delete_eq _ _]
    dsimp only
    unfold segRes
    dsimp only [g', segFinW]
    iframe Hm2 Hb2
  imod Hid
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  have hpost : k ≤ fl.data.length ∧ (k = fl.data.length ∨ 0 < k) ∧
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
  iapply HΦ $$ %k %zs %hpost Hk Hv Hm1
  iexact Hb1

end tail

end WalFs
end EtcdGrove
end Perennial

end
