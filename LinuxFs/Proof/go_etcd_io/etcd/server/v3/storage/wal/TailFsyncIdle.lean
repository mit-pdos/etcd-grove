/- Lean-first (no Rocq counterpart).

# The fdatasync of an idle tail, the step (the W7-W12 log of `notes/wal-fsext-plan.md`, sixth session)

`wp_idleFsync`: the extension's `Fsync` on the tail of a WAL no handle has registered (`Close` of
`Open`'s handle before `ReadAll`, `WAL.Close.specOpening`), the program holding half of the tail's
`OsMeta` and bytes and half of the WAL directory's claim, in which the file is at the last `.wal` name
(what `openAtIndex` opened last: `readWALNames` sorts the names, `selectWALFiles` takes a suffix). It
opens `walInv`, joins the halves with the invariant's (`walInvBody_syncIdle`, `TailSyncIdle.lean`) and
runs `wp_osFsync`; on success the program's halves are the synced ones, the WAL state unchanged; on
failure (never `EINTR`) nothing changes.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncIdle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The file at the last `.wal` name of a directory is the last of its `.wal` files. -/
theorem walInos_getLast {d : Dir} {b : GoString} {i : Ino} (hb : (walNames d).getLast? = some b)
    (hi : d !! b = some (.file i)) : (walInos d).getLast? = some i := by
  obtain ⟨ns, hns⟩ := List.getLast?_eq_some_iff.1 hb
  unfold walInos
  rw [hns, List.filterMap_append]
  simp [hi]

/-- **The tail is the file at the last `.wal` name** of the directory's claim. -/
theorem tail_ino_of_last {d : Dir} {b : GoString} {i : Ino} {segs pre : List SegG} {g0 : SegG}
    (hb : (walNames d).getLast? = some b) (hi : d !! b = some (.file i))
    (hinos : walInos d = segs.map (·.ino)) (hs : segs = pre ++ [g0]) : i = g0.ino := by
  have h := walInos_getLast hb hi
  rw [hinos, hs] at h
  simp at h
  exact h.symm

end pure

section step
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **An idle tail's fdatasync** (see the file header). -/
theorem wp_idleFsync (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (j : Ino) (X : List GoString) (hj0 : NamesH) (b : GoString) (m : OsMeta) (bs : List ByteG)
    (fd : w64) (dq : DFrac) (d : OsFd) (Φ : val → IProp GF)
    (hb : (walNames hj0.cur).getLast? = some b) (hi : hj0.cur !! b = some (.file d.ino))
    (hlen : bs.length = m.size) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ osFd fd dq d -∗ walDirKey (W := W) dir j X -∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗ walTailsFrag (W := W) ∅ -∗
      walCutFrag (W := W) none -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ e : w64, osFd fd dq d -∗ walDirKey (W := W) dir j X -∗
        osNames j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗ walTailsFrag (W := W) ∅ -∗
        walCutFrag (W := W) none -∗
        ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Harea Hfd Hk Hn Hf Hcf Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_syncIdle walCodec Mr R jr r s dir j X hj0 $$ Hb Hk Hn Hf Hcf with
    ⟨%lay, %pre, %g0, %hp, Hseg, Hk, Hn, Hf, Hcf, Hconts⟩
  obtain ⟨hs, hinos, hsz⟩ := hp
  have hino : d.ino = g0.ino := tail_ino_of_last hb hi hinos hs
  unfold segRes
  icases Hseg with ⟨Hm2, Hb2⟩
  rw [← hino]
  icases osMeta_agree' _ _ _ _ _ $$ Hm1 Hm2 with %hmm
  subst hmm
  icases osBytes_agree d.ino _ _ 0 bs g0.bs (by rw [hlen, hsz]) $$ Hb1 Hb2 with %hbb
  subst hbb
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  ihave Hbw := (osBytes_halves _ _ _).2 $$ [Hb1 Hb2]
  · iframe
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osFsync fd dq d g0.om 0 g0.bs (OsMeta.covers_whole _ hlen) osN_sub_nwal $$ Hos Hfd Hm Hbw
  iintro %e Hr Hfd
  icases Hr with (⟨%he, Hm, Hb⟩ | ⟨%he, Hm, Hb⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨Hsucc, -⟩
    ihave Hb := Hsucc $$ [Hm2 Hb2]
    · dsimp only [syncTail]; rw [← hino]; iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hk Hn Hf Hcf
    ileft
    iframe
    ipureintro; exact he
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨-, Hfail⟩
    ihave Hb := Hfail $$ [Hm2 Hb2]
    · iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hk Hn Hf Hcf
    iright
    iframe
    ipureintro; exact he

end step

end WalFs
end EtcdGrove
end Perennial

end
