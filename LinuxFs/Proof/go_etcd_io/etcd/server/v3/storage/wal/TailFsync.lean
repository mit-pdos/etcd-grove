/- Lean-first (no Rocq counterpart).

# The tail's fdatasync step (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log")

`wp_tailFsync`: the extension's `Fsync` on the crash-tracked tail, every record of the history
flushed (the write position at the end of the tail's stream, no write in flight). It opens `walInv`
(`wp_atomic_nc`), joins the program's halves of the tail's `OsMeta` and bytes with the invariant's
(`walInvBody_sync`, `TailSync.lean`) and runs `wp_osFsync`. On success the invariant moves to the WAL
state with the mark at the whole history (`walSyncS`), the tail synced, and the program gets its
halves of the synced tail and `walSyncedLb dir |H|`; on failure (never `EINTR`) nothing changes.
The lock token's pending-cut flag (`walCutFrag none`) says no cut's rename is pending. The tail may
be in a resize window (`TailMetaW`: the invariant moves to `syncLayW`, W6 log, twentieth session).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriter

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

/-- **The tail's fdatasync** (see the file header). -/
theorem wp_tailFsync (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (fd : w64) (dq : DFrac) (d : OsFd) (Φ : val → IProp GF)
    (hm : TailMetaW m bs) (hwr : wr = (tailStream Mr H md cuts).length) (ko : Option Nat)
    (hko : (m.lo = m.size ∧ m.hi = m.size) ∨ ko = some m.size) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ walOldOpt (W := W) dir cuts ko -∗ osFd fd dq d -∗
      walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
      osMeta d.ino (DFrac.own (1 : Qp).half) m -∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs -∗
      (∀ e : w64, osFd fd dq d -∗ walTailKey (W := W) dir γ -∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) -∗ walCutFrag (W := W) none -∗
        ((⌜e = 0⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) ∗
            walSyncedLb (W := W) dir H.length) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ osMeta d.ino (DFrac.own (1 : Qp).half) m ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs)) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Harea Hko Hfd Hk Hv Hcf Hm1 Hb1 HΦ
  unfold walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply (wp_atomic_nc (E1 := ⊤) (E2 := (⊤ : CoPset) \ ↑walN) _ _ rfl)
  iintro Hnc
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_sync walCodec walCodec_ok Mr R jr r s dir γ _ ko $$ Hb Hk Hv Hcf Hko with
    ⟨%F, %dw, %lay, %pre, %g0, %hp, Hseg, Hk, Hv, Hcf, Hconts⟩
  obtain ⟨hdw, hs, htg, ⟨ents, habs⟩⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwrl, hino, hF⟩ := htg
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, -, -, -, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  unfold segResF segRes
  rw [← hF]
  dsimp only
  icases Hseg with ⟨Hm2, Hb2⟩
  rw [← hino]
  icases osMeta_agree' _ _ _ _ _ $$ Hm1 Hm2 with %hmm
  subst hmm
  icases osBytes_agree d.ino _ _ 0 bs g0.bs (by rw [hm.1, hsz]) $$ Hb1 Hb2 with %hbb
  subst hbb
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  ihave Hbw := (osBytes_halves _ _ _).2 $$ [Hb1 Hb2]
  · iframe
  have htail : lay.wr = (segStream walCodec Mr dw lay.cuts lay.cuts.length).length := by
    rw [← hwrl, hwr, hH, hmd, hcuts]; rfl
  have hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z := fun z hz => by
    rw [hm.1]; exact hm.2.2.1.ge z hz
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) \ ↑walN from fun _ h => h)) with Hid
  imodintro
  iframe Hnc
  iapply wp_osFsync fd dq d g0.om 0 g0.bs (OsMeta.covers_whole _ hm.1) osN_sub_nwal $$ Hos Hfd Hm Hbw
  iintro %e Hr Hfd
  icases Hr with (⟨%he, Hm, Hb⟩ | ⟨%he, Hm, Hb⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨Hsucc, -⟩
    imod Hsucc $$ [] [Hm2 Hb2] with ⟨Hb, Hpast⟩
    · ipureintro
      refine ⟨rfl, htail, hzf, hko.imp (fun h => ⟨?_, ?_⟩) (fun h => by rw [h, hm.1])⟩
      · show g0.om.lo = g0.bs.length; rw [h.1, hm.1]
      · show g0.om.hi = g0.bs.length; rw [h.2, hm.1]
    · dsimp only [syncTail]; rw [← hino]; iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists _; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hk Hv Hcf
    ileft
    iframe
    isplitr
    · ipureintro; exact he
    unfold walSyncedLb
    iexists (walSyncS s dir dw), { dw with m := dw.H.length }
    iframe Hpast
    ipureintro
    exact ⟨walSyncS_lookup s dir dw, by rw [hH]; exact Nat.le_refl _⟩
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases Hconts with ⟨-, Hfail⟩
    ihave Hb := Hfail $$ [Hm2 Hb2]
    · iframe
    imod Hid
    imod Hcl $$ [Hb]
    · iexists s; iexact Hb
    imodintro
    iapply HΦ $$ %e Hfd Hk Hv Hcf
    iright
    iframe
    ipureintro; exact he

end tail

end WalFs
end EtcdGrove
end Perennial

end
