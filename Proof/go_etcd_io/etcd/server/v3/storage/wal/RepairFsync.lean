/- Lean-first (no Rocq counterpart).

# `fileutil.Fsync` of `Repair`'s truncated tail (L4; the W7-W12 log, thirteenth session)

`fileutil.Fsync.wp_specRepTail`: `Fsync.specRepTail` (`RepairCallees.lean`) over the body of `os.File.Sync`
(the part's model: the fd's kind, then the extension's `Fsync`, `EINTR` retried), by the pending token
(kind `true`):

* `os.File.Sync.wp_tailR`: `os.File.Sync.wp_proof` (`Proof/os/File__Sync.lean`) with the tail's step
  `wp_tailFsyncPE` (`FdatasyncLentE.lean`, over `walInvBody_syncPE`: the synced layout F-Z, or
  `TailPend` with the pending run `Repair` kept past `wr`, P6) for `wp_osFsync` (never `EINTR`); on
  success the token back, its `|old|` the synced layout's, the tail synced; on failure the token back.
* `fileutil.Fsync.wp_specRepTail`: the zeros known past the size first (`Fs.wp_osMeta_zfGe`), then the
  above.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncLentE
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairTailDefs
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.RepairCallees
public import Proof.os.ErrorOk
public import Spec.os.File__Sync

@[expose] public section

noncomputable section

set_option autoImplicit false

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

/-- The area's `osInv`. -/
theorem walAreaOk_osInv (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    walAreaOk (L := hG.goose_localGS) (W := W) C Mr R jr r ⊢ osInv (L := hG.goose_localGS) := by
  unfold walAreaOk
  iintro ⟨-, #H, -⟩
  iexact H

/-- **`f.Sync()` of `Repair`'s truncated tail** (`os.File.Sync.wp_proof` with `wp_tailFsyncR` for the
extension's step; see the file header). -/
theorem os.File.Sync.wp_tailR (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr : Nat)
    (m : OsMeta) (bs : List ByteG) (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd)
    (hm : TailMetaE Mr (tailCrc Mr H md cuts) wr m bs) (hzf : ∀ z, m.zf = some z → m.size ≤ z)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    {{ walAreaOk walCodec Mr R jr r ∗ os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        walLentTokB (W := W) dir γ k true ∗ tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗
        walCutFrag (W := W) none ∗
        osMeta d.ino (DFrac.own (1 : Qp).half) m ∗ osBytes d.ino 0 (DFrac.own (1 : Qp).half) bs }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        tailVar (W := W) γ ((H, md, cuts, wr, d.ino, none) : TailG) ∗ walCutFrag (W := W) none ∗
        ((⌜err = interface.nil⌝ ∗ (∃ k' : Nat, walLentTokB (W := W) dir γ k' true) ∗
            osMeta d.ino (DFrac.own (1 : Qp).half) m.synced ∗
            osBytes d.ino 0 (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  unfold os.ownFile
  wp_start as ⟨#Harea, ⟨%inner, #Hf, Hfo, #Hn, #Hsys⟩, Hosfd, Hk, Hv, Hcf, Hm, Hbs⟩
  ihave #Hos := walAreaOk_osInv walCodec Mr R jr r $$ Harea
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hos Hosfd as Hosfd
  wp_apply wp_tailFsyncPE Mr R jr r dir γ k true H md cuts wr m bs fd dq d _ hm hzf hwr
    $$ Harea Hosfd Hk Hv Hcf Hm Hbs as %e Hosfd Hv Hcf Hr
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -⟩ | ⟨%he, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  wp_auto
  icases Hr with (⟨%he, Hk, Hm, Hbs⟩ | ⟨%he, -⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn Hsys as %pe #Hok
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    iright
    ipureintro; intro h; cases h

end tail

end WalFs

section spec
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc WalFs

variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`fileutil.Fsync` of `Repair`'s truncated tail** (see the file header): `Fsync.specRepTail`. -/
theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.wp_specRepTail (Mr : WalMarshal) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specRepTail (hG := hG) (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 tg k off hS
  wp_start as ⟨#Harea, Hw, Hcf⟩
  unfold walTailPO
  icases Hw with ⟨Hf, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, hmz, hsz62, hfd⟩ := hp
  iapply Fs.wp_osMeta_zfGe _ _ rfl i _ m $$ Hm
  iintro %hzf Hm
  wp_auto
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  wp_apply WalFs.os.File.Sync.wp_tailR Mr R jr r dir γ k H md cuts o0 m bs f fd name (DFrac.own 1)
    (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ hmz.tailMetaE hzf hS $$ [Harea Hf Hfd Hk Hv Hcf Hm Hb]
    as %err ⟨Hf, Hfd, Hv, Hcf, Hr⟩
  · iframe; iexact Harea
  iapply HΦ
  iframe Hcf Hf Hoff
  isplitl [Hfd Hlkt]
  · iexists rd, lo, lk; iframe
  icases Hr with (⟨%he, Hk, Hm, Hb⟩ | %he)
  · ileft
    isplitr
    · ipureintro; exact he
    iframe Hk
    iexists m.synced, (bs.map (fun x => durB x.1))
    iframe Hm Hb
    isplitr
    · ipureintro
      refine ⟨by simp [OsMeta.synced, hmsz], ⟨by simp [OsMeta.synced, hmz.1.1], hmz.1.2.1, rfl, rfl⟩,
        fun z hz => ?_, fun y hy => ?_⟩
      · simp only [OsMeta.synced, Option.some.injEq] at hz
        rw [← hz]; exact OsMeta.size_le_syncZ m
      · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
    · iapply tailVar_unfold $$ Hv
  · iright; ipureintro; exact he

end spec

end EtcdGrove
end Perennial

end
