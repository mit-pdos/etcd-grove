/- Lean-first (no Rocq counterpart).

# `ReadAll`'s error exits (W3/W5 of `notes/wal-fsext-plan.md`, twentieth session)

What every error return of `ReadAll` (S/wal.go:512-684) needs for the spec's error post (`Q d ∗
walReadFailedF w dir`), as one rule over the code still to run (`readAll_failWp`): the client's
update committed with nothing changed (`walAu_same`: the state it holds is the state it gets back,
so no look at the invariant is needed; the error post asks nothing of `d`) and the ghost handle's
mode set from `opening s` to `failed` (`walInv_failOpening`, `walHandleP_set` on the handles'
authority in `walInvBody`). The program's halves of the segments, lent out of the live decoder
and given back (`ownDecoder_halves`: the look at the invariant before the loop needs them). Also `decEnv_nonnil` (`io.EOF` and `io.ErrUnexpectedEOF` are not nil:
the loop's condition `err == nil` fails at every stop).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtSteps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import GooseLang.Ext.Fs.NotCrashedAcc
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The ghost handle's mode set to `failed`, on the invariant's contents. -/
theorem walInvBody_failOpening (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (w : Loc) (dir : GoString) (sn : w64 × w64) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walOpening (W := W) w dir sn ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walReadFailed (W := W) w dir := by
  iintro Hb Ho
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases (walGhost_handleAuth (W := W) s).1 $$ Hg with ⟨Ha, Hg⟩
  unfold walOpening walReadFailed
  imod walHandleP_set (W := W) w dir (.opening sn) .failed $$ Ha Ho with ⟨Ha, Ho⟩
  ihave Hg := Hg $$ Ha
  imodintro
  iframe Ho
  iexists Ls, cl, n, F
  iframe

/-- **`ReadAll` failed: the ghost handle `failed`** (see the file header). -/
theorem walInv_failOpening (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walOpening (W := W) w dir sn ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walReadFailed (W := W) w dir := by
  iintro #Hinv Hnc Ho
  iapply walInv_step C Mr R jr r (walOpening (W := W) w dir sn) (walReadFailed (W := W) w dir) ⊤
    CoPset.subseteq_top (fun s => by
      iintro Hb Ho
      imod walInvBody_failOpening C Mr R jr r s w dir sn $$ Hb Ho with ⟨Hb, Ho⟩
      imodintro
      iframe)
    $$ Hinv Hnc Ho

/-- **The client's update committed with nothing changed** (see the file header). -/
theorem walAu_same (dir : GoString) (Pre : WalDur → Prop) (Q : WalDur → IProp GF) :
    ⊢ (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d ∗ ⌜Pre d⌝ }> @ walAuMask, ∅
        <{ walDiskAt (W := W) dir d, COMM Q d }>) ={⊤}=∗ ∃ d, Q d ∗ ⌜Pre d⌝ := by
  iintro Hau
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod (fupd_mask_subseteq (show (⊤ : CoPset) \ ↑walN ⊆ (⊤ : CoPset) from fun _ _ => CoPset.mem_full))
    with Hmc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%dc, ⟨Ho, %hpre⟩, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ Ho with HQ
  imod Hmc
  imodintro
  iexists dc
  iframe HQ
  ipureintro; exact hpre

end iris

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **An error exit of `ReadAll`** (see the file header): before the code `e` that returns the
error, the update committed unchanged and the ghost handle `failed`. -/
theorem readAll_failWp (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) (Pre : WalDur → Prop) (Q : WalDur → IProp GF)
    (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ walOpening (W := W) w dir sn -∗
      (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d ∗ ⌜Pre d⌝ }> @ walAuMask, ∅
        <{ walDiskAt (W := W) dir d, COMM Q d }>) -∗
      (∀ d, Q d -∗ walReadFailed (W := W) w dir -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }} := by
  iintro #Hinv Ho Hau Hk
  iapply wp_notCrashed_acc _ _ h
  iintro Hnc
  imod walInv_failOpening (L := hG.goose_localGS) C Mr R jr r w dir sn $$ Hinv Hnc Ho with ⟨Hnc, Hf⟩
  imod walAu_same dir Pre Q $$ Hau with ⟨%d, HQ, -⟩
  imodintro
  iframe Hnc
  iapply Hk $$ HQ Hf

end wp

section halves
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- The program's halves of the segments `gs`. -/
abbrev segHalves (gs : List SegG) : IProp GF :=
  iprop([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
    osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- **The halves lent out of the files' readers.** -/
theorem ownFbrs_halves (IoE : GoInterface → Prop) (eof : GoInterface) :
    ∀ (fbrs : List Loc) (fs : List (DecFile GF)) (rs : List (List w8)) (gs : List SegG),
    fs.length = gs.length →
    (∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
      ∃ (f : Loc) (fd : w64) (nm : GoString) (fl : OsFd), F.S = walFileS f fd nm fl g) →
    ownFbrs IoE eof fbrs fs rs ⊢ segHalves gs ∗ (segHalves gs -∗ ownFbrs IoE eof fbrs fs rs)
  | [], [], [], [], _, _ => by
    iintro -
    isplitl
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    · iintro -; simp only [ownFbrs]; iempintro
  | fbr :: fbrs, ⟨fr, bs, S⟩ :: fs, r :: rs, g :: gs, hl, hk => by
    obtain ⟨f, fd, nm, fl, hS⟩ := hk 0 _ g rfl rfl
    simp only at hS
    subst hS
    have ih := ownFbrs_halves IoE eof fbrs fs rs gs (by simpa using hl)
      (fun k F g' h1 h2 => hk (k + 1) F g' h1 h2)
    simp only [ownFbrs, segHalves]
    iintro ⟨Hf, Hs⟩
    icases ih $$ Hs with ⟨Hgs, Hsb⟩
    iunfold ownFbr at Hf
    icases Hf with ⟨%b, %fi, %err, #Hfb, #Hdf, Hb, %herr, #Hans, Hfi⟩
    icases bufio.ownReader_open b fr _ _ r $$ Hb with ⟨%q, HS, Hbk⟩
    iunfold walFileS at HS
    icases HS with ⟨%hpre, Hf, Hfd, Hoff, Hm, Hby⟩
    isplitl [Hm Hby Hgs]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Hm Hby
      iexact Hgs
    · iintro Hall
      icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hall with ⟨⟨Hm, Hby⟩, Hgs⟩
      isplitl [Hf Hfd Hoff Hm Hby Hbk Hfi]
      · iunfold ownFbr
        iexists b, fi, err
        iframe Hfb Hdf Hans Hfi
        isplitl [Hf Hfd Hoff Hm Hby Hbk]
        · iapply Hbk
          iunfold walFileS
          dsimp only
          iframe Hf Hfd Hoff Hm Hby
          ipureintro; exact hpre
        · ipureintro; exact herr
      · iapply Hsb $$ Hgs
  | [], _ :: _, _, _, _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | [], [], _ :: _, _, _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, [], _, _, _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, _ :: _, [], _, _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | [], [], [], _ :: _, hl, _ => by simp at hl
  | _ :: _, _ :: _, _ :: _, [], hl, _ => by simp at hl

/-- **The halves lent out of the decoder** (see the file header). -/
theorem ownDecoder_halves (d : Loc) (IoE : GoInterface → Prop) (eof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32) (live : Bool) (gs : List SegG)
    (hl : fs.length = gs.length)
    (hk : ∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
      ∃ (f : Loc) (fd : w64) (nm : GoString) (fl : OsFd), F.S = walFileS f fd nm fl g) :
    ownDecoder d IoE eof fs off c live ⊢
      segHalves gs ∗ (segHalves gs -∗ ownDecoder d IoE eof fs off c live) := by
  unfold ownDecoder
  iintro ⟨%sl, %fbrs, %h, %rs, #Hmu, Hbrs, #Hsl, Hoff, Hcrc, Hcont, Hdc, Hf, %hwf⟩
  icases ownFbrs_halves IoE eof fbrs fs rs gs hl hk $$ Hf with ⟨Hh, Hbk⟩
  iframe Hh
  iintro Hh
  iexists sl, fbrs, h, rs
  iframe Hmu Hbrs Hsl Hoff Hcrc Hcont Hdc
  isplitl [Hh Hbk]
  · iapply Hbk $$ Hh
  · ipureintro; exact hwf

end halves

end WalFs
end EtcdGrove
end Perennial
