/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ValidSnapshotEntries.lean` (W8 of
`notes/wal-fsext-plan.md`): the update committed and every segment pinned once, at a step before the retry
loop (`walInv_openAll`); each attempt is `validSnapshotEntries` over the pin (`specPinned`, or `specAbsent`
with no WAL); the put-back (`walInv_unpinAll`) at the step after the attempt that returns.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries
public import LinuxFs.Spec.go_uber_org.zap.String
public import LinuxFs.Spec.go_uber_org.zap.Int
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.NameClaims
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`ValidSnapshotEntries`' retry loop, generic in what each attempt holds** (`A`, given back by the
attempt `hcall`, its success `Good`): the attempts' outcome is passed at a step to `Fin` (the put-back of
the pin), at the attempt that returns. -/
theorem wal.ValidSnapshotEntries.wp_core (lg : Loc) (dir : GoString) (A : IProp GF) (Good : GoSlice → IProp GF)
    (Ψ : GoSlice → GoInterface → IProp GF)
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hcall : {{ A }}
      (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries)) (Val #lg)) (Val #dir))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); A ∗
          ((⌜err ≠ GoInterface.nil⌝ ∗ wal.vseErrIs err) ∨ (⌜err = GoInterface.nil⌝ ∗ Good sl)) }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗ A ∗
        (∀ (sl : GoSlice) (err : GoInterface), A -∗ (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ Good sl)) -∗
          notCrashed (hC := hG.goose_localGS.goose_crashGS) ={⊤}=∗
          notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ Ψ sl err) }}
      (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.ValidSnapshotEntries)) (Val #lg)) (Val #dir))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); Ψ sl err }} := by
  wp_start as ⟨#Hzap, HA, Hfin⟩
  try wp_auto
  ihave HI : (∃ (att : w64) (le : GoInterface), "attempt" ∷ attempt_ptr ↦ att ∗
      "lastErr" ∷ lastErr_ptr ↦ le ∗ "%hatt" ∷ ⌜1 ≤ sint.Z att ∧ sint.Z att ≤ 4⌝ ∗
      "Hst" ∷ ((⌜sint.Z att ≤ 3⌝ ∗ A ∗
        (∀ (sl : GoSlice) (err : GoInterface), A -∗
          (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ Good sl)) -∗
          notCrashed (hC := hG.goose_localGS.goose_crashGS) ={⊤}=∗
          notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ Ψ sl err)) ∨
        (⌜sint.Z att = 4⌝ ∗ Ψ slice.nil le)) : IProp GF)
      $$ [attempt lastErr HA Hfin]
  · iexists W64 1, _
    iframe
    isplitr
    · ipureintro; exact ⟨by decide, by decide⟩
    ileft
    iframe
    ipureintro; decide
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #Hos, -⟩
  ihave ⟨%nx, #Hnx⟩ := os.errNotExist_of_pkgInit $$ Hos
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  wp_for HI
  obtain ⟨hatt1, hatt4⟩ := hatt
  wp_if_destruct
  · -- an attempt
    have hlt3 : sint.Z att ≤ 3 := by
      first | exact Hif | (revert Hif; simp) | word
    icases Hst with (⟨-, HA, Hfin⟩ | ⟨%h4, -⟩)
    rotate_left
    · exfalso; omega
    try wp_auto
    wp_apply hcall $$ [$HA] as %sl %err ⟨HA, Hres⟩
    try wp_auto
    icases Hres with (⟨%herr, #Hes⟩ | ⟨%herr, Hg⟩)
    · -- an error: `errors.Is(err, os.ErrNotExist)`
      rcases err with ei | _
      rotate_left
      · exact absurd rfl herr
      dsimp only
      try wp_auto
      iunfold wal.vseErrIs at Hes
      ihave Hes1 := Hes $$ %nx Hnx
      wp_apply Hes1 $$ [] as %b -
      try wp_auto
      cases b
      · -- not `ErrNotExist`: return the error
        iapply wp_notCrashed_acc _ _ rfl
        iintro Hnc
        imod Hfin $$ %slice.nil %(GoInterface.ok ei) HA [] Hnc with ⟨Hnc, HΨ⟩
        · ileft; ipureintro; exact herr
        imodintro
        iframe Hnc
        try wp_auto
        wp_for_post
        try wp_auto
        iapply HΦ; iexact HΨ
      · -- `ErrNotExist`: the next attempt
        by_cases Hw : sint.Z att < sint.Z (W64 3)
        · try wp_auto
          simp only [decide_eq_true Hw]
          wp_pures
          try wp_auto
          wp_apply wp_String as %f1 -
          wp_apply wp_Int as %f2 -
          wp_apply wp_Int as %f3 -
          wp_apply wp_Error as %f4 -
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3, f4]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          try wp_auto
          wp_apply wp_Warn lg _ _ $$ []
          · iframe #
          try wp_auto
          wp_for_post
          try wp_auto
          iframe
          iexists att + W64 1, GoInterface.ok ei
          iframe
          isplitr
          · ipureintro; constructor <;> word
          ileft
          iframe
          ipureintro; word
        · -- the third attempt failed: put back now, while steps remain
          iapply wp_notCrashed_acc _ _ rfl
          iintro Hnc
          imod Hfin $$ %slice.nil %(GoInterface.ok ei) HA [] Hnc with ⟨Hnc, HΨ⟩
          · ileft; ipureintro; exact herr
          imodintro
          iframe Hnc
          try wp_auto
          simp only [decide_eq_false Hw]
          wp_pures
          try wp_auto
          wp_for_post
          try wp_auto
          iframe
          iexists att + W64 1, GoInterface.ok ei
          iframe
          isplitr
          · ipureintro; constructor <;> word
          iright
          iframe
          ipureintro; word
    · -- success: return the snapshots
      subst herr
      dsimp only
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod Hfin $$ %sl %GoInterface.nil HA [Hg] Hnc with ⟨Hnc, HΨ⟩
      · iright; iframe; ipureintro; rfl
      imodintro
      iframe Hnc
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ; iexact HΨ
  · -- the loop's end: three attempts failed
    icases Hst with (⟨%h3, -, -⟩ | ⟨%h4, HΨ⟩)
    · exfalso
      apply Hif
      first | exact h3 | (simp; word) | word
    try wp_auto
    iapply HΦ; iexact HΨ

theorem wal.ValidSnapshotEntries.wp_proof (Mr : WalMarshal)
    (wp_pinned : go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.specPinned (W := W) Mr)
    (wp_absent : go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries.specAbsent (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    wal.ValidSnapshotEntries.spec (W := W) Mr := by
  intro lg R jr r dir nm qp Q hin hnmO hr hdl
  iintro %Φ ⟨#Hpkg, #Hzap, #Hok, Hp, Hres, Hperm, Hu, Hau⟩ HΦ
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  have hnm := hin.1
  have hdc := dir_child hin
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_openAll walCodec Mr R jr r dir nm N _ h Wn Q hin (hok.1 nm hnm)
    $$ Hinv Hsi Hnc Hu Hau HN Hsf with ⟨Hnc, HN, Hsf, %o, HQ, Hcase⟩
  icases Hcase with (⟨⟨%ho, %hNnm, %hcn⟩, Hu⟩ | ⟨%d, %lay, %X, %hj, ⟨%hle, %hpin⟩, Hpin⟩)
  · -- no WAL: every attempt fails at `readWALNames`
    subst ho
    imodintro
    iframe Hnc
    have hcall : {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
          osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ zapLoggerOk lg ∗
          (osPathS R r (DFrac.own qp) jr ∗ osCallPerm 1 ∗ osNames jr N (DFrac.own (1 : Qp).half) h) }}
        (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries)) (Val #lg)) (Val #dir))
        {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
            osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ zapLoggerOk lg ∗
            (osPathS R r (DFrac.own qp) jr ∗ osCallPerm 1 ∗ osNames jr N (DFrac.own (1 : Qp).half) h)) ∗
          ((⌜err ≠ GoInterface.nil⌝ ∗ wal.vseErrIs err) ∨ (⌜err = GoInterface.nil⌝ ∗ (BI.pure False : IProp GF))) }} := by
      iintro %Φ' ⟨#Hpk, #Hoi, #Hsi', #Hz, Hp', Hperm', HN'⟩ HΦ'
      rw [hdc]
      wp_apply wp_absent lg R r nm jr qp N h hnmO hNnm hcn $$ [Hp' Hperm' HN'] as %sl %err
        ⟨Hp', Hperm', HN', %herr, #Hes⟩
      · iframe; iframe #
      iapply HΦ'
      iframe; iframe #
      ileft; iframe #; ipureintro; exact herr
    wp_apply (wal.ValidSnapshotEntries.wp_core lg dir _ (fun _ => (BI.pure False : IProp GF))
      (fun sl err => iprop(osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
        WalFs.walUnlockedTok ∗ ∃ o : Option WalDur, Q o ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ (d : WalDur) (ps : List Loc), ⌜o = some d⌝ ∗ sl ↦*□ ps ∗
          walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut))))
      wp_String wp_Int wp_Error wp_Warn hcall) $$ [Hp Hperm HN Hsf Hcl Hu HQ] as %sl %err HΨ
    · iframe; iframe #
      iintro %sl %err ⟨-, -, -, -, Hp, Hperm, HN⟩ Hout Hnc
      imodintro
      iframe Hnc Hp Hperm
      isplitl [HN Hsf Hcl]
      · unfold walAreaRes; iexists N, h, cl, Wn; iframe
        ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩
      iexists none
      iframe HQ
      icases Hout with (%herr | ⟨-, %hF⟩)
      · ileft; ipureintro; exact herr
      · exact hF.elim
    iapply HΦ $$ HΨ
  · -- a WAL: every segment pinned
    obtain ⟨hljr, hX, hcoh, habs, hidle, hnd, hsn⟩ := hpin
    unfold walPinAllRes
    icases Hpin with ⟨#Hkey, Hl, ⟨Htf, Hnf⟩, Ho, HS, Hj⟩
    imod walInv_dirPath walCodec Mr R jr r dir lay.j X $$ Hinv Hnc Hnf Hkey with ⟨Hnc, Hnf, %qd, Hpd⟩
    imodintro
    iframe Hnc
    have hS : ∀ g ∈ lay.segs, g.om.size = g.bs.length := fun g hg => (habs.metas g hg).1
    have hcall : {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
          zapLoggerOk lg ∗ WalFs.walAreaOk walCodec Mr R jr r ∗
          (osPathS R dir (DFrac.own qd) lay.j ∗ osCallPerm 1 ∗ ([∗list] g ∈ lay.segs, segRes g) ∗
            osNames lay.j (.except X) (DFrac.own (1 : Qp).half) hj) }}
        (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries)) (Val #lg)) (Val #dir))
        {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
            zapLoggerOk lg ∗ WalFs.walAreaOk walCodec Mr R jr r ∗
            (osPathS R dir (DFrac.own qd) lay.j ∗ osCallPerm 1 ∗ ([∗list] g ∈ lay.segs, segRes g) ∗
              osNames lay.j (.except X) (DFrac.own (1 : Qp).half) hj)) ∗
          ((⌜err ≠ GoInterface.nil⌝ ∗ wal.vseErrIs err) ∨
           (⌜err = GoInterface.nil⌝ ∗ ∃ ps : List Loc, sl ↦*□ ps ∗
              walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut))) }} := by
      iintro %Φ' ⟨#Hpk, #Hz, #Hok2, Hpd', Hperm', HS', Hj'⟩ HΦ'
      wp_apply wp_pinned lg R jr r dir qd d lay X hj ⟨hljr, hX, hcoh, habs, hidle, hnd, hsn⟩ hdl
        $$ [Hpd' Hperm' HS' Hj'] as %sl %err ⟨Hpd', Hperm', HS', Hj', Hres⟩
      · iframe; iframe #
      iapply HΦ'
      iframe; iframe #
    wp_apply (wal.ValidSnapshotEntries.wp_core lg dir _
      (fun sl => iprop(∃ ps : List Loc, sl ↦*□ ps ∗
        walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut)))
      (fun sl err => iprop(osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
        WalFs.walUnlockedTok ∗ ∃ o : Option WalDur, Q o ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ (d : WalDur) (ps : List Loc), ⌜o = some d⌝ ∗ sl ↦*□ ps ∗
          walSnapsAt ps (walValidSnaps (d.H.map WalOpG.toM) d.cut))))
      wp_String wp_Int wp_Error wp_Warn hcall)
      $$ [Hpd Hperm HS Hj Hp HN Hsf Hcl HQ Hl Htf Hnf Ho] as %sl %err HΨ
    · iframe; iframe #
      iintro %sl %err ⟨-, -, -, Hpd, Hperm, HS, Hj⟩ Hout Hnc
      imod walInv_unpinAll walCodec Mr R jr r dir lay X hj hS $$ Hinv Hnc [Hl Htf Hnf Ho HS Hj]
        with ⟨Hnc, Hu⟩
      · unfold walPinAllRes; iframe; iframe #
      imodintro
      iframe Hnc Hperm Hu
      isplitl [HN Hsf Hcl]
      · unfold walAreaRes; iexists N, h, cl, Wn; iframe
        ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩
      iexists o
      iframe HQ
      icases Hout with (%herr | ⟨-, %ps, Hsl, Hsn⟩)
      · ileft; ipureintro; exact herr
      · iright
        obtain ⟨dc, rfl, hdc'⟩ : ∃ dc, o = some dc ∧ walDurLe dc d := by
          cases o with
          | none => exact absurd hle (by simp [walOptLe])
          | some dc => exact ⟨dc, rfl, hle⟩
        iexists dc, ps
        isplitr
        · ipureintro; rfl
        iframe Hsl
        rw [hdc'.1, hdc'.2.2.2.1]
        iexact Hsn
    iapply HΦ $$ HΨ


end proof

end EtcdGrove
end Perennial
