/-
`tx.writeMeta()` (U10 of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 7): the meta page
built in a fresh buffer (`metaBuf`), written at slot `txid % 2` under `metalock`, then synced
unless `NoSync`. The commit point is the caller's: right after the `WriteAt`, still under
`metalock`, its view shift `Hcp` gets `metalock`'s resource, hands over the slot's page-cache
bytes and the client halves of its mapped cells, and gets them back as the write left them, which
for one aligned OS page is all of `metaBuf mv` or nothing (`j = 4096` or `j = 0`), whatever
`WriteAt` returned: `WriteAt.spec`'s page cut (`PwCut`, `notes/bbolt-port-plan.md` §2.4).

The spec is over local resources (the writer side's fields and file, which `Commit` takes from
`wdbLive`): `db.ops.writeAt` holds `db.file.WriteAt`'s method value, which `wdbCoreG` does not
yet say (its `wa` is unconstrained: reported, U10).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Commit.MetaBuf
public import Proof.go_etcd_io.bbolt.Mmap.LoggerDefs
public import Proof.go_etcd_io.bbolt.Mmap.Cells
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Commit.MetaPage
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Write
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.os.File__WriteAt
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link
public import Proof.ReceiptTactics
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Tx__writeMetaDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxRecDepth 20000 in
theorem Tx.writeMeta.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hPIB : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hWrite : internal.common.Meta.Write.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG)) :
    Tx.writeMeta.spec (GF := GF) (hG := hG) := by
  intro K tx r sm q dq mp mv f fd om b l dqf dqw Ψ hroot hfl hmp hsz hmaps hl
  wp_start as ⟨#Hcore, #Hreg, Hst, Hdb, Hme, Hmv, Hf, Hwa, Hfo, Hfd, Hm, Hcp⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  iunfold dbFixed at Hfix
  icases Hfix with ⟨#Hps, #Hsp, ⟨%lg, #Hlg, #Hlgok⟩, -, -, -, ⟨%ns, #Hns⟩, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  iunfold dbLogger at Hlgok
  wp_apply hLogger K.db lg Ht0.2.1 $$ []
  · iframe #
  wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hbuf, -⟩
  · ipureintro; decide
  rw [show (zero_val w8 : w8) = W8 0 from rfl]
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hpos := ownSlice_ptr_pos _ _ _ (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hbuf
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hpos $$ Hbuf
    with ⟨Hb, Hback⟩
  rw [flatMap_encode_w8]
  have hslen : sl.len.toNat = 4096 := by
    have h1 := Hlen.1; have h2 := Hlen.2
    rw [List.length_replicate] at h1; simp only [sint.nat] at h1
    word
  wp_apply hPIB K.db sl (W64 0) (by simp [hslen]) (by simp [hslen]) Hpos $$ []
  · iframe #
  rw [show (((0 * 4096 : Nat)) : Int) = 0 from rfl, loc_add_0]
  icases zeroPage_meta sl.ptr Hpos $$ Hb with ⟨%Hmax, Hh, Hm0, Hz⟩
  wp_apply hWrite mp sl.ptr mv zeroHdr _ hroot hfl hmp Hpos (by omega) $$ [Hmv Hh Hm0] as ⟨Hmv, Hh, Hm0⟩
  · iframe #; iframe
  wp_apply +noauto sync.Mutex.wp_Lock $$ [$Hsync $Hml] as ⟨Hlk, HR⟩
  wp_take_receipt as Hrc
  wp_apply hId $$ [Hh] as Hh
  · iframe #; iframe
  have hoff : ((mv.txid' % W64 2) * W64 4096).toNat = 4096 * (mv.txid'.toNat % 2) := by
    have h2 : (mv.txid' % W64 2).toNat = mv.txid'.toNat % 2 := by simp
    rw [BitVec.toNat_mul, h2]; simp; omega
  have hs2 : mv.txid'.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  -- the buffer's bytes, as `WriteAt` takes them
  icases metaPage_bytes sl.ptr mv Hpos $$ [Hh Hm0 Hz] with Hb
  · iframe
  ihave Hsl := Hback $$ %(metaBuf mv) %(by rw [metaBuf_length, List.length_replicate]) [Hb]
  · rw [flatMap_encode_w8]; iexact Hb
  -- the commit step's first half
  iunfold commitStep at Hcp
  imod Hcp $$ HR with ⟨%xs, %old, Hxs, %Hxl, Hold, Hk⟩
  ihave Hc : mcellsAny om.maps ((mv.txid' % W64 2) * W64 4096).toNat
      (((mv.txid' % W64 2) * W64 4096).toNat + (metaBuf mv).length) $$ [Hold]
  · rw [hmaps, metaBuf_length, hoff]
    iapply wm_cells_of_bytes b l _ old (by omega) Hxl.2 $$ Hold
  -- the write
  have h0 : 0 ≤ ((mv.txid' % W64 2) * W64 4096).toInt := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  wp_apply hWriteAt f fd K.p.path (DFrac.own 1) sl (metaBuf mv) (DFrac.own 1)
    ((mv.txid' % W64 2) * W64 4096) (DFrac.own 1) (dbFd K.p.ino) om xs rfl h0
    (by rw [hoff]; omega) (by rw [metaBuf_length, hoff]; omega)
    (by rw [metaBuf_length]; decide) (by rw [metaBuf_length]; decide)
    (by rw [metaBuf_length, hoff]; omega)
    $$ [Hfo Hsl Hfd Hm Hxs Hc] as %n %err ⟨Hfo, Hsl, Hfd, %j, %ys, %Hj, Hm, Hys, Hc, Herr⟩
  · iframe #
    rw [← fileOwn_eq, hoff]
    iframe
  obtain ⟨hjle, hpo, hcut, hres⟩ := Hj
  simp only [metaBuf_length, hoff] at hcut hjle
  have hj01 : j = 0 ∨ j = 4096 := by
    unfold PwCut at hcut
    simp only [osPageSize] at hcut
    omega
  have hys : ys.map Prod.fst = (if j = 0 then xs.map Prod.fst else metaBuf mv) := by
    rw [hoff] at hpo
    exact pwOut_inside_fst om (4096 * (mv.txid'.toNat % 2)) (metaBuf mv) j xs ys
      (by rw [metaBuf_length]; omega) (by rw [metaBuf_length]; exact Hxl.1)
      (by rw [metaBuf_length]; exact hj01) hpo
  have hyl : ys.length = 4096 := by
    have := congrArg List.length hys
    simp only [List.length_map] at this
    rw [this]; split
    · simp [Hxl.1]
    · exact metaBuf_length mv
  have hsize : pwSize om.size (4096 * (mv.txid'.toNat % 2)) j = om.size :=
    pwSize_inside _ _ _ 4096 (by omega) (by omega)
  have hom' : (pwPost om (4096 * (mv.txid'.toNat % 2)) (metaBuf mv).length j).size = om.size ∧
      (pwPost om (4096 * (mv.txid'.toNat % 2)) (metaBuf mv).length j).maps = om.maps :=
    ⟨hsize, by simp only [pwPost, announce_maps]⟩
  rw [hoff]
  generalize pwPost om (4096 * (mv.txid'.toNat % 2)) (metaBuf mv).length j = om' at hom'
  rw [metaBuf_length]
  ihave Hc : ∃ vf, cellsR b (4096 * (mv.txid'.toNat % 2)) ys.length vf $$ [Hc]
  · rw [hmaps, hyl]
    iapply wm_cells_any b l _ (by omega) $$ Hc
  icases Hc with ⟨%vf, Hc⟩
  iapply cellsR_agree_bytes _ rfl K.p (DFrac.own 1) _ b l (by simp [hom'.2, hmaps]) (DFrac.own 1)
    (by simp) _ ys (4096 * (mv.txid'.toNat % 2)) vf (by omega) $$ Hos Hm Hys Hc
  iintro Hm Hys Hc
  icases cellsR_bytes b (ys.map Prod.fst) _ $$ [Hc] with Hc
  · simp only [List.length_map]; iexact Hc
  imod Hk $$ %j %ys [] Hys Hc Hrc with ⟨HR, HΨ⟩
  · ipureintro; exact ⟨hj01, hys⟩
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlgok
  | ok li =>
  cases err with
  | ok ei =>
    -- the write failed: unlock, log, return the error
    have hj : j = 0 ∨ j = 4096 := hj01
    simp only [fmtErrorOkOrNil]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (metaR K.B K.db K.p) $$ [$Hsync $Hml $Hlk HR]
    · iexact HR
    ihave %Hpos2 := ownSlice_ptr_pos _ _ _
      (show metaBuf mv ≠ [] from List.ne_nil_of_length_pos (by rw [metaBuf_length]; decide)) $$ Hsl
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hpos2 $$ Hsl
      with ⟨Hb, Hback⟩
    rw [flatMap_encode_w8]
    icases (metaBuf_hdr sl.ptr mv Hpos2).1 $$ Hb with ⟨Hh, Hrest⟩
    wp_apply hId $$ [Hh] as Hh
    · iframe #; iframe
    rw [show (metaHdr mv).id' = mv.txid' % W64 2 from rfl]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    try wp_auto
    icases Herr with #Herr
    wp_apply wp_boltLog li _ _ [W8 100, W8 100, W8 118] _
      [interface.mkOk Pgid.ty #(mv.txid' % W64 2), interface.mkOk go.int #(W64 4096),
        GoInterface.ok ei] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl2] [] [] as Hsl2 -
    · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
        show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
      iexact Hsl2
    · simp only [List.zip_cons_cons, List.zip_nil_left, Iris.BI.BigSepL.bigSepL_cons,
        Iris.BI.BigSepL.bigSepL_nil]
      isplitr
      · iapply logArgOk_of_argWf; exact pgid_argWf _
      isplitr
      · iapply logArgOk_of_argWf
        apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
        exact .cons_int _ _ _ (.int _) .nil
      isplitr
      · iapply logArgOk_of_fmtErrorOk
        · simp [methodVerbs]
        iexact Herr
      iempintro
    try wp_auto
    iapply HΦ
    rw [← fileOwn_eq]
    unfold metaSummed
    iframe Hst Hdb Hme Hmv Hf Hwa Hfo Hfd
    isplitl [Hm]
    · iexists _; iframe; ipureintro; exact hom'
    iexists j
    iframe
    isplitr
    · ipureintro; exact ⟨hj, fun h => nomatch h⟩
    iright
    isplitr
    · ipureintro; exact fun h => nomatch h
    iexact Herr
  | nil =>
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (metaR K.B K.db K.p) $$ [$Hsync $Hml $Hlk HR]
    · iexact HR
    have hj : j = 4096 := by
      rcases hres with ⟨h1, -, -⟩ | ⟨-, h2⟩
      · rw [metaBuf_length] at h1; exact h1
      · exact absurd rfl h2
    ihave Hfo : fileOwn f fd K.p.path (DFrac.own 1) $$ [Hfo]
    · rw [fileOwn_eq]; iexact Hfo
    -- the sync (unless `NoSync`), then the statistics
    cases ns with
    | true =>
      wp_auto
      wp_apply hInc K tx r sm q (W64 1) $$ [Hst] as %_n Hst
      · iframe #; iframe
      try wp_auto
      iapply HΦ
      unfold metaSummed
      iframe Hst Hdb Hme Hmv Hf Hwa Hfo Hfd
      isplitl [Hm]
      · iexists _; iframe; ipureintro; exact hom'
      iexists j
      iframe
      isplitr
      · ipureintro; exact ⟨Or.inr hj, fun _ => hj⟩
      ileft; ipureintro; rfl
    | false =>
      wp_auto
      wp_apply hSync K.db f fd K.p K.p.ino _ dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
        as %e2 ⟨Hf, Hfo, Hfd, ⟨%m', Hm, %Hm'⟩, Hr⟩
      · iframe #; iframe
      icases Hr with (%He | ⟨%He, #Hfe⟩)
      · subst He
        wp_auto
        wp_apply hInc K tx r sm q (W64 1) $$ [Hst] as %_n Hst
        · iframe #; iframe
        try wp_auto
        iapply HΦ
        unfold metaSummed
        iframe Hst Hdb Hme Hmv Hf Hwa Hfo Hfd
        isplitl [Hm]
        · iexists m'; iframe; ipureintro; exact ⟨Hm'.1.trans hom'.1, Hm'.2.trans hom'.2⟩
        iexists j
        iframe
        isplitr
        · ipureintro; exact ⟨Or.inr hj, fun _ => hj⟩
        ileft; ipureintro; rfl
      · cases e2 with
        | nil => exact absurd rfl He
        | ok e2 =>
        ihave %hgoos : ⌜goosLinux⌝ $$ []
        · iapply goosLinux_of_pkgInit $$ Hpkg
        ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
        · iapply goarchAmd64_of_pkgInit $$ Hpkg
        unfold goosLinux at hgoos
        unfold goarchAmd64 at hgoarch
        wp_auto
        try rw [hgoos, hgoarch]
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 118] _
          [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
            GoInterface.ok e2] _ iprop(True) _
          (by decide) (by decide) rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
        · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
            show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
          iexact Hsl3
        · log_args_ok
        try wp_auto
        iapply HΦ
        unfold metaSummed
        iframe Hst Hdb Hme Hmv Hf Hwa Hfo Hfd
        isplitl [Hm]
        · iexists m'; iframe; ipureintro; exact ⟨Hm'.1.trans hom'.1, Hm'.2.trans hom'.2⟩
        iexists j
        iframe
        isplitr
        · ipureintro; exact ⟨Or.inr hj, fun _ => hj⟩
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        iexact Hfe

end proof

end bbolt
end EtcdGrove
end Perennial
