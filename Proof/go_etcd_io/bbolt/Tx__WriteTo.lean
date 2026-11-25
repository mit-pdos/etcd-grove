/-
**`Tx.WriteTo` for a read transaction** (session S4, D-I6 of `notes/bbolt-integration-plan.md`):
the reader's `WriteFlag` is zero, so the database's own `*os.File` is read; the two meta pages are
built in a page buffer from the reader's meta copy (`wtM`) and written; then `io.CopyN` copies the
file's pages `[2, hwm)` through an `io.SectionReader`, each `pread` seeing the store's bytes of the
reader's view and freelist page (`store_rd_acc`, an accessor of `os.heldAcc`); the bytes written
are an image of the reader's data (`writeTo_fileOK`, `wt_bridge`), with the receipt of its txid.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__WriteTo
public import Proof.go_etcd_io.bbolt.Read.SizeFields
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetId
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__DecTxid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetChecksum
public import Spec.fmt.Errorf
public import Spec.io.NewSectionReader
public import Spec.io.CopyN
public import Spec.os.File__ReadAt
public import Proof.os.ReaderAt
public import Proof.go_etcd_io.bbolt.Read.WriteTo
public import Proof.go_etcd_io.bbolt.Commit.MetaPage
import all Spec.go_etcd_io.bbolt.Api

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.WriteTo.wp_proof (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (wp_SetFlags : internal.common.Page.SetFlags.spec (GF := GF) (hG := hG))
    (wp_Meta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (wp_SetId : internal.common.Page.SetId.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_DecTxid : internal.common.Meta.DecTxid.spec (GF := GF) (hG := hG))
    (wp_Sum64 : internal.common.Meta.Sum64.spec (GF := GF) (hG := hG))
    (wp_SetChecksum : internal.common.Meta.SetChecksum.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_NSR : io.NewSectionReader.spec (GF := GF) (hG := hG))
    (wp_CopyN : io.CopyN.spec (GF := GF) (hG := hG))
    (hRead : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      os.File.ReadAt.specRacyLt (GF := GF) (hG := hG)) :
    Tx.WriteTo.spec (GF := GF) (hG := hG) := by
  intro _ _ _ tx γ q D w Wr c bs₀ hplain
  wp_start as ⟨Ht, #Hwr, HWr⟩
  ihave Ht : boltTx tx γ (q.half + q.half) (TxView.ro D) $$ [Ht]
  · rw [Qp.half_add_half]; iexact Ht
  icases ((boltTx_fractional (GF := GF) tx γ (TxView.ro D)).fractional q.half q.half).1 $$ Ht
    with ⟨Ht1, Ht2⟩
  iunfold boltTx at Ht2
  icases (boltTx_rdTx _ _ tx _ _ rfl).1 $$ Ht2 with ⟨%db', Hr, #Hdb'⟩
  icases rdTx_wt_acc _ _ tx _ _ $$ Hr with ⟨%K, %v, %mv, %k, %m, %l, %fx, %HK, #Hcore, Hwf, Hme,
    Hmv, Hdb, #HC, Hk, Hfile, Hmap, Hcl⟩
  obtain ⟨hKB, hKN, hTv⟩ := HK
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, #Hpkg, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  ihave #Hfix' := Hfix
  iunfold dbFixed at Hfix'
  icases Hfix' with ⟨#Hps, -⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  iunfold rdxFile at Hfile
  icases Hfile with ⟨%f, Hff, %hfn, %ti, #Hti0, %fn, Hfo, Hfd⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hbuf, -⟩
  · ipureintro; decide
  rw [show (zero_val w8 : w8) = W8 0 from rfl]
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hpos := ownSlice_ptr_pos _ _ _ (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hbuf
  have hslen : sl.len.toNat = 4096 := by
    have h1 := Hlen.1; have h2 := Hlen.2
    rw [List.length_replicate] at h1; simp only [sint.nat] at h1
    word
  try wp_auto
  have hb : sint.Z sl.len = (sl.len.toNat : Int) := by word
  rw [hb, show sint.Z (W64 0) = 0 from rfl,
    if_pos (show (0 : Int) ≤ 0 ∧ (0 : Int) < (sl.len.toNat : Int) by omega),
    sliceIndexRef_byte _ _ Hpos (by omega), loc_add_0]
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hpos $$ Hbuf
    with ⟨Hb, Hback⟩
  rw [flatMap_encode_w8]
  icases zeroPage_meta sl.ptr Hpos $$ Hb with ⟨%Hmax, Hh, Hm0, Hz⟩
  try wp_auto
  wp_apply wp_SetFlags $$ [Hh] as Hh
  · iframe #; iframe
  ihave Hb := (pageBuf_typed sl.ptr (wtHdr (W64 0)) _ Hpos).2 $$ [Hh Hm0 Hz]
  · iframe
  ihave Hbuf := Hback $$ %(encode (wtHdr (W64 0)) ++ encode (decode (List.replicate 64 (W8 0)) : Meta) ++
      List.replicate 4016 (W8 0)) %(by rw [List.length_append, List.length_append, ByteEncoding.encode_length, ByteEncoding.encode_length, List.length_replicate, List.length_replicate]) [Hb]
  · rw [flatMap_encode_w8]; iexact Hb
  try wp_auto
  ihave #HC' := HC
  iunfold rdxC at HC'
  icases HC' with ⟨%C, #Hrc, %HCf⟩
  obtain ⟨hCok, hCtree, hCtx1, hChwm, hmvC, hvC, hfxC⟩ := HCf
  have hmvtx : mv.txid'.toNat = C.txid := by rw [hmvC]; exact hCok.2.2.2.2.2.2.1.1
  ihave IH : (∃ (i : Nat), "id" ∷ id_ptr ↦ W64 (i : Int) ∗ "%hk" ∷ ⌜i ≤ 2⌝ ∗
      "n" ∷ n_ptr ↦ W64 ((4096 * i : Nat) : Int) ∗
      "Hbuf" ∷ (∃ (hid : w64) (mm : Meta),
        sl ↦* (encode (wtHdr hid) ++ encode mm ++ List.replicate 4016 (W8 0))) ∗
      "HWr" ∷ (∃ cw : Bool, Wr cw (bs₀ ++ wtPre mv i) ∗ ⌜0 < i → cw = true⌝) ∗
      "Hme" ∷ tx.[Tx, go!"meta"] ↦{DFrac.own q.half} m ∗ "Hmv" ∷ m ↦{DFrac.own q.half} mv ∗
      "buf" ∷ buf_ptr ↦ sl ∗ "page" ∷ page_ptr ↦ sl.ptr ∗ "tx" ∷ tx_ptr ↦ tx : IProp GF)
      $$ [id n Hbuf HWr Hme Hmv buf page tx]
  · iexists 0; simp only [named]
    iframe id Hme Hmv buf page tx
    isplitr
    · ipureintro; omega
    isplitl [n]
    · rw [show W64 ((4096 * 0 : Nat) : Int) = zero_val w64 from rfl]; iexact n
    isplitl [Hbuf]
    · iexists _, _; iexact Hbuf
    iexists c
    simp only [wtPre, ↓reduceIte, List.append_nil]
    iframe; ipureintro; omega
  wp_for IH
  have hi2 : uint.Z (W64 (i : Int)) = (i : Int) := by word
  rw [hi2, show uint.Z (W64 1) = 1 from rfl]
  by_cases hil : (i : Int) ≤ 1
  · rw [decide_eq_true hil]
    simp only [↓reduceIte]
    have hi : i < 2 := by omega
    icases Hbuf with ⟨%hid, %mm, Hbuf⟩
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hpos $$ Hbuf
      with ⟨Hb, Hback⟩
    rw [flatMap_encode_w8]
    icases (pageBuf_typed sl.ptr (wtHdr hid) mm Hpos).1 $$ Hb with ⟨Hh, Hm0, Hz⟩
    try wp_auto
    wp_apply wp_Meta sl.ptr Hpos (by omega)
    try wp_auto
    wp_apply wp_SetId $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply wp_Txid $$ [m] as m
    · iframe #; iframe
    try wp_auto
    have hl16 : 0 < (sl.ptr +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
    by_cases ht : mv.txid' % W64 2 = W64 (i : Int)
    have hw : wtM mv i = mv := by unfold wtM; rw [if_pos ((wtM_test mv i hi).1 ht)]
    rw [decide_eq_true ht]
    ihave Hm0 : (sl.ptr +ₗ 16) ↦ wtM mv i $$ [Hm0]
    · rw [hw]; iexact Hm0
    try wp_auto
    rotate_left
    rw [decide_eq_false ht]
    try wp_auto
    wp_apply wp_Meta sl.ptr Hpos (by omega)
    try wp_auto
    wp_apply wp_DecTxid $$ [Hm0] as Hm0
    · iframe #; iframe
    ihave Hm0 : (sl.ptr +ₗ 16) ↦ wtM mv i $$ [Hm0]
    · have hw : wtM mv i = metaDec mv := by
        unfold wtM; rw [if_neg (fun h => ht ((wtM_test mv i hi).2 h))]
      rw [hw]; unfold metaDec; iexact Hm0
    try wp_auto
    all_goals
      wp_apply wp_Meta sl.ptr Hpos (by omega)
      try wp_auto
      wp_apply wp_Sum64 (sl.ptr +ₗ 16) (wtM mv i) (DFrac.own 1) hl16 $$ [Hm0] as Hm0
      · iframe #; iframe
      try wp_auto
      wp_apply wp_Meta sl.ptr Hpos (by omega)
      try wp_auto
      wp_apply wp_SetChecksum $$ [Hm0] as Hm0
      · iframe #; iframe
      try wp_auto
      -- the page is `metaBuf (wtM mv i)`
      have h1 : 1 ≤ mv.txid'.toNat := by omega
      icases internal.common.typedPointsto_of_eq _ _ (metaHdr (wtM mv i)) _ $$ [Hh] with Hh
      · iframe; ipureintro; rw [← wtM_hdr mv i hi h1]; rfl
      icases internal.common.typedPointsto_of_eq _ _ (metaSummed (wtM mv i)) _ $$ [Hm0] with Hm0
      · iframe; ipureintro; rfl
      ihave Hb := (pageBuf_typed sl.ptr _ _ Hpos).2 $$ [Hh Hm0 Hz]
      · iframe
      rw [← metaBuf_eq_buf]
      ihave Hsl := Hback $$ %(metaBuf (wtM mv i)) %(by rw [metaBuf_length, List.length_append, List.length_append, ByteEncoding.encode_length, ByteEncoding.encode_length, List.length_replicate]) [Hb]
      · rw [flatMap_encode_w8]; iexact Hb
      icases HWr with ⟨%cw, HWr, %hcw⟩
      ihave #Hwr' := Hwr
      iunfold io.writerOk at Hwr'
      wp_apply Hwr' $$ [Hsl HWr] as %nn %werr ⟨%kk, Hsl, HWr, %Hkk, #Hwe⟩
      · iframe
      obtain ⟨hnn, hkkl, hkerr⟩ := Hkk
      rw [metaBuf_length] at hkkl
      rcases werr with wi | _
      · -- the meta page's write failed
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        ihave #Hwe' := fmtErrorOkOrNil_ne _ (by simp) $$ Hwe
        ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
        · iPkgInit
        wp_apply wp_Errorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
        · iframe; iframe #
          fmt_args_ok
          · -- the page id, a `Pgid` (a named `uint64` without methods): `ArgWf` (since fmtmodel the
            -- non-method-verb integer case asks for a method)
            ileft; ipureintro
            refine Perennial.EtcdGrove.fmt.argWf_of_argsWf (_root_.Perennial.fmt.ArgsWf.cons_int _ (uint.Z (W64 (i : Int))) []
              (_root_.Perennial.fmt.IntArgValue.named _ _ (uint.Z (W64 (i : Int))) ?_ ?_
                (_root_.Perennial.fmt.NoFmtMethods.of_methodSetIs_nil _) ?_) _root_.Perennial.fmt.ArgsWf.nil)
            · simp [_root_.Perennial.fmt.IsIntType, internal.common.Pgid.ty, go.int, go.int64, go.int32,
                go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
            · rw [go.is_underlying]; simp [_root_.Perennial.fmt.IsIntType]
            · rw [go.is_underlying]; exact .uint64 _
          iunfold fmtErrorOk at Hwe'
          icases Hwe' with ⟨%hwe, #Hwm⟩
          iright; ileft
          isplitr
          · iexact Hwm
          · ipureintro; exact hwe
        try wp_auto
        wp_for_post
        try wp_auto
        ihave Ht2 := Hcl $$ Hwf Hme Hmv Hdb Hk [Hff Hfo Hfd] Hmap
        · iunfold rdxFile
          iexists f
          iframe Hff
          isplitr
          · ipureintro; exact hfn
          iexists ti
          iframe Hti0
          iexists fn
          iframe
        ihave Ht2 : boltTx tx γ q.half (TxView.ro D) $$ [Ht2]
        · iunfold boltTx
          iapply (boltTx_rdTx _ _ tx _ _ rfl).2
          iexists db'
          iframe; iframe #
        ihave Ht := ((boltTx_fractional (GF := GF) tx γ (TxView.ro D)).fractional q.half q.half).2
          $$ [Ht1 Ht2]
        · iframe
        have hqq : boltTx (GF := GF) tx γ (q.half + q.half) (TxView.ro D) ⊢
            boltTx tx γ q (TxView.ro D) := by
          rw [Qp.half_add_half]
        ihave Ht := hqq $$ Ht
        iapply HΦ
        iexists (wtPre mv i ++ List.take kk (metaBuf (wtM mv i)))
        rw [← List.append_assoc]
        iframe
        iright; ipureintro; simp
      · -- the page written
        have hkk : kk = 4096 := by rw [metaBuf_length] at hkerr; exact hkerr rfl
        subst hkk
        try wp_auto
        wp_for_post
        iframe
        iexists (i + 1)
        have hnn' : nn = W64 4096 := by
          apply BitVec.eq_of_toNat_eq
          have : sint.Z nn = 4096 := hnn
          simp only [sint.Z] at this; word
        subst hnn'
        have hi01 : i = 0 ∨ i = 1 := by omega
        rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by rcases hi01 with rfl | rfl <;> rfl,
          show W64 ((4096 * i : Nat) : Int) + W64 4096 = W64 ((4096 * (i + 1) : Nat) : Int) by
            rcases hi01 with rfl | rfl <;> rfl]
        simp only [named]
        iframe
        isplitr
        · ipureintro; omega
        isplitl [Hsl]
        · iexists (W64 (i : Int)), (metaSummed (wtM mv i))
          rw [metaBuf_eq_buf, ← wtHdr_eq mv i hi h1] at *
          iexact Hsl
        iexists true
        isplitl [HWr]
        · have hpre : wtPre mv i ++ List.take 4096 (metaBuf (wtM mv i)) = wtPre mv (i + 1) := by
            rw [List.take_of_length_le (by rw [metaBuf_length]; omega)]
            rcases hi01 with rfl | rfl
            · simp only [wtPre, ↓reduceIte, List.nil_append, wtMeta0_eq]; rfl
            · simp only [wtPre, wtMetas, wtMeta1_eq]; rfl
          rw [List.append_assoc, hpre]; iexact HWr
        ipureintro; intro; rfl
  · rw [decide_eq_false hil]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hi : i = 2 := by omega
    subst hi
    try wp_auto
    -- the size: the high-water mark's pages
    wp_apply (Tx.Size.wp_fields wp_Pgid tx m K.db mv _ _) $$ [Hme Hmv Hdb] as ⟨Hme, Hmv, Hdb⟩
    · iframe; iframe #
    have hpg : mv.pgid'.toNat = C.hwm := by rw [hmvC]; exact hCok.2.2.2.2.2.2.1.2.2.1
    have h2 : 3 ≤ C.hwm := by
      obtain ⟨⟨hwf, -⟩, -⟩ := hCtree
      cases hwf with
      | page _ _ h2 h3 _ _ _ _ => omega
    try wp_auto
    have hoff : (W64 4096 * W64 2 : w64) = W64 8192 := rfl
    rw [hoff]
    have e1 : (mv.pgid' * W64 4096 : w64).toNat = C.hwm * 4096 := by
      rw [BitVec.toNat_mul, hpg, show (W64 4096 : w64).toNat = 4096 from rfl]
      omega
    have hsz : (mv.pgid' * W64 4096 - W64 8192 : w64).toNat = (C.hwm - 2) * 4096 := by
      rw [BitVec.toNat_sub, e1, show (W64 8192 : w64).toNat = 8192 from rfl]
      omega
    have hszZ : sint.Z (mv.pgid' * W64 4096 - W64 8192 : w64) = ((C.hwm - 2) * 4096 : Nat) := by
      have : (mv.pgid' * W64 4096 - W64 8192 : w64).toNat < 2 ^ 63 := by rw [hsz]; omega
      simp only [sint.Z]; word
    -- the section reader of the file's pages from slot 2
    wp_apply wp_NSR ⟨go.GoType.PointerType os.File.ty, #f⟩ (W64 8192)
      (mv.pgid' * W64 4096 - W64 8192) (by decide) (by rw [hszZ]; omega)
      (by rw [hsz]; simp only [show (W64 8192 : w64).toNat = 8192 from rfl]; omega) as %sr Hsr
    try wp_auto
    -- the file's inode is the database's
    ihave #Ht0' := Ht0
    iunfold t0At at Ht0'
    icombine Ht0' Hti0 gives %hti
    obtain ⟨-, hti⟩ := hti
    subst hti
    -- `io.EOF`
    ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
    · iPkgInit
    ihave #Heof := io.eof_of_init $$ Hio
    iunfold errors.newVar at Heof
    icases Heof with ⟨%eofl, #Heof, -⟩
    -- the reader's `pread`s see the store's bytes of its view and freelist page
    have hE : ↑(pagesN K.N) ⊆ (⊤ : CoPset) := CoPset.subseteq_top
    ihave #Hacc : os.heldAcc K.p.ino (wtRs C.pages fx)
        iprop(k ↪[K.B.rds]{DFrac.own q.half.half} (⟨v, fx⟩ : RdInfo) ∗
          ghostVar K.B.map (QpMul q.half sync.rfrac).half.half (some (v.base, l) : MapSt))
        (⊤ \ ↑(pagesN K.N)) $$ []
    · iunfold os.heldAcc
      imodintro
      iintro ⟨Hk, Hmap⟩
      imod store_rd_acc K.B K.N K.p ⊤ hE k v fx _ _ _ _ $$ [Hk Hmap] with ⟨%rs, Hrs, %Hrs, Hclose⟩
      · iframe; iframe #
      imodintro
      iexists rs
      iframe Hrs
      isplitr
      · ipureintro
        rw [hvC] at Hrs
        exact wtRs_held _ _ rs Hrs.1 Hrs.2
      iintro Hrs
      iapply Hclose $$ Hrs
    have hosE : ↑osN ⊆ (⊤ \ ↑(pagesN K.N) : CoPset) := fun x hx =>
      CoPset.in_diff.2 ⟨CoPset.subseteq_top x hx, fun hp => Ht0.2.2.1 x ⟨nclose_subseteq K.N "pages" x hp, hx⟩⟩
    ihave #Hrd := os.File.readerAtOk (hRead) f fn.1 fn.2 (DFrac.own (QpMul q.half sync.rfrac).half)
      (DFrac.own (QpMul q.half sync.rfrac).half) (dbFd K.p.ino) (wtRs C.pages fx) _
      (⊤ \ ↑(pagesN K.N)) _ rfl hosE (by intro ii T h _; cases h; exact ⟨eofl, rfl⟩) $$ Hos Heof Hacc
    icases HWr with ⟨%cw, HWr, %hcw⟩
    have hcw' : cw = true := hcw (by omega)
    subst hcw'
    rw [show wtPre mv 2 = wtMetas mv from rfl]
    rw [← fileOwn_eq] at *
    wp_apply wp_CopyN w Wr true (bs₀ ++ wtMetas mv) sr _ (W64 8192) _
      iprop(os.ownFile f fn.1 fn.2 (DFrac.own (QpMul q.half sync.rfrac).half) ∗
        osFd fn.1 (DFrac.own (QpMul q.half sync.rfrac).half) (dbFd K.p.ino) ∗
        (k ↪[K.B.rds]{DFrac.own q.half.half} (⟨v, fx⟩ : RdInfo) ∗
          ghostVar K.B.map (QpMul q.half sync.rfrac).half.half (some (v.base, l) : MapSt)))
      (fun i x => ∀ b, os.heldByte (wtRs C.pages fx) i b → x = b) hplain (by rw [hszZ]; omega)
      $$ [HWr Hsr Hfo Hfd Hk Hmap] as %wn %cerr ⟨%c', %ys, ⟨Hfo, Hfd, Hk, Hmap⟩, HWr, %Hys⟩
    · rw [← fileOwn_eq]; simp only; iframe; iframe #
    try wp_auto
    obtain ⟨hwnl, hylen, hHd, herr, hc'⟩ := Hys
    have hc'' : c' = true := by rcases hc' with h | ⟨h, -⟩ <;> exact h
    subst hc''
    -- the reader back
    ihave Ht2 := Hcl $$ Hwf Hme Hmv Hdb Hk [Hff Hfo Hfd] Hmap
    · iunfold rdxFile
      iexists f
      iframe Hff
      isplitr
      · ipureintro; exact hfn
      iexists (K.t0, K.p.ino)
      iframe Hti0
      iexists fn
      rw [fileOwn_eq]; simp only
      iframe
    ihave Ht2 : boltTx tx γ q.half (TxView.ro D) $$ [Ht2]
    · iunfold boltTx
      iapply (boltTx_rdTx _ _ tx _ _ rfl).2
      iexists db'
      iframe; iframe #
    ihave Ht := ((boltTx_fractional (GF := GF) tx γ (TxView.ro D)).fractional q.half q.half).2
      $$ [Ht1 Ht2]
    · iframe
    have hqq : boltTx (GF := GF) tx γ (q.half + q.half) (TxView.ro D) ⊢ boltTx tx γ q (TxView.ro D) := by
      rw [Qp.half_add_half]
    ihave Ht := hqq $$ Ht
    rcases cerr with ci | _
    · -- the copy failed
      try wp_auto
      iapply HΦ
      iexists (wtMetas mv ++ ys)
      rw [← List.append_assoc]
      iframe
      iright; ipureintro; simp
    · -- the copy succeeded
      have hyl : ys.length = (C.hwm - 2) * 4096 := by rw [← hsz]; exact herr.1 rfl
      try wp_auto
      iapply HΦ
      iexists (wtMetas mv ++ ys)
      rw [← List.append_assoc]
      iframe
      ileft
      have hD : D = treeData C := by
        have h := congrArg TxView.base hTv
        simp only [TxView.ro] at h
        rw [h, hvC]; rfl
      have hy : ∀ j x, ys[j]? = some x → ∀ b, os.heldByte (wtRs C.pages fx) (8192 + j) b → x = b :=
        fun j x hx => hHd j x hx
      obtain ⟨hpgb, hys, hfl⟩ := wt_bridge C fx ys hCtree hfxC hyl hy
      ihave %htx := preceipt_lt _ $$ Hrc
      have htx2 : C.txid < 2 ^ 62 := by have := Ht0.1.2; omega
      rw [hmvC, hD]
      obtain ⟨-, -, himg, hm, -, -, htxw, -⟩ :=
        writeTo_image C (wtG ys) ys hCok hCtree hCtx1 hyl hpgb hys hfl
      isplitr
      · ipureintro
        refine ⟨rfl, ?_⟩
        unfold boltImage
        exact writeTo_fileOK C (wtG ys) ys hCok hCtree hCtx1 htx2 (by omega) hyl hpgb hys hfl
      unfold boltImageRcpt
      iapply fileRcpt_intro _ (wtSt C) himg hm
      rw [htxw]; iexact Hrc

end proof

end bbolt
end EtcdGrove
end Perennial
