module
public import Spec.go_etcd_io.bbolt.DB__allocate
public import Spec.go_etcd_io.bbolt.DB__mmap
public import Spec.go_etcd_io.bbolt.DB__growSize
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.sync.Pool__Get
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetOverflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetId
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetPgid
public import Proof.go_etcd_io.bbolt.DBAlloc
public import Proof.go_etcd_io.bbolt.AllocPage
public import Proof.go_etcd_io.bbolt.MmapSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

theorem alloc_cnat (count : w64) (h0 : 0 < sint.Z count) :
    (uint.nat count : Int) = sint.Z count := by word

theorem alloc_mul (count : w64) (ps : Nat) (h0 : 0 < sint.Z count)
    (h : sint.Z count * ps < 2 ^ 47) (hps : 1 ≤ ps) :
    sint.Z (count * W64 (ps : Int)) = sint.Z count * ps := by
  have : (ps : Int) < 2 ^ 47 := by
    have : (1 : Int) * ps ≤ sint.Z count * ps := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  have h1 : uint.Z count = sint.Z count := by word
  have h2 : uint.Z (W64 (ps : Int)) = ps := by word
  have hlt : uint.Z count * uint.Z (W64 (ps : Int)) < 2 ^ 64 := by rw [h1, h2]; omega
  have h3 := word.unsigned_mul_nowrap count (W64 (ps : Int)) hlt
  have h5 : uint.Z (count * W64 (ps : Int)) < 2 ^ 63 := by rw [h3, h1, h2]; omega
  have h4 : sint.Z (count * W64 (ps : Int)) = uint.Z (count * W64 (ps : Int)) := by word
  rw [h4, h3, h1, h2]

theorem alloc_unat (x : w64) : (uint.nat x : Int) = uint.Z x := by word

theorem alloc_ov (count : w64) (h0 : 0 < sint.Z count) (h32 : sint.Z count ≤ 2 ^ 32) :
    W32 (sint.Z (count - W64 1)) = W32 ((uint.nat count - 1 : Nat) : Int) := by
  have h1 : sint.Z (count - W64 1) = sint.Z count - 1 := by word
  have h2 : ((uint.nat count - 1 : Nat) : Int) = sint.Z count - 1 := by
    have := alloc_cnat count h0; omega
  rw [h1, h2]

theorem alloc_hwm (pg count : w64) (ps : Nat) (hpg : uint.Z pg * ps < 2 ^ 48)
    (h0 : 0 < sint.Z count) (hc : sint.Z count * ps < 2 ^ 47) (hps : 80 ≤ ps)
    (hps32 : ps < 2 ^ 32) :
    uint.Z (pg + count) = uint.Z pg + sint.Z count ∧
    sint.Z ((pg + count + W64 1) * W64 (ps : Int)) = (uint.Z pg + sint.Z count + 1) * ps := by
  have h1 : uint.Z count = sint.Z count := by word
  have hpg0 := (word.unsigned_range pg).1
  have hpgl : uint.Z pg < 2 ^ 48 := by
    have : uint.Z pg * 1 ≤ uint.Z pg * ps := Int.mul_le_mul_of_nonneg_left (by omega) hpg0
    omega
  have hcl : sint.Z count < 2 ^ 47 := by
    have : sint.Z count * 1 ≤ sint.Z count * ps := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hadd : uint.Z (pg + count) = uint.Z pg + sint.Z count := by
    rw [word.unsigned_add_nowrap pg count (by omega), h1]
  have hadd1 : uint.Z (pg + count + W64 1) = uint.Z pg + sint.Z count + 1 := by
    have hone : uint.Z (W64 1) = 1 := by decide
    rw [word.unsigned_add_nowrap _ _ (by rw [hadd, hone]; omega), hadd, hone]
  have h2 : uint.Z (W64 (ps : Int)) = ps := by word
  have hexp : (uint.Z pg + sint.Z count + 1) * ps = uint.Z pg * ps + sint.Z count * ps + ps := by
    simp only [Int.add_mul, Int.one_mul]
  have hlt : uint.Z (pg + count + W64 1) * uint.Z (W64 (ps : Int)) < 2 ^ 64 := by
    rw [hadd1, h2, hexp]; omega
  have h3 := word.unsigned_mul_nowrap _ _ hlt
  have h5 : uint.Z ((pg + count + W64 1) * W64 (ps : Int)) < 2 ^ 63 := by
    rw [h3, hadd1, h2, hexp]; omega
  refine ⟨hadd, ?_⟩
  have h4 : sint.Z ((pg + count + W64 1) * W64 (ps : Int)) =
      uint.Z ((pg + count + W64 1) * W64 (ps : Int)) := by word
  rw [h4, h3, hadd1, h2]

theorem alloc_sz (n : Nat) (h : n < 2 ^ 63) : sint.Z (W64 (n : Int)) = n := by word

theorem alloc_ps (n : Nat) (h : n < 2 ^ 63) : uint.Z (W64 (n : Int)) = n := by word

theorem alloc_wsz (sz : w64) (h : 0 ≤ sint.Z sz) : sz = W64 ((sint.nat sz : Nat) : Int) := by
  rw [show sint.nat sz = (sint.Z sz).toNat from rfl]
  rw [Int.toNat_of_nonneg h]
  word

set_option maxHeartbeats 4000000 in
theorem DB.allocate.wp_proof (hGet : sync.Pool.Get.spec (GF := GF) (hG := hG))
    (hSetOv : _root_.Perennial.EtcdGrove.bbolt.Page.SetOverflow.spec (GF := GF) (hG := hG))
    (hSetId : _root_.Perennial.EtcdGrove.bbolt.Page.SetId.spec (GF := GF) (hG := hG))
    (hId : _root_.Perennial.EtcdGrove.bbolt.Page.Id.spec (GF := GF) (hG := hG))
    (hPgid : _root_.Perennial.EtcdGrove.bbolt.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hSetPgid : _root_.Perennial.EtcdGrove.bbolt.Meta.SetPgid.spec (GF := GF) (hG := hG))
    (hmmapSize : DB.mmapSize.spec (GF := GF) (hG := hG))
    (hgrowSize : DB.growSize.spec (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hErrorf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG))
    (hmmap : DB.mmap.spec (GF := GF) (hG := hG)) :
    DB.allocate.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ w ml mv WR WR' txid count hAlloc hw hc0 hc32 hcps hpg hhwm hD
  wp_start as ⟨Hdb, Hwd, Hwp, Hwfl, Hmf, Hmv, HWR⟩
  simp only [ownDB]
  iNamed Hdb
  have hok := Hok
  obtain ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩ := Hdv
  have hps80 : 80 ≤ σ.ps := hok.1
  have hps32 : σ.ps < 2 ^ 32 := hok.2.1
  have hcnat := alloc_cnat count hc0
  have hmul := alloc_mul count σ.ps hc0 hcps (by omega)
  have hmuln : sint.nat (count * W64 (σ.ps : Int)) = uint.nat count * σ.ps := by
    rw [show sint.nat (count * W64 (σ.ps : Int)) = (sint.Z (count * W64 (σ.ps : Int))).toNat
      from rfl, hmul, ← hcnat]
    exact (Int.natCast_mul _ _) ▸ Int.toNat_natCast (uint.nat count * σ.ps)
  try wp_auto
  have hN : 16 ≤ uint.nat count * σ.ps := by
    have h1 : 1 ≤ uint.nat count := by word
    have := Nat.mul_le_mul_right σ.ps h1
    omega
  by_cases hc1 : count = W64 1
  all_goals first
    | (rw [decide_eq_true hc1]
       try wp_auto
       wp_apply hGet _ _ $$ [Hpool] as %v Hv
       · iexact Hpool
       simp only [pageBuf]
       icases Hv with ⟨%s, %Hvs, Hs⟩
       subst Hvs
       try wp_auto
       icases (ownSlice_bytes s _ _ (by simp; omega)).1 $$ Hs with ⟨Hs, %Hslen⟩
       have hlen : uint.nat count * σ.ps = σ.ps := by rw [hc1]; simp
       ihave Hs : bytesPointsto s.ptr (DFrac.own 1) (List.replicate (uint.nat count * σ.ps) (W8 0))
         $$ [Hs]
       · rw [hlen]; iexact Hs
       have hslen : 0 < sint.Z s.len := by
         have := Hslen; simp only [List.length_replicate] at this; omega)
    | (rw [decide_eq_false hc1]
       try wp_auto
       wp_apply wp_slice_make2 (V := w8) as %s ⟨Hs, -⟩
       · ipureintro; rw [hmul]; exact Int.mul_nonneg (by omega) (by omega)
       try wp_auto
       rw [hmuln]
       rw [show (zero_val w8 : w8) = W8 0 from rfl]
       icases (ownSlice_bytes s _ _ (by simp; omega)).1 $$ Hs with ⟨Hs, %Hslen⟩
       have hslen : 0 < sint.Z s.len := by
         have := Hslen; simp only [List.length_replicate] at this; omega)
  all_goals
    icases persistent_entails_left (bytesPointsto_car s.ptr _ _ (by simp; omega)) $$ Hs
      with ⟨Hs, %Hcar⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧
      sint.Z (W64 0) < sint.Z s.len from ⟨by decide, by simpa using hslen⟩))]
    unfold sliceIndexRef
    rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
    try wp_auto
    icases (zero_page (hG := hG) s.ptr _ Hcar hN).1 $$ Hs with ⟨Hpg, Hz⟩
    wp_apply hSetOv s.ptr _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    rw [Hfl']
    simp only [FLImpl.iface, interface.mkOk]
    try wp_auto
    isimp only [ownFL] at Hfl
    icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
    icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
    ihave Hfl : ownFL I fls σ.fl $$ [Hsh Hown]
    · simp only [ownFL]; iframe; iframe #
    wp_apply hAlloc fls σ.fl txid count hc0 $$ [Hfl] as %r Hr
    · iframe
    try wp_auto
    wp_apply hSetId s.ptr _ r $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hId s.ptr _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    have hsn : sint.nat count = uint.nat count := by
      rw [show sint.nat count = (sint.Z count).toNat from rfl, ← hcnat]; simp
    simp only
    icases Hr with (⟨%Hr0, Hfl⟩ | ⟨%Hcan, Hfl⟩)
    · -- none free: the page at the high-water mark
      subst Hr0
      rw [decide_eq_true rfl]
      try wp_auto
      isimp only [dbPlain] at Hplain
      iNamed Hplain
      rw [Hrw]
      try wp_auto
      wp_apply hPgid ml mv _ $$ [Hmv] as Hmv
      · iframe
      try wp_auto
      wp_apply hSetId s.ptr _ _ $$ [Hpg] as Hpg
      · iframe
      try wp_auto
      wp_apply hId s.ptr _ _ $$ [Hpg] as Hpg
      · iframe
      try wp_auto
      by_cases hms : sint.Z (W64 0) < sint.Z dv.MaxSize'
      · rw [decide_eq_true hms]
        try wp_auto
        wp_apply hmmapSize dbl (W64 (σ.ps : Int)) DFrac.discard _ (by word) (by word) $$ [Hps]
          as %r1 %e1 ⟨-, %He1⟩
        · iexact Hps
        try wp_auto
        split at He1
        · -- the size fits: Linux, so the allocation grows by `growSize`
          obtain ⟨rfl, hr1⟩ := He1
          try wp_auto
          rw [GOOSLinux.goos]
          try wp_auto
          wp_apply hgrowSize dbl _ _ _ _ $$ [AllocSize] as AllocSize
          · iframe
          try wp_auto
          generalize hna : (if sint.Z r1 ≤ sint.Z dv.AllocSize' then r1
            else (mv.pgid' + count + W64 1) * W64 (σ.ps : Int) + dv.AllocSize') = na
          by_cases hgt : sint.Z dv.MaxSize' < sint.Z na
          · -- beyond the maximum size: log it, an error
            rw [decide_eq_true hgt]
            try wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl ⟨Hsl, -⟩
            try wp_auto
            wp_apply hLogger dbl DFrac.discard dv.logger' dl Hdbl $$ [Hlogger Hdl] as -
            · iframe; iframe #
            have Hd : (if dv.logger' = interface.nil then discardIface dl else dv.logger') =
                discardIface dl := by
              rcases Hlog with h | h <;> rw [h] <;> simp [discardIface, interface.mkOk]
            rw [Hd]
            try wp_auto
            wp_apply hErrorf dl _ _ $$ [Hdlok]
            · iframe; iexact Hdlok
            try wp_auto
            ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
            · iPkgInit
            icases bboltError_access errors.ErrMaxSizeReached (by simp [bboltErrorNames]) $$ Hei
              with ⟨%e, #He, %Hne⟩
            try wp_auto
            iapply HΦ
            ileft
            isplitr
            · ipureintro; obtain ⟨t, p, rfl⟩ := Hne; exact fun h => by cases h
            isplitr [Hwd Hwp Hwfl Hmf Hmv HWR]
            · try simp only [ownDB]
              iexists dv, fls, v0, v1, dl
              isplitr
              · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
              isplitr
              · ipureintro; exact Hok
              isplitr
              · ipureintro; exact Hdr
              ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
              · simp only [dbPlain]; rw [Hrw]; iframe
              rw [Hfl']
              try simp only [FLImpl.iface, interface.mkOk]
              iframe
              iframe #
              try (ipureintro; exact Hlog)
            · iframe
          · rw [decide_eq_false hgt]
            try wp_auto
            have hmz := alloc_hwm mv.pgid' count σ.ps hpg hc0 hcps hps80 hps32
            have hdsz : sint.Z dv.datasz' = σ.sz := by rw [Hdsz]; exact alloc_sz σ.sz (by have := Hok.2.2.2.1.1; omega)
            by_cases hge : sint.Z dv.datasz' ≤ sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int))
            · rw [decide_eq_true hge]
              try wp_auto
              -- too small: remap (the writer dereferenced, no reader open)
              have hrw0 : σ.rwtx ≠ null := fun h =>
                absurd ((Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 h) (by rw [hw]; exact Option.some_ne_none w)
              have hrs := Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              ihave Hmmaph := (show ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders -
                  σ.readers.size) (), sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap))
                  ⊢ sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap) ∗
                    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) (),
                      sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap)) from by
                rw [show Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size =
                  (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) + 1 by omega, List.replicate_succ]
                exact BigSepL.bigSepL_cons.1) $$ Hmmaph
              icases Hmmaph with ⟨Hmh, Hmmaph⟩
              rw [Hfile']
              wp_apply hmmap dbl σ.file σ.fd σ.bs dv.logger' dl (W64 (σ.ps : Int)) dv.MaxSize' dv.MmapFlags'
                σ.rwtx (DFrac.own 1) dv.dataref' σ.data dv.datasz' dv.meta0' dv.meta1' (some (σ.data, σ.sz))
                σ.sz γ.mmap σ.readers iprop(WR ∗ pagesView σ.data σ.ps w.q w.pages)
                iprop(WR' ∗ pagesView σ.data σ.ps w.q w.pages) WR' _ Hdbl Hok.2.2.2.1.2 (by word) (by word)
                (by rw [hmz.2]; exact Int.mul_nonneg (by have := (word.unsigned_range mv.pgid').1; omega) (by omega))
                (by rw [hmz.2]; simp only [Int.add_mul, Int.one_mul]; omega) Hlog
                (Or.inr ⟨by rw [Hdr]; exact loc_ne_null_of_car _ Hok.2.2.2.2.1, by rw [Hdr], by rw [Hdr],
                  by rw [Hdr]⟩)
                (fun h => absurd h hrw0) (fun _ => hD hrw0)
                $$ [Hmh Htoks HWR Hwp Hdata Hwd Hslots Htail file MaxSize rwtx MmapFlags dataref datasz meta0
                  meta1 Hbytes Hmap]
                as %e Hres
              · iframe
                iframe #
                iintro %hM ⟨HK, HPV⟩
                have hf := fields_whole σ v0 v1 Hok hM w hw
                iframe
                isplitl [Hdata Hwd]
                · iapply (pointsto_split' _ _ σ.frem w.q 1 hf.symm).2; iframe
                iapply remap_gather σ v0 v1 Hok hM w hw
                iframe
              icases Hres with ⟨%hM, file, MaxSize, Hml, rwtx, MmapFlags, Hbytes, Hmh, Hres⟩
              icases Hres with (⟨%He, HWR, Hwand, dataref, datasz, meta0, meta1, Hmap⟩ |
                ⟨%He, HK, %dp', %ds', %m0', %m1', %m', %n', dataref, Hd, datasz, meta0, meta1, Hmap, Hr⟩ |
                ⟨%He, HK, %b, %sz, %v0', %v1', %Hb, dataref, Hd, datasz, meta0, meta1, Hmap, Hr⟩)
              · -- an early error of `db.mmap`: the database is lost (its cells are in the wand)
                cases e with
                | nil => exact absurd rfl He.1
                | ok ei =>
                  try wp_auto
                  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
                  · iPkgInit
                  icases bboltError_access errors.ErrMaxSizeReached (by simp [bboltErrorNames]) $$ Hei
                    with ⟨%em, #Hem, %Hne⟩
                  obtain ⟨t', p', rfl⟩ := Hne
                  try wp_auto
                  by_cases hty : ei.ty = go.GoType.PointerType t'
                  · rw [if_pos hty]
                    obtain ⟨l, hl⟩ := errWF_ptr_val He.2 rfl hty
                    rcases ei with ⟨ety, ev⟩
                    simp only at hty hl
                    subst hty hl
                    try wp_auto
                    by_cases hlp : l = p'
                    · rw [decide_eq_true hlp]
                      try wp_auto
                      iapply HΦ
                      iright; ileft
                      isplitr
                      · ipureintro; intro h; cases h
                      iframe
                      try (ileft; icases HWR with ⟨HWR, -⟩; iexact HWR)
                    · rw [decide_eq_false hlp]
                      try wp_auto
                      wp_apply wp_slice_literal
                      isplitr
                      · ipureintro; rfl
                      iintro %sl ⟨Hsl, -⟩
                      wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                      try wp_auto
                      iapply HΦ
                      iright; ileft
                      isplitr
                      · ipureintro; intro h; cases h
                      iframe
                      try (ileft; icases HWR with ⟨HWR, -⟩; iexact HWR)
                  · rw [if_neg hty]
                    try wp_auto
                    wp_apply wp_slice_literal
                    isplitr
                    · ipureintro; rfl
                    iintro %sl ⟨Hsl, -⟩
                    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                    try wp_auto
                    iapply HΦ
                    iright; ileft
                    isplitr
                    · ipureintro; intro h; cases h
                    iframe
                    try (ileft; icases HWR with ⟨HWR, -⟩; iexact HWR)

              · -- the mapping lost after the dereference
                cases e with
                | nil => exact absurd rfl He.1
                | ok ei =>
                  try wp_auto
                  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
                  · iPkgInit
                  icases bboltError_access errors.ErrMaxSizeReached (by simp [bboltErrorNames]) $$ Hei
                    with ⟨%em, #Hem, %Hne⟩
                  obtain ⟨t', p', rfl⟩ := Hne
                  try wp_auto
                  by_cases hty : ei.ty = go.GoType.PointerType t'
                  · rw [if_pos hty]
                    obtain ⟨l, hl⟩ := errWF_ptr_val He.2 rfl hty
                    rcases ei with ⟨ety, ev⟩
                    simp only at hty hl
                    subst hty hl
                    try wp_auto
                    by_cases hlp : l = p'
                    · rw [decide_eq_true hlp]
                      try wp_auto
                      iapply HΦ
                      iright; ileft
                      isplitr
                      · ipureintro; intro h; cases h
                      iframe
                      try (iright; iexact HK)
                    · rw [decide_eq_false hlp]
                      try wp_auto
                      wp_apply wp_slice_literal
                      isplitr
                      · ipureintro; rfl
                      iintro %sl ⟨Hsl, -⟩
                      wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                      try wp_auto
                      iapply HΦ
                      iright; ileft
                      isplitr
                      · ipureintro; intro h; cases h
                      iframe
                      try (iright; iexact HK)
                  · rw [if_neg hty]
                    try wp_auto
                    wp_apply wp_slice_literal
                    isplitr
                    · ipureintro; rfl
                    iintro %sl ⟨Hsl, -⟩
                    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                    try wp_auto
                    iapply HΦ
                    iright; ileft
                    isplitr
                    · ipureintro; intro h; cases h
                    iframe
                    try (iright; iexact HK)
              · -- remapped
                subst He
                obtain ⟨Hbl, Hbc, Hbp, Hmsz, -⟩ := Hb
                have hps0 : 0 < uint.Z (W64 (σ.ps : Int)) := by rw [alloc_ps σ.ps (by omega)]; omega
                have hge' := mmapSizeOf_ge _ _ _ (by have := Int.le_max_left (σ.bs.length : Int) (sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int))); omega) hps0 Hmsz
                have hle' := mmapSizeOf_le _ _ _ Hmsz
                have hminsz := hmz.2
                have hszn : ((sint.nat sz : Nat) : Int) = sint.Z sz := by
                  rw [show sint.nat sz = (sint.Z sz).toNat from rfl]; omega
                have hsz : σ.sz ≤ sint.nat sz := by
                  have := Int.le_max_right (σ.bs.length : Int) (sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int)))
                  rw [hdsz] at hge; omega
                have hmax : sint.nat sz ≤ 281474976710655 := by omega
                have hf := fields_whole σ v0 v1 Hok hM w hw
                try wp_auto
                icases (remap_carve σ v0 v1 Hok hM w hw b.ptr (sint.nat sz) hsz) $$ Hr with ⟨Hslots, Htail, Hwp⟩
                icases (pointsto_split' _ _ σ.frem w.q 1 hf.symm).1 $$ Hd with ⟨Hdata, Hwd⟩
                ihave Htoks : ([∗map] _k ↦ _r ∈ σ.readers, mmapTok (GF := GF) γ.mmap sync.rfrac) $$ []
                · rw [hM]
                  iapply (BigSepM.bigSepM_empty (PROP := IProp GF) (M := GMap Nat)
                    (Φ := fun (_ : Nat) (_ : Reader) => mmapTok (GF := GF) γ.mmap sync.rfrac)).2
                  itrivial
                ihave Hmmaph := (show sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap) ∗
                      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) (),
                        sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap)) ⊢
                    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size) (),
                      sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap)) from by
                  rw [show Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size =
                    (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) + 1 by omega, List.replicate_succ,
                    Nat.add_sub_cancel]
                  exact (BigSepL.bigSepL_cons (Φ := fun (_ : Nat) (_ : Unit) =>
                    sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap))).2)
                  $$ [Hmh Hmmaph]
                · iframe
                try rw [Hrw]
                try wp_auto
                wp_apply hPgid ml mv _ $$ [Hmv] as Hmv
                · iframe
                try wp_auto
                wp_apply hSetPgid ml mv _ $$ [Hmv] as Hmv
                · iframe
                try wp_auto
                iapply HΦ
                iright; iright
                isplitr
                · ipureintro; rfl
                iexists σ.remap b.ptr (sint.nat sz), { mv with pgid' := mv.pgid' + count }, mv.pgid'
                isplitr
                · ipureintro
                  have h2 := writer_hwm_ge2 σ v0 v1 Hok w hw
                  have hu := alloc_unat mv.pgid'
                  refine ⟨by omega, fun k hk => writer_not_covered_above σ v0 v1 Hok w hw _ (by omega), rfl,
                    by (try simp only); rw [hmz.1]; omega, ?_, by (try simp only); rw [hmz.1]; omega,
                    Or.inr ⟨rfl, by (try simp only); rw [hmz.1]; omega, Or.inr ⟨b.ptr, sint.nat sz, hsz, rfl⟩⟩⟩
                  (try simp only); rw [hmz.1]
                  have h3 : (uint.Z mv.pgid' + sint.Z count + 1) * σ.ps =
                      (uint.Z mv.pgid' + sint.Z count) * σ.ps + σ.ps := by simp only [Int.add_mul, Int.one_mul]
                  have := Int.le_max_right (σ.bs.length : Int) (sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int)))
                  try simp only [DBState.remap.proj_ps]
                  omega
                isplitr [Hwd Hwp Hwfl Hmf Hmv HK Hpg Hz]
                · try simp only [ownDB]
                  iexists { dv with dataref' := b, data' := b.ptr, datasz' := sz, meta0' := b.ptr +ₗ 16, meta1' := b.ptr +ₗ (uint.Z (W64 (σ.ps : Int)) + 16) }, fls, v0, v1, dl
                  have hpsz : uint.Z (W64 (σ.ps : Int)) = σ.ps := alloc_ps σ.ps (by omega)
                  isplitr
                  · ipureintro
                    refine ⟨rfl, Hps', alloc_wsz sz (by omega), rfl, ?_, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
                    show b.ptr +ₗ (uint.Z (W64 (σ.ps : Int)) + 16) = b.ptr +ₗ ((σ.ps + 16 : Nat) : Int)
                    rw [hpsz]; push_cast; rfl
                  isplitr
                  · ipureintro; exact dbOK_remap σ v0 v1 Hok b.ptr (sint.nat sz) hsz hmax Hbp
                  isplitr
                  · ipureintro
                    show b = slice.mk b.ptr (W64 ((sint.nat sz : Nat) : Int)) (W64 ((sint.nat sz : Nat) : Int))
                    rw [← alloc_wsz sz (by omega)]
                    rcases b with ⟨bp, bl, bc⟩
                    simp only at Hbl Hbc ⊢
                    rw [Hbl, Hbc]
                  ihave Hplain : dbPlain dbl (DFrac.own 1) { dv with dataref' := b, data' := b.ptr, datasz' := sz, meta0' := b.ptr +ₗ 16, meta1' := b.ptr +ₗ (uint.Z (W64 (σ.ps : Int)) + 16) } $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
                  · simp only [dbPlain]; rw [Hrw, Hfile']; iframe
                  rw [Hfl']
                  try simp only [FLImpl.iface, interface.mkOk]
                  try simp only [DBState.remap.proj_data, DBState.remap.proj_ps, DBState.remap.proj_sz,
                    DBState.remap.proj_file, DBState.remap.proj_rwtx, DBState.remap.proj_fd,
                    DBState.remap.proj_bs, DBState.remap.proj_fl, DBState.remap.proj_readers,
                    DBState.remap.proj_rem, DBState.remap.proj_frem]
                  iframe
                  iframe #
                  try (ipureintro; exact Hlog)
                · iframe
                  try (isplitl [HK]; iright; iexact HK)
                  rw [alloc_ov count hc0 hc32] at *
                  iapply fresh_page (hG := hG) s.ptr mv.pgid' (uint.nat count) σ.ps Hcar (by omega) (by omega) hN
                  iframe
            · -- the mapping is large enough
              rw [decide_eq_false hge]
              try wp_auto
              try rw [Hrw]
              try wp_auto
              wp_apply hPgid ml mv _ $$ [Hmv] as Hmv
              · iframe
              try wp_auto
              wp_apply hSetPgid ml mv _ $$ [Hmv] as Hmv
              · iframe
              try wp_auto
              iapply HΦ
              iright; iright
              isplitr
              · ipureintro; rfl
              iexists σ, { mv with pgid' := mv.pgid' + count }, mv.pgid'
              isplitr
              · ipureintro
                have h2 := writer_hwm_ge2 σ v0 v1 Hok w hw
                have hu := alloc_unat mv.pgid'
                refine ⟨by omega, fun k hk => writer_not_covered_above σ v0 v1 Hok w hw _ (by omega), rfl,
                  by (try simp only); rw [hmz.1]; omega, by
                    (try simp only); rw [hmz.1]
                    have h3 : (uint.Z mv.pgid' + sint.Z count + 1) * σ.ps =
                        (uint.Z mv.pgid' + sint.Z count) * σ.ps + σ.ps := by simp only [Int.add_mul, Int.one_mul]
                    have := hmz.2; have := Hok.2.2.2.1.1; omega, by (try simp only); rw [hmz.1]; omega,
                  Or.inr ⟨rfl, by (try simp only); rw [hmz.1]; omega, Or.inl rfl⟩⟩
              isplitr [Hwd Hwp Hwfl Hmf Hmv HWR Hpg Hz]
              · try simp only [ownDB]
                iexists dv, fls, v0, v1, dl
                isplitr
                · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
                isplitr
                · ipureintro; exact Hok
                isplitr
                · ipureintro; exact Hdr
                ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
                · simp only [dbPlain]; rw [Hrw]; iframe
                rw [Hfl']
                try simp only [FLImpl.iface, interface.mkOk]
                iframe
                iframe #
                try (ipureintro; exact Hlog)
              · iframe
                isplitl [HWR]
                · ileft; iframe; ipureintro; rfl
                rw [alloc_ov count hc0 hc32] at *
                iapply fresh_page (hG := hG) s.ptr mv.pgid' (uint.nat count) σ.ps Hcar (by omega) (by omega) hN
                iframe
        · -- too large to map: an error
          cases e1 with
          | nil => exact absurd rfl He1.1
          | ok ei =>
            try wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl ⟨Hsl, -⟩
            wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
            try wp_auto
            iapply HΦ
            ileft
            isplitr
            · ipureintro; intro h; cases h
            isplitr [Hwd Hwp Hwfl Hmf Hmv HWR]
            · try simp only [ownDB]
              iexists dv, fls, v0, v1, dl
              isplitr
              · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
              isplitr
              · ipureintro; exact Hok
              isplitr
              · ipureintro; exact Hdr
              ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
              · simp only [dbPlain]; rw [Hrw]; iframe
              rw [Hfl']
              try simp only [FLImpl.iface, interface.mkOk]
              iframe
              iframe #
              try (ipureintro; exact Hlog)
            · iframe
      · rw [decide_eq_false hms]
        try wp_auto
        have hmz := alloc_hwm mv.pgid' count σ.ps hpg hc0 hcps hps80 hps32
        have hdsz : sint.Z dv.datasz' = σ.sz := by rw [Hdsz]; exact alloc_sz σ.sz (by have := Hok.2.2.2.1.1; omega)
        by_cases hge : sint.Z dv.datasz' ≤ sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int))
        · rw [decide_eq_true hge]
          try wp_auto
          -- too small: remap (the writer dereferenced, no reader open)
          have hrw0 : σ.rwtx ≠ null := fun h =>
            absurd ((Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 h) (by rw [hw]; exact Option.some_ne_none w)
          have hrs := Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          ihave Hmmaph := (show ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders -
              σ.readers.size) (), sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap))
              ⊢ sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap) ∗
                ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) (),
                  sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap)) from by
            rw [show Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size =
              (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) + 1 by omega, List.replicate_succ]
            exact BigSepL.bigSepL_cons.1) $$ Hmmaph
          icases Hmmaph with ⟨Hmh, Hmmaph⟩
          rw [Hfile']
          wp_apply hmmap dbl σ.file σ.fd σ.bs dv.logger' dl (W64 (σ.ps : Int)) dv.MaxSize' dv.MmapFlags'
            σ.rwtx (DFrac.own 1) dv.dataref' σ.data dv.datasz' dv.meta0' dv.meta1' (some (σ.data, σ.sz))
            σ.sz γ.mmap σ.readers iprop(WR ∗ pagesView σ.data σ.ps w.q w.pages)
            iprop(WR' ∗ pagesView σ.data σ.ps w.q w.pages) WR' _ Hdbl Hok.2.2.2.1.2 (by word) (by word)
            (by rw [hmz.2]; exact Int.mul_nonneg (by have := (word.unsigned_range mv.pgid').1; omega) (by omega))
            (by rw [hmz.2]; simp only [Int.add_mul, Int.one_mul]; omega) Hlog
            (Or.inr ⟨by rw [Hdr]; exact loc_ne_null_of_car _ Hok.2.2.2.2.1, by rw [Hdr], by rw [Hdr],
              by rw [Hdr]⟩)
            (fun h => absurd h hrw0) (fun _ => hD hrw0)
            $$ [Hmh Htoks HWR Hwp Hdata Hwd Hslots Htail file MaxSize rwtx MmapFlags dataref datasz meta0
              meta1 Hbytes Hmap]
            as %e Hres
          · iframe
            iframe #
            iintro %hM ⟨HK, HPV⟩
            have hf := fields_whole σ v0 v1 Hok hM w hw
            iframe
            isplitl [Hdata Hwd]
            · iapply (pointsto_split' _ _ σ.frem w.q 1 hf.symm).2; iframe
            iapply remap_gather σ v0 v1 Hok hM w hw
            iframe
          icases Hres with ⟨%hM, file, MaxSize, Hml, rwtx, MmapFlags, Hbytes, Hmh, Hres⟩
          icases Hres with (⟨%He, HWR, Hwand, dataref, datasz, meta0, meta1, Hmap⟩ |
            ⟨%He, HK, %dp', %ds', %m0', %m1', %m', %n', dataref, Hd, datasz, meta0, meta1, Hmap, Hr⟩ |
            ⟨%He, HK, %b, %sz, %v0', %v1', %Hb, dataref, Hd, datasz, meta0, meta1, Hmap, Hr⟩)
          · -- an early error of `db.mmap`: the database is lost (its cells are in the wand)
            cases e with
            | nil => exact absurd rfl He.1
            | ok ei =>
              try wp_auto
              ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
              · iPkgInit
              icases bboltError_access errors.ErrMaxSizeReached (by simp [bboltErrorNames]) $$ Hei
                with ⟨%em, #Hem, %Hne⟩
              obtain ⟨t', p', rfl⟩ := Hne
              try wp_auto
              by_cases hty : ei.ty = go.GoType.PointerType t'
              · rw [if_pos hty]
                obtain ⟨l, hl⟩ := errWF_ptr_val He.2 rfl hty
                rcases ei with ⟨ety, ev⟩
                simp only at hty hl
                subst hty hl
                try wp_auto
                by_cases hlp : l = p'
                · rw [decide_eq_true hlp]
                  try wp_auto
                  iapply HΦ
                  iright; ileft
                  isplitr
                  · ipureintro; intro h; cases h
                  iframe
                  try (ileft; icases HWR with ⟨HWR, -⟩; iexact HWR)
                · rw [decide_eq_false hlp]
                  try wp_auto
                  wp_apply wp_slice_literal
                  isplitr
                  · ipureintro; rfl
                  iintro %sl ⟨Hsl, -⟩
                  wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                  try wp_auto
                  iapply HΦ
                  iright; ileft
                  isplitr
                  · ipureintro; intro h; cases h
                  iframe
                  try (ileft; icases HWR with ⟨HWR, -⟩; iexact HWR)
              · rw [if_neg hty]
                try wp_auto
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %sl ⟨Hsl, -⟩
                wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                try wp_auto
                iapply HΦ
                iright; ileft
                isplitr
                · ipureintro; intro h; cases h
                iframe
                try (ileft; icases HWR with ⟨HWR, -⟩; iexact HWR)

          · -- the mapping lost after the dereference
            cases e with
            | nil => exact absurd rfl He.1
            | ok ei =>
              try wp_auto
              ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
              · iPkgInit
              icases bboltError_access errors.ErrMaxSizeReached (by simp [bboltErrorNames]) $$ Hei
                with ⟨%em, #Hem, %Hne⟩
              obtain ⟨t', p', rfl⟩ := Hne
              try wp_auto
              by_cases hty : ei.ty = go.GoType.PointerType t'
              · rw [if_pos hty]
                obtain ⟨l, hl⟩ := errWF_ptr_val He.2 rfl hty
                rcases ei with ⟨ety, ev⟩
                simp only at hty hl
                subst hty hl
                try wp_auto
                by_cases hlp : l = p'
                · rw [decide_eq_true hlp]
                  try wp_auto
                  iapply HΦ
                  iright; ileft
                  isplitr
                  · ipureintro; intro h; cases h
                  iframe
                  try (iright; iexact HK)
                · rw [decide_eq_false hlp]
                  try wp_auto
                  wp_apply wp_slice_literal
                  isplitr
                  · ipureintro; rfl
                  iintro %sl ⟨Hsl, -⟩
                  wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                  try wp_auto
                  iapply HΦ
                  iright; ileft
                  isplitr
                  · ipureintro; intro h; cases h
                  iframe
                  try (iright; iexact HK)
              · rw [if_neg hty]
                try wp_auto
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %sl ⟨Hsl, -⟩
                wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
                try wp_auto
                iapply HΦ
                iright; ileft
                isplitr
                · ipureintro; intro h; cases h
                iframe
                try (iright; iexact HK)
          · -- remapped
            subst He
            obtain ⟨Hbl, Hbc, Hbp, Hmsz, -⟩ := Hb
            have hps0 : 0 < uint.Z (W64 (σ.ps : Int)) := by rw [alloc_ps σ.ps (by omega)]; omega
            have hge' := mmapSizeOf_ge _ _ _ (by have := Int.le_max_left (σ.bs.length : Int) (sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int))); omega) hps0 Hmsz
            have hle' := mmapSizeOf_le _ _ _ Hmsz
            have hminsz := hmz.2
            have hszn : ((sint.nat sz : Nat) : Int) = sint.Z sz := by
              rw [show sint.nat sz = (sint.Z sz).toNat from rfl]; omega
            have hsz : σ.sz ≤ sint.nat sz := by
              have := Int.le_max_right (σ.bs.length : Int) (sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int)))
              rw [hdsz] at hge; omega
            have hmax : sint.nat sz ≤ 281474976710655 := by omega
            have hf := fields_whole σ v0 v1 Hok hM w hw
            try wp_auto
            icases (remap_carve σ v0 v1 Hok hM w hw b.ptr (sint.nat sz) hsz) $$ Hr with ⟨Hslots, Htail, Hwp⟩
            icases (pointsto_split' _ _ σ.frem w.q 1 hf.symm).1 $$ Hd with ⟨Hdata, Hwd⟩
            ihave Htoks : ([∗map] _k ↦ _r ∈ σ.readers, mmapTok (GF := GF) γ.mmap sync.rfrac) $$ []
            · rw [hM]
              iapply (BigSepM.bigSepM_empty (PROP := IProp GF) (M := GMap Nat)
                (Φ := fun (_ : Nat) (_ : Reader) => mmapTok (GF := GF) γ.mmap sync.rfrac)).2
              itrivial
            ihave Hmmaph := (show sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap) ∗
                  ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) (),
                    sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap)) ⊢
                ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size) (),
                  sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap)) from by
              rw [show Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size =
                (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) + 1 by omega, List.replicate_succ,
                Nat.add_sub_cancel]
              exact (BigSepL.bigSepL_cons (Φ := fun (_ : Nat) (_ : Unit) =>
                sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap))).2)
              $$ [Hmh Hmmaph]
            · iframe
            try rw [Hrw]
            try wp_auto
            wp_apply hPgid ml mv _ $$ [Hmv] as Hmv
            · iframe
            try wp_auto
            wp_apply hSetPgid ml mv _ $$ [Hmv] as Hmv
            · iframe
            try wp_auto
            iapply HΦ
            iright; iright
            isplitr
            · ipureintro; rfl
            iexists σ.remap b.ptr (sint.nat sz), { mv with pgid' := mv.pgid' + count }, mv.pgid'
            isplitr
            · ipureintro
              have h2 := writer_hwm_ge2 σ v0 v1 Hok w hw
              have hu := alloc_unat mv.pgid'
              refine ⟨by omega, fun k hk => writer_not_covered_above σ v0 v1 Hok w hw _ (by omega), rfl,
                by (try simp only); rw [hmz.1]; omega, ?_, by (try simp only); rw [hmz.1]; omega,
                Or.inr ⟨rfl, by (try simp only); rw [hmz.1]; omega, Or.inr ⟨b.ptr, sint.nat sz, hsz, rfl⟩⟩⟩
              (try simp only); rw [hmz.1]
              have h3 : (uint.Z mv.pgid' + sint.Z count + 1) * σ.ps =
                  (uint.Z mv.pgid' + sint.Z count) * σ.ps + σ.ps := by simp only [Int.add_mul, Int.one_mul]
              have := Int.le_max_right (σ.bs.length : Int) (sint.Z ((mv.pgid' + count + W64 1) * W64 (σ.ps : Int)))
              try simp only [DBState.remap.proj_ps]
              omega
            isplitr [Hwd Hwp Hwfl Hmf Hmv HK Hpg Hz]
            · try simp only [ownDB]
              iexists { dv with dataref' := b, data' := b.ptr, datasz' := sz, meta0' := b.ptr +ₗ 16, meta1' := b.ptr +ₗ (uint.Z (W64 (σ.ps : Int)) + 16) }, fls, v0, v1, dl
              have hpsz : uint.Z (W64 (σ.ps : Int)) = σ.ps := alloc_ps σ.ps (by omega)
              isplitr
              · ipureintro
                refine ⟨rfl, Hps', alloc_wsz sz (by omega), rfl, ?_, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
                show b.ptr +ₗ (uint.Z (W64 (σ.ps : Int)) + 16) = b.ptr +ₗ ((σ.ps + 16 : Nat) : Int)
                rw [hpsz]; push_cast; rfl
              isplitr
              · ipureintro; exact dbOK_remap σ v0 v1 Hok b.ptr (sint.nat sz) hsz hmax Hbp
              isplitr
              · ipureintro
                show b = slice.mk b.ptr (W64 ((sint.nat sz : Nat) : Int)) (W64 ((sint.nat sz : Nat) : Int))
                rw [← alloc_wsz sz (by omega)]
                rcases b with ⟨bp, bl, bc⟩
                simp only at Hbl Hbc ⊢
                rw [Hbl, Hbc]
              ihave Hplain : dbPlain dbl (DFrac.own 1) { dv with dataref' := b, data' := b.ptr, datasz' := sz, meta0' := b.ptr +ₗ 16, meta1' := b.ptr +ₗ (uint.Z (W64 (σ.ps : Int)) + 16) } $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
              · simp only [dbPlain]; rw [Hrw, Hfile']; iframe
              rw [Hfl']
              try simp only [FLImpl.iface, interface.mkOk]
              try simp only [DBState.remap.proj_data, DBState.remap.proj_ps, DBState.remap.proj_sz,
                DBState.remap.proj_file, DBState.remap.proj_rwtx, DBState.remap.proj_fd,
                DBState.remap.proj_bs, DBState.remap.proj_fl, DBState.remap.proj_readers,
                DBState.remap.proj_rem, DBState.remap.proj_frem]
              iframe
              iframe #
              try (ipureintro; exact Hlog)
            · iframe
              try (isplitl [HK]; iright; iexact HK)
              rw [alloc_ov count hc0 hc32] at *
              iapply fresh_page (hG := hG) s.ptr mv.pgid' (uint.nat count) σ.ps Hcar (by omega) (by omega) hN
              iframe
        · -- the mapping is large enough
          rw [decide_eq_false hge]
          try wp_auto
          try rw [Hrw]
          try wp_auto
          wp_apply hPgid ml mv _ $$ [Hmv] as Hmv
          · iframe
          try wp_auto
          wp_apply hSetPgid ml mv _ $$ [Hmv] as Hmv
          · iframe
          try wp_auto
          iapply HΦ
          iright; iright
          isplitr
          · ipureintro; rfl
          iexists σ, { mv with pgid' := mv.pgid' + count }, mv.pgid'
          isplitr
          · ipureintro
            have h2 := writer_hwm_ge2 σ v0 v1 Hok w hw
            have hu := alloc_unat mv.pgid'
            refine ⟨by omega, fun k hk => writer_not_covered_above σ v0 v1 Hok w hw _ (by omega), rfl,
              by (try simp only); rw [hmz.1]; omega, by
                (try simp only); rw [hmz.1]
                have h3 : (uint.Z mv.pgid' + sint.Z count + 1) * σ.ps =
                    (uint.Z mv.pgid' + sint.Z count) * σ.ps + σ.ps := by simp only [Int.add_mul, Int.one_mul]
                have := hmz.2; have := Hok.2.2.2.1.1; omega, by (try simp only); rw [hmz.1]; omega,
              Or.inr ⟨rfl, by (try simp only); rw [hmz.1]; omega, Or.inl rfl⟩⟩
          isplitr [Hwd Hwp Hwfl Hmf Hmv HWR Hpg Hz]
          · try simp only [ownDB]
            iexists dv, fls, v0, v1, dl
            isplitr
            · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
            isplitr
            · ipureintro; exact Hok
            isplitr
            · ipureintro; exact Hdr
            ihave Hplain : dbPlain dbl (DFrac.own 1) dv $$ [StrictMode NoSync NoFreelistSync FreelistType NoGrowSync PreLoadFreelist MmapFlags MaxBatchSize MaxBatchDelay AllocSize MaxSize path openFile file dataref datasz meta0 meta1 opened rwtx stats batch ops readOnly]
            · simp only [dbPlain]; rw [Hrw]; iframe
            rw [Hfl']
            try simp only [FLImpl.iface, interface.mkOk]
            iframe
            iframe #
            try (ipureintro; exact Hlog)
          · iframe
            isplitl [HWR]
            · ileft; iframe; ipureintro; rfl
            rw [alloc_ov count hc0 hc32] at *
            iapply fresh_page (hG := hG) s.ptr mv.pgid' (uint.nat count) σ.ps Hcar (by omega) (by omega) hN
            iframe
    · -- found in the freelist: the run's pages are free, so no view covers them
      rw [hsn] at Hcan
      have hrfree := Hcan.2 r (inRun_self r _ (by omega))
      have hr2 : 2 ≤ uint.Z r := Hwf.2.1 r (List.mem_append_left _ hrfree)
      have hr0 : r ≠ W64 0 := by
        intro h; have : uint.Z r = 0 := by rw [h]; rfl
        omega
      rw [decide_eq_false hr0]
      try wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; rfl
      iexists { σ with fl := σ.fl.allocate txid r (uint.nat count) }, mv, r
      isplitr
      · ipureintro
        have hb := alloc_below σ v0 v1 Hok w hw r _ (by omega) Hcan
        have := alloc_unat mv.pgid'
        refine ⟨hr2, alloc_not_covered σ v0 v1 Hok w hw r _ Hcan, rfl, Int.le_refl _, hpg,
          by omega, Or.inl ⟨Hcan, rfl, rfl⟩⟩
      isplitr [Hwd Hwp Hwfl Hmf Hmv HWR Hpg Hz]
      · try simp only [ownDB]
        iexists dv, fls, v0, v1, dl
        isplitr
        · ipureintro; exact ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩
        isplitr
        · ipureintro; exact dbOK_allocate σ v0 v1 Hok txid r _ (by omega) Hcan
        isplitr
        · ipureintro; exact Hdr
        rw [hsn, Hfl']
        try simp only [FLImpl.iface, interface.mkOk]
        iframe
        iframe #
        try (ipureintro; exact Hlog)
      · iframe
        isplitl [HWR]
        · ileft; iframe; ipureintro; rfl
        rw [alloc_ov count hc0 hc32] at *
        iapply fresh_page (hG := hG) s.ptr r (uint.nat count) σ.ps Hcar (by omega) (by omega) hN
        iframe

end proof

end bbolt
end EtcdGrove
end Perennial
