module
public import Spec.go_etcd_io.bbolt.Tx__writeMeta
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.os.File__WriteAt
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Proof.go_etcd_io.bbolt.AllocPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The zero meta. -/
abbrev zeroMetaW : Meta :=
  Meta.mk (W32 0) (W32 0) (W32 0) (W32 0) (InBucket.mk (W64 0) (W64 0)) (W64 0) (W64 0) (W64 0)
    (W64 0)

theorem leBytes_zeroW (n : Nat) : leBytes n 0 = List.replicate n (W8 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [leBytes, Int.zero_ediv, ih, List.replicate_succ]; try rfl

theorem metaBytes_zeroW : metaBytes zeroMetaW = List.replicate 64 (W8 0) := by
  unfold metaBytes inBucketBytes zeroMetaW
  simp only [BitVec.toNat_ofInt]
  simp [leBytes_zeroW, List.replicate_append_replicate]

/-- A zeroed page buffer is a zero header, a zero meta and zeros. -/
theorem zero_regionW (l : Loc) (ps : Nat) (hl : l.locCar ≠ 0) (hps : 80 ≤ ps) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (List.replicate ps (W8 0)) ⊢
      l ↦ Page.mk (W64 0) (W16 0) (W16 0) (W32 0) ∗ (l +ₗ (16 : Int)) ↦ zeroMetaW ∗
        bytesPointsto (l +ₗ ((80 : Nat) : Int)) (DFrac.own 1) (List.replicate (ps - 80) (W8 0)) := by
  have hl16 : (l +ₗ (16 : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  iintro H
  icases (zero_page (hG := hG) l ps hl (by omega)).1 $$ H with ⟨Hp, Hz⟩
  rw [show ps - 16 = 64 + (ps - 80) by omega, ← List.replicate_append_replicate]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hz with ⟨Hm, Hz⟩
  rw [List.length_replicate, show l +ₗ (16 : Int) +ₗ ((64 : Nat) : Int) = l +ₗ ((80 : Nat) : Int) by
    rw [loc_add_assoc]; rfl]
  rw [← metaBytes_zeroW]
  ihave Hm := (Meta_bytes (hG := hG) (l +ₗ (16 : Int)) zeroMetaW _ hl16).2 $$ Hm
  iframe

/-- The meta page's header, meta and zeros: its bytes. -/
theorem meta_page_joinW (l : Loc) (ps : Nat) (mv : Meta) (hl : l.locCar ≠ 0) :
    l ↦ Page.mk (mv.txid' % W64 2) (W16 4) (W16 0) (W32 0) ∗ (l +ₗ (16 : Int)) ↦ metaSummed mv ∗
      bytesPointsto (l +ₗ ((80 : Nat) : Int)) (DFrac.own 1) (List.replicate (ps - 80) (W8 0)) ⊢
    bytesPointsto (GF := GF) l (DFrac.own 1) (metaPage mv ps) := by
  have hl16 : (l +ₗ (16 : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  iintro ⟨Hp, Hm, Hz⟩
  ihave Hp := (Page_bytes (hG := hG) l _ _ hl).1 $$ Hp
  ihave Hm := (Meta_bytes (hG := hG) _ _ _ hl16).1 $$ Hm
  unfold metaPage
  iapply (bytesPointsto_app _ _ _ _).2
  rw [List.length_append, show (pageBytes (Page.mk (mv.txid' % W64 2) (W16 4) (W16 0) (W32 0))).length +
      (metaBytes (metaSummed mv)).length = 80 by simp [pageBytes, metaBytes_length, leBytes_length]]
  iframe
  iapply (bytesPointsto_app _ _ _ _).2
  rw [show (pageBytes (Page.mk (mv.txid' % W64 2) (W16 4) (W16 0) (W32 0))).length = 16 by
    simp [pageBytes, leBytes_length]]
  iframe

theorem metaPage_length (mv : Meta) (ps : Nat) (h : 80 ≤ ps) : (metaPage mv ps).length = ps := by
  simp [metaPage, pageBytes, metaBytes_length, leBytes_length]; omega

theorem mod2_val (x : w64) (ps : Nat) (hps : ps < 2 ^ 32) :
    x % W64 2 * W64 (ps : Int) = W64 ((uint.nat (x % W64 2) * ps : Nat) : Int) := by
  have : x % W64 2 = W64 ((uint.nat (x % W64 2) : Nat) : Int) := by unfold uint.nat; word
  conv => lhs; rw [this]
  rw [← BitVec.ofInt_mul]; push_cast; rfl

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [linux : GOOSLinux]

theorem Tx.writeMeta.wp_proof
    (hLog : DB.Logger.spec (GF := GF) (hG := hG))
    (hPIB : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hMW : Meta.Write.spec (GF := GF) (hG := hG))
    (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hWA : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hfds : _root_.Perennial.EtcdGrove.bbolt.fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG))
    (hErrf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG)) :
    Tx.writeMeta.spec (GF := GF) (hG := hG) := by
  intro txl dbl ml mv f fd bs m ps lg dl ns st dq Hdbl Hmlc Hps80 Hps32 Hlg Hroot Hfl Hslot
  wp_start as ⟨Hdb, Hmeta, Hstats, Hmv, Hlogger, #Hdl, #Hdlok, Hps, Hfile, Hns, Hwa, #Hml, #Hof,
    Hbytes, Hmap, Hmr⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply hLog dbl dq lg dl Hdbl $$ [Hlogger] as Hlogger
  · iframe; iframe #
  have Hd : (if lg = interface.nil then discardIface dl else lg) = discardIface dl := by
    rcases Hlg with h | h <;> rw [h] <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  wp_apply wp_slice_make2 (V := w8) as %s ⟨Hs, -⟩
  · ipureintro; word
  try wp_auto
  rw [show sint.nat (W64 (ps : Int)) = ps by word, show (zero_val w8 : w8) = W8 0 from rfl]
  have hne : List.replicate ps (W8 0) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  icases (ownSlice_bytes s _ _ hne).1 $$ Hs with ⟨Hs, %Hslen⟩
  icases persistent_entails_left (bytesPointsto_car s.ptr _ _ hne) $$ Hs with ⟨Hs, %Hcar⟩
  wp_apply hPIB dbl (W64 (ps : Int)) dq s (W64 0) Hcar (by word) (by simp at Hslen; word)
    $$ [Hps] as Hps
  · iframe
  rw [show s.ptr +ₗ sint.Z (W64 0 * W64 (ps : Int)) = s.ptr by
    rw [show sint.Z (W64 0 * W64 (ps : Int)) = 0 by word]; simp [Loc.add]]
  icases zero_regionW (GF := GF) s.ptr ps Hcar Hps80 $$ Hs with ⟨Hp, Hm, Hz⟩
  try wp_auto
  wp_apply hMW ml s.ptr mv _ _ Hmlc Hroot Hfl $$ [Hmv Hp Hm] as ⟨Hmv, Hp, Hm⟩
  · iframe
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hml] as ⟨Hlocked, -⟩
  try wp_auto
  wp_apply hId s.ptr _ (DFrac.own 1) $$ [Hp] as Hp
  · iframe
  try wp_auto
  ihave Hs := meta_page_joinW (GF := GF) s.ptr ps mv Hcar $$ [Hp Hm Hz]
  · unfold metaSummed; iframe
  have Hml := metaPage_length mv ps Hps80
  have hne' : metaPage mv ps ≠ [] := List.ne_nil_of_length_pos (by omega)
  ihave Hs := (ownSlice_bytes s _ _ hne').2 $$ [Hs]
  · iframe; ipureintro; rw [Hml]; simp at Hslen; exact ⟨Hslen.1, Hslen.2⟩
  have Hs2 : uint.nat (mv.txid' % W64 2) < 2 := by unfold uint.nat; word
  have Hoff : uint.nat (mv.txid' % W64 2) * ps + ps ≤ bs.length := by
    rw [Nat.add_mul, Nat.one_mul] at Hslot; omega
  rw [mod2_val mv.txid' ps Hps32]
  have Hsn : sint.nat (W64 ((uint.nat (mv.txid' % W64 2) * ps : Nat) : Int)) =
      uint.nat (mv.txid' % W64 2) * ps := by
    have : uint.nat (mv.txid' % W64 2) * ps < 2 ^ 62 := by
      have := Nat.mul_le_mul_right ps (show uint.nat (mv.txid' % W64 2) ≤ 1 by omega); omega
    word
  wp_apply hWA f fd bs m s (metaPage mv ps) (DFrac.own 1)
      (W64 ((uint.nat (mv.txid' % W64 2) * ps : Nat) : Int)) (by word)
      $$ [Hbytes Hmap Hs Hmr] as %n %err ⟨%k, %Hk, Hbytes, Hmap, Hs, Hmr⟩
  · rw [Hsn, Nat.min_eq_left (by omega), Hml]; iframe; iframe #
  rw [Hsn, Nat.min_eq_left (by omega), Hml]
  obtain ⟨Hk1, -, Hk3⟩ := Hk
  rw [Hml] at Hk1 Hk3
  cases err
  rotate_left
  · -- written: unlock, sync
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hml $Hlocked]
    · iframe; inext; itrivial
    try wp_auto
    cases ns
    · try wp_auto
      wp_apply hfds dbl f fd dq $$ [Hfile] as %ferr Hfile
      · iframe; iframe #
      try wp_auto
      cases ferr
      rotate_left
      · try wp_auto
        wp_apply hInc _ st (W64 1) $$ [Hstats] as %st' ⟨-, Hstats⟩
        · iframe
        try wp_auto
        iapply HΦ
        iexists k, st', _
        iframe
        ipureintro; exact ⟨rfl, Hk1, fun _ => Hk3 rfl⟩
      · rename_i e
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %slx ⟨Hslx, -⟩
        try wp_auto
        rw [GOOSLinux.goos]
        try wp_auto
        wp_apply hErrf dl _ _ $$ [Hdlok]
        · iframe #
        try wp_auto
        iapply HΦ
        iexists k, st, _
        iframe
        ipureintro; exact ⟨rfl, Hk1, fun h => nomatch h⟩
    · try wp_auto
      wp_apply hInc _ st (W64 1) $$ [Hstats] as %st' ⟨-, Hstats⟩
      · iframe
      try wp_auto
      iapply HΦ
      iexists k, st', _
      iframe
      ipureintro; exact ⟨rfl, Hk1, fun _ => Hk3 rfl⟩
  · rename_i e
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hml $Hlocked]
    · iframe; inext; itrivial
    try wp_auto
    icases (ownSlice_bytes s _ _ hne').1 $$ Hs with ⟨Hs, -⟩
    icases (page_header_bytes (hG := hG) s.ptr (DFrac.own 1) (metaPage mv ps) (by omega) Hcar).1 $$ Hs
      with ⟨Hh, -⟩
    wp_apply hId s.ptr _ (DFrac.own 1) $$ [Hh] as Hh
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %slx ⟨Hslx, -⟩
    try wp_auto
    wp_apply hErrf dl _ _ $$ [Hdlok]
    · iframe #
    try wp_auto
    iapply HΦ
    iexists k, st, _
    iframe
    ipureintro; exact ⟨rfl, Hk1, fun h => nomatch h⟩

end proof

end bbolt
end EtcdGrove
end Perennial
