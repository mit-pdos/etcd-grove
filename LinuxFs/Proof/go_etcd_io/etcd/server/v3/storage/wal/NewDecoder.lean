/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/NewDecoder.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.New
public import Perennial.GooseLang.IPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.wp_proof
    (HNFB : go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader.spec (GF := GF) (hG := hG))
    (HNew : go_etcd_io.etcd.pkg.v3.crc.New.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG) := by
  intro sl fs IoE eof
  wp_start as ⟨#Htab, Hsl, Hfs⟩
  wp_auto
  wp_func_call
  wp_call
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %rd ⟨Hrd, -⟩
  · ipureintro; word
  try wp_auto
  rename_i i0
  irename : (i0 ↦ zero_val w64 : IProp GF) => Hi0
  have hfl : fs.length = sint.nat sl.len := by simpa using Hlen.1
  ihave IH : iprop(∃ (n k : w64) (fbrs : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "Hi0" ∷ i0 ↦ k ∗
      "Hrd" ∷ rd ↦* (fbrs ++ List.replicate (fs.length - sint.nat n) (zero_val Loc)) ∗
      "Hfbrs" ∷ ownFbrs IoE eof fbrs (fs.take (sint.nat n)) ((fs.take (sint.nat n)).map (fun _ => [])) ∗
      "Hfs" ∷ ([∗list] F ∈ fs.drop (sint.nat n), iprop(decFile IoE eof F ∗ F.S [])) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ fs.length ∧ fbrs.length = sint.nat n⌝) $$ [i Hi0 Hrd Hfs]
  · iexists W64 0, _, []
    simp only [named]
    rw [show sint.nat (W64 0) = 0 by rfl, Nat.sub_zero, hfl, List.nil_append, List.drop_zero,
      List.take_zero, List.map_nil]
    iframe
    isplitr
    · iunfold ownFbrs; itrivial
    ipureintro; refine ⟨by decide, by omega, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    have hlt : sint.nat n < fs.length := by rw [hfl]; word
    obtain ⟨F, hF⟩ : ∃ F, fs[sint.nat n]? = some F := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hFm : (List.map (fun F => GoInterface.ok F.fr) fs)[(sint.Z n).toNat]? =
        some (GoInterface.ok F.fr) := by
      rw [List.getElem?_map]; show (fs[sint.nat n]?).map _ = _; rw [hF]; rfl
    wp_apply wp_load_slice_index sl (sint.Z n) _ (DFrac.own 1) (GoInterface.ok F.fr) Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hFm
    try wp_auto
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) _ (DFrac.own 1) (GoInterface.ok F.fr) Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hFm
    rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hF).2]
    icases Hfs with ⟨⟨#HF, HS⟩, Hfs⟩
    ihave HF' := HF
    iunfold decFile at HF'
    icases HF' with ⟨#Hrs, #Hpre, #HFI, %HFp⟩
    wp_apply HNFB F.fr F.S (decRdErr F.bs eof IoE) []
      (fun fi err => iprop(⌜err ≠ GoInterface.nil → IoE err⌝ ∗
        (⌜err = GoInterface.nil⌝ -∗ fileInfoOk fi F.bs.length))) HFp.1 $$ [HS]
      as %fbr ⟨%b, %fi, %err, Hfbr, Hb, HQ⟩
    · iframe; iexact HFI
    try wp_auto
    ihave Hfbr2 := (dfractional_update_into_persistently
      (typedPointsto (GF := GF) fbr
        (go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err) (DFrac.own 1))
      (fun dq => typedPointsto (GF := GF) fbr
        (go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err) dq)
      (DFrac.own 1)).update_into_persistently $$ Hfbr
    iapply wp_fupd
    imod Hfbr2 with #Hfbr
    ihave %Hrdl := ownSlice_len _ _ _ $$ Hrd
    simp only [List.length_append, List.length_replicate] at Hrdl
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rd.len := ⟨Hn.1, by word⟩
    simp only [Hbnd2, and_self, ↓reduceIte]
    wp_apply wp_store_slice_index rd (sint.Z n) _ fbr $$ [Hrd] as Hrd
    · iframe; ipureintro
      simp only [List.length_append, List.length_replicate]
      exact ⟨Hn.1, by word⟩
    icases HQ with ⟨%HQ1, HQ2⟩
    try wp_auto
    imodintro
    wp_for_post
    iframe
    iexists n + W64 1, n, fbrs ++ [fbr]
    simp only [named]
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hidx : (sint.Z n).toNat = fbrs.length := by rw [Hn.2.2]; try rfl
    have hset : (fbrs ++ List.replicate (fs.length - sint.nat n) (zero_val Loc)).set
        (sint.Z n).toNat fbr =
        (fbrs ++ [fbr]) ++ List.replicate (fs.length - (sint.nat n + 1)) (zero_val Loc) := by
      rw [hidx, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
        show fs.length - sint.nat n = (fs.length - (sint.nat n + 1)) + 1 by omega,
        List.replicate_succ, List.set_cons_zero, List.append_assoc]
      rfl
    have htake : fs.take (sint.nat n + 1) = fs.take (sint.nat n) ++ [F] := by
      rw [List.take_add_one, hF]; rfl
    rw [hn1, hset, htake]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitl [Hfbrs Hb HQ2]
    · iapply ownFbrs_snoc IoE eof fbr F [] fbrs _ _ (by rw [Hn.2.2, List.length_take]; omega)
        (by simp)
      iframe Hfbrs
      iunfold ownFbr
      iexists b, fi, err
      iframe
      iframe Hfbr HF
      ipureintro; exact HQ1
    ipureintro
    refine ⟨by word, by omega, by simp [Hn.2.2]⟩
  · have hn : sint.nat n = fs.length := by rw [hfl] at Hn ⊢; word
    rw [hn, Nat.sub_self, List.replicate_zero, List.append_nil, List.take_length, List.drop_length]
    iunfold walCrcTable at Htab
    icases Htab with ⟨%tab, #Hgt, #Htabarr⟩
    wp_auto
    wp_apply HNew (W32 0) tab as %lc Hlc
    wp_alloc d as Hd
    iStructNamed Hd
    iapply wp_fupd
    wp_auto
    ipersist Hrd
    ihave Hm := sync.init_Mutex (GF := GF) (BI.pure True : IProp GF) ⊤ _ $$ mu
    ihave Hm2 := Hm $$ []
    · inext; itrivial
    imod Hm2 with #Hmu
    imodintro
    iapply HΦ
    iexists d
    isplitr
    · ipureintro; rfl
    iframe Hsl
    iunfold ownDecoder
    iexists rd, fbrs, interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.crc.digest.ty) #lc,
      fs.map (fun _ => [])
    iframe
    iframe Hmu Hrd
    isplitl [Hlc]
    · iunfold ownDecCrc
      iexists lc, tab
      iframe
      iframe Htabarr
      ipureintro; rfl
    ipureintro
    refine ⟨by decide, fun _ => ?_⟩
    cases fs <;> simp [liveRs]

end proof

end EtcdGrove
end Perennial
