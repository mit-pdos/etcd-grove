/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/newEncoder.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newEncoder
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.New

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

theorem go_etcd_io.etcd.server.v3.storage.wal.newEncoder.wp_proof
    (wp_NewPW : go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter.spec (GF := GF) (hG := hG))
    (wp_New : go_etcd_io.etcd.pkg.v3.crc.New.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.newEncoder.spec (GF := GF) (hG := hG) := by
  intro wi prev off h0 h1
  wp_start as #Htab
  iunfold walCrcTable at Htab
  icases Htab with ⟨%tab, #Hg, #Ht⟩
  try wp_auto
  wp_apply (wp_NewPW wi (W64 4096) off (by decide) (by decide) h0 h1) as %pw Hpw
  try wp_auto
  wp_apply (wp_New prev tab) as %l Hl
  try wp_auto
  wp_func_call
  wp_call
  wp_apply (wp_slice_make3 (V := w8) (W64 1048576) (W64 1048576) ⟨by decide, by decide⟩)
    as %b ⟨Hb, -, %Hbc⟩
  try wp_auto
  iapply wp_fupd
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %u ⟨Hu, -⟩
  · ipureintro; decide
  try wp_auto
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave %Hul := ownSlice_len _ _ _ $$ Hu
  ihave ⟨«$r0», %Hen⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamed «$r0»
  have hbl2 : sint.Z b.len = 1048576 := by
    have := Hbl.1; rw [List.length_replicate] at this
    have h2 := Hbl.2
    have h3 : (sint.nat b.len : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
    omega
  have hbc2 : b.cap = b.len := by
    rw [Hbc]; apply BitVec.eq_of_toInt_eq
    rw [show (W64 1048576).toInt = 1048576 by decide]; exact hbl2.symm
  imod sync.init_Mutex (BI.pure True) ⊤
    «$r0_ptr».[go_etcd_io.etcd.server.v3.storage.wal.encoder, go!"mu"] $$ mu [] with #Hmu
  · inext; itrivial
  iapply HΦ
  isplitl
  rotate_left
  · ipureintro; exact Hen
  iunfold ownEncoder
  iexists pw, _, b, u, _, _
  isplitl []
  · iexact Hmu
  isplitl [bw]
  · iexact bw
  isplitl [Hpw]
  · iexact Hpw
  isplitl [crc]
  · iexact crc
  isplitl [Hl]
  · iunfold ownDecCrc
    iexists l, tab
    isplitr
    · ipureintro; rfl
    iframe Hl
    iexact Ht
  isplitl [buf]
  · iexact buf
  isplitl [Hb]
  · iexact Hb
  isplitr
  · ipureintro; exact ⟨hbl2, hbc2⟩
  isplitl [uint64buf]
  · iexact uint64buf
  isplitl [Hu]
  · iexact Hu
  ipureintro
  simp

end proof

end EtcdGrove
end Perennial
