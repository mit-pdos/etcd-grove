/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/encoder__encode.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encode
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.write
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Write
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32
public import LinuxFs.Spec.google_golang_org.protobuf.proto.SizePb
public import LinuxFs.Spec.google_golang_org.protobuf.proto.MarshalPb
public import LinuxFs.Spec.google_golang_org.protobuf.proto.MarshalAppendCachedRecord
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_CrcWrite : go_etcd_io.etcd.pkg.v3.crc.digest.Write.spec (GF := GF) (hG := hG))
    (wp_Sum32 : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG))
    (wp_Size : proto.SizePb.spec (GF := GF) (hG := hG))
    (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG))
    (wp_MarshalAppend : proto.MarshalAppendCachedRecord.spec (GF := GF) (hG := hG))
    (wp_pad : go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding.spec (GF := GF) (hG := hG))
    (wp_write : go_etcd_io.etcd.server.v3.storage.wal.write.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.spec (GF := GF) (hG := hG) := by
  intro e wi W out pend c rp t d hsz
  iintro #Hw
  wp_start as ⟨#Henv, He, Hout, Hr⟩
  iunfold encRecIn at Hr
  icases Hr with ⟨%v, Hv, #Ht, #Hd, %Huf⟩
  ihave ⟨Hv, %Hrp⟩ := typedPointsto_not_null_dup _ _ _ $$ Hv
  iStructNamed Hv
  iunfold ownEncoder at He
  icases He with ⟨%pw, %h, %b, %u, %bs, %us, #Hmu, Hbw, Hpw, Hcrc, Hdig, Hbuf, Hbs, %Hb, Hu64, Hus,
    %Hus⟩
  ihave %Htnn := typedPointsto_not_null _ _ _ $$ Ht
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_if_destruct
  · exact absurd Hif Htnn
  iunfold encEnv at Henv
  icases Henv with ⟨#Hproto, #Hbin, #Hsync, #Htime, #Hmet⟩
  wp_apply wp_Lock $$ [] as ⟨Hown, -⟩
  · iexact Hmu
  try wp_auto
  iunfold ownDecCrc at Hdig
  icases Hdig with ⟨%l, %tab, %Hh, Hl, #Htab⟩
  subst Hh
  ihave #Hdd := recBytes_recOf _ _ _ _ $$ Hd
  try wp_auto
  wp_apply (wp_CrcWrite l c tab v.Data' d DFrac.discard) $$ [Hl] as ⟨Hl, -⟩
  · iframe; iframe #
  try wp_auto
  wp_apply (wp_Sum32 l (hash.crc32.crc32c c d) tab (DFrac.own 1)) $$ [Hl] as Hl
  · iexact Hl
  try wp_auto
  -- freeze the record: `recRoC rp (recOf ⟨t, c', d⟩)`
  ipersist «$r0»
  ipersist Type'
  ipersist Crc
  ipersist Data
  imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    rp.[go_etcd_io.etcd.server.v3.storage.wal.walpb.Record, go!"state"] ↦ st ∗
    rp.[go_etcd_io.etcd.server.v3.storage.wal.walpb.Record, go!"sizeCache"] ↦ sc ∗
      rp.[go_etcd_io.etcd.server.v3.storage.wal.walpb.Record, go!"unknownFields"] ↦ us ∗
      us ↦* ([] : List w8))) $$ [state sizeCache unknownFields] with #Hinv
  · inext
    iexists v.state', v.sizeCache', v.unknownFields'
    iframe
    rw [Huf]
    iapply ownSlice_nil
  ihave #Hro : recRoC rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩) $$ []
  · iunfold recRoC
    iunfold recPtsCC
    iexists v.Type', «$r0_ptr», v.Data'
    have hdata : (recOf ⟨t, hash.crc32.crc32c c d, d⟩).data = (recOf ⟨t, 0#32, d⟩).data := rfl
    rw [hdata]
    simp only [recOf, recCell, recHidden]
    isplitr
    · ipureintro; exact Hrp
    iframe #
    ipureintro
    exact ufWire_nil _
  try wp_auto
  have wpS := wp_Size pbRecordC pbRecordC_reg rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩)
  simp only [pbRecordC_ty, pbRecordC_roC, pbRecordC_size] at wpS
  wp_apply wpS $$ [] as %n %hn
  · iframe #
  try wp_auto
  have hS : sint.Z n = recSize (recOf ⟨t, hash.crc32.crc32c c d, d⟩) := hn (by omega)
  have hlenE : (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)).length < 2 ^ 47 := by
    rw [recEnc_length]; exact hsz
  wp_if_destruct
  · -- larger than the buffer: `proto.Marshal`
    have wpM := wp_Marshal pbRecordC pbRecordC_reg rp (recOf ⟨t, hash.crc32.crc32c c d, d⟩)
      trivial (by simp only [pbRecordC_size]; omega)
    simp only [pbRecordC_ty, pbRecordC_roC, pbEncC_pbRecordC] at wpM
    wp_apply wpM $$ [] as %dat ⟨Hdat, Hcap⟩
    · iframe #
    try wp_auto
    wp_apply (wp_pad dat (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)) (by omega))
      $$ [Hdat Hcap] as %dat2 ⟨Hdat2, Hcap2, -⟩
    · iframe
    try wp_auto
    wp_apply (wp_write pw wi W out pend u us dat2
      (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ++ List.replicate
        (framePad (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)).length) (0#8)) (DFrac.own 1) _ Hus
      (by have := framePad_lt (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)).length
          simp only [List.length_append, List.length_replicate]; omega))
      $$ [Hw] [Hpw Hout Hus Hdat2] as %err ⟨%ys, %pend', Hout, Hpw, Hus, Hdat2, %Hr⟩
    · iexact Hw
    · iframe
      iunfold encEnv
      iframe #
    try wp_auto
    wp_apply wp_Unlock $$ [Hown]
    · iframe
      isplitl []
      · iexact Hmu
      inext; itrivial
    try wp_auto
    iapply HΦ
    iexists ys, pend'
    iframe Hout Hro
    isplitl [Hpw Hbw Hcrc Hl Hbuf Hbs Hu64 Hus]
    · iunfold ownEncoder
      iexists pw, _, b, u, bs, _
      iframe
      iframe Hmu
      isplitl [Hl]
      · iunfold ownDecCrc
        iexists l, tab
        iframe
        iframe Htab
        ipureintro; rfl
      ipureintro
      exact ⟨Hb, u64Le_length _⟩
    ipureintro
    simp only [WalEnc.frame, walRecEnc, WalEnc.encodeFrameSize, List.append_assoc] at Hr ⊢
    exact Hr
  · -- `MarshalAppend` into `e.buf[:0]`
    try wp_auto
    obtain ⟨hbl, hbc⟩ := Hb
    have h0 : sint.Z (W64 0) = 0 := rfl
    have hsl : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z b.cap := by
      rw [h0, hbc, hbl]; unfold encBufBytes; omega
    simp only [hsl, and_self, ite_true]
    ihave Hbc : ownSliceCap w8 b (DFrac.own 1) $$ []
    · iapply ownSliceCap_empty b hbc.symm (by rw [hbl]; unfold encBufBytes; omega)
    icases ownSlice_slice_with_cap (W64 0) (W64 0) b bs ⟨by rw [h0]; exact Int.le_refl 0,
      by rw [h0]; exact Int.le_refl 0, by rw [h0, hbl]; unfold encBufBytes; omega⟩ $$ [Hbs Hbc] with ⟨-, Hb0, Hc0⟩
    · iframe
    have wpA := wp_MarshalAppend pbRecordC pbRecordC_reg opts_ptr (DFrac.own 1) rp
      (recOf ⟨t, hash.crc32.crc32c c d, d⟩) (slice.slice b w8 (W64 0) (W64 0))
      (subslice (sint.nat (W64 0)) (sint.nat (W64 0)) bs) trivial
      (by simp only [pbRecordC_size, subslice, sint.nat, h0]; simp; omega)
    simp only [pbRecordC_ty, pbRecordC_roC, pbEncC_pbRecordC] at wpA
    try wp_auto
    wp_apply wpA $$ [opts Hb0 Hc0] as %b' ⟨Hopts, Hb', Hc', Hor⟩
    · iframe
      iframe #
    have hsub : subslice 0 0 bs = [] := by simp [subslice]
    rw [hsub, List.nil_append]
    try wp_auto
    wp_apply (wp_pad b' (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)) (by omega))
      $$ [Hb' Hc'] as %dat2 ⟨Hdat2, Hcap2, Hback⟩
    · iframe
    try wp_auto
    wp_apply (wp_write pw wi W out pend u us dat2
      (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩) ++ List.replicate
        (framePad (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)).length) (0#8)) (DFrac.own 1) _ Hus
      (by have := framePad_lt (recEnc (recOf ⟨t, hash.crc32.crc32c c d, d⟩)).length
          simp only [List.length_append, List.length_replicate]; omega))
      $$ [Hw] [Hpw Hout Hus Hdat2] as %err ⟨%ys, %pend', Hout, Hpw, Hus, Hdat2, %Hr⟩
    · iexact Hw
    · iframe
      iunfold encEnv
      iframe #
    try wp_auto
    wp_apply wp_Unlock $$ [Hown]
    · iframe
      isplitl []
      · iexact Hmu
      inext; itrivial
    try wp_auto
    ihave ⟨Hb', Hc'⟩ := Hback $$ [Hdat2 Hcap2]
    · iframe
    ihave Hbs' : (∃ bs' : List w8, b ↦* bs') $$ [Hb' Hc' Hor]
    · icases Hor with (%Hpc | ⟨%ys0, Hy, Hyc⟩)
      · ihave %Hwf := ownSliceCap_wf _ _ $$ Hc'
        iapply (encBuf_back b' b _
          (by rw [Hpc.1]; exact sliceIndexRef_w8_zero b)
          (by rw [Hpc.2]; exact w64_sub_W64_zero _) hbc Hwf)
        iframe
      · ihave %Hwf := ownSliceCap_wf _ _ $$ Hyc
        iapply (encBuf_back (slice.slice b w8 (W64 0) (W64 0)) b ys0
          (slice_w8_zero_ptr b _) (slice_w8_zero_cap b _) hbc Hwf)
        iframe
    icases Hbs' with ⟨%bs', Hbs'⟩
    iapply HΦ
    iexists ys, pend'
    iframe Hout Hro
    isplitl [Hpw Hbw Hcrc Hl Hbuf Hbs' Hu64 Hus]
    · iunfold ownEncoder
      iexists pw, _, b, u, bs', _
      iframe
      iframe Hmu
      isplitl [Hl]
      · iunfold ownDecCrc
        iexists l, tab
        iframe
        iframe Htab
        ipureintro; rfl
      ipureintro
      exact ⟨⟨hbl, hbc⟩, u64Le_length _⟩
    ipureintro
    simp only [WalEnc.frame, walRecEnc, WalEnc.encodeFrameSize, List.append_assoc] at Hr ⊢
    exact Hr

end proof

end EtcdGrove
end Perennial
