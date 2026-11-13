/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__GetCrc.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc


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
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.wp_proof : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG) := by
  intro l r
  wp_start as Hr
  iunfold ownRec at Hr
  icases Hr with ⟨%v, Hl, #Hc, #Ht, Hd⟩
  ihave %Hn := typedPointsto_not_null l _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  have hl : decide (l = null) = false := decide_eq_false Hn
  simp only [hl]
  iunfold optPtsTo at Ht
  icases Ht with (⟨%Hnull, %Hz⟩ | #Ht)
  · wp_auto
    simp only [decide_eq_true Hnull]
    wp_auto
    rw [Hz, show (W32 0) = zero_val w32 from rfl]
    iapply HΦ
    iunfold ownRec
    iexists v
    isplitl [state Type' Crc Data unknownFields sizeCache]
    · iapply typedPointsto_combine l _ _ Hn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · iframe
      iunfold optPtsTo
      iunfold optPtsTo at Hc
      isplitl []
      · iexact Hc
      · ileft
        ipureintro
        exact ⟨Hnull, Hz⟩
  · ihave %Hn' := typedPointsto_not_null v.Crc' _ _ $$ Ht
    wp_auto
    simp only [decide_eq_false Hn']
    wp_auto
    iapply HΦ
    iunfold ownRec
    iexists v
    isplitl [state Type' Crc Data unknownFields sizeCache]
    · iapply typedPointsto_combine l _ _ Hn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · iframe
      iunfold optPtsTo
      iunfold optPtsTo at Hc
      isplitl []
      · iexact Hc
      · iright
        iexact Ht

end proof

end EtcdGrove
end Perennial
