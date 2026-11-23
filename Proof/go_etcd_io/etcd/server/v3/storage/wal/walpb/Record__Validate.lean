/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__Validate.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc


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

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.wp_proof
    (HErrorf : fmt.ErrorfErrsNot.spec (GF := GF) (hG := hG))
    (HGetCrc : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG) := by
  intro l r crc e t ht
  wp_start as ⟨#HE, #Hok, #Hn, #Ht, Hr⟩
  wp_auto
  wp_apply HGetCrc $$ Hr as Hr
  wp_if_destruct
  · rename_i Hif
    iapply HΦ
    iframe
    ileft
    ipureintro
    exact ⟨rfl, trivial⟩
  · rename_i Hif
    wp_apply HGetCrc $$ Hr as Hr
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply HErrorf _ _ [GoInterface.ok e, interface.mkOk go.uint32 #r.crc,
        interface.mkOk go.uint32 #crc] [e] e t ?wf ?ww (by simp) ht $$ [Hsl2] as %err ⟨#Herr, #Hn', #Ht'⟩
    case wf => errargs_wf
    case ww => wraps_err
    · iframe
      isplitl []
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact Hok
      iframe Hn Ht
    · iapply HΦ
      iframe
      iright
      isplitl []
      · ipureintro; assumption
      · iexists err
        isplitl []
        · ipureintro; rfl
        · iframe Herr Hn' Ht'

end proof

end EtcdGrove
end Perennial
