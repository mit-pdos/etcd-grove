/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/parseWALName.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.parseWALName.wp_proof
    (HSuf : strings.HasSuffix.spec (GF := GF) (hG := hG))
    (HScan : fmt.SscanfWalName.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG) := by
  intro str
  wp_start as #Hpkg
  ihave #Hi : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave Heb := wal.walInit_errBadWALName $$ Hi
  iunfold wal.errVar at Heb
  icases Heb with ⟨%eb, #Heb, -⟩
  wp_auto
  wp_apply HSuf str (go!".wal")
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_auto
    wp_apply HScan str _ (DFrac.own 1) seq_ptr index_ptr _ _ $$ [Hasl seq index]
      as %cnt %e ⟨Hasl, %a, %b, seq, index, %Hsc⟩
    · iframe
    try wp_auto
    iapply HΦ
    ipureintro
    refine ⟨fun x y _ hs => Hsc.1 x y hs, fun h => ?_⟩
    rcases h with h | h
    · exact absurd Hif h
    · exact Hsc.2 h
  · iapply HΦ
    ipureintro
    exact ⟨fun x y hs _ => absurd hs Hif, fun _ => by simp⟩

end proof

end EtcdGrove
end Perennial
