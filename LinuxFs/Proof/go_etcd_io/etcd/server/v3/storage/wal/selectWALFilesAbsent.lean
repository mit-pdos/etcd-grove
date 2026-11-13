/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/selectWALFilesAbsent.lean`, over
`readWALNames.specAbsent` and `fmt.ErrorfErrs.spec`. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFilesAbsent
public import LinuxFs.Spec.fmt.ErrorfErrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.wp_proofAbsent
    (HNames : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.specAbsent (GF := GF) (hG := hG))
    (HErrorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.specAbsent (GF := GF) (hG := hG) := by
  intro lg d b sp R j dq qc N dqn h hb hN hi
  wp_start as ⟨#Hlg, #Hos, #Hsi, Hp, Hperm, Hn⟩
  wp_auto
  wp_apply HNames lg d b R j dq qc N dqn h hb hN hi $$ [Hp Hperm Hn]
    as %r %err ⟨Hp, Hperm, Hn, %e, %herr, #He⟩
  · iframe
    isplitl []
    · iexact Hlg
    isplitl []
    · iexact Hos
    iexact Hsi
  subst herr
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply HErrorf _ _ [GoInterface.ok e] [e] (by
        intro ii hii
        right
        simpa using hii) $$ [Hasl] as %err2 #Herr2
  · iframe
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
    iexact He
  try wp_auto
  iapply HΦ
  iframe
  iexists err2
  isplitr
  · ipureintro; rfl
  iexact Herr2

end proof

end EtcdGrove
end Perennial

end
