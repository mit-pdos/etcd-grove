/-
The proof of `Spec/os/RenameSNE.lean`: the model's `LstatDir` (the target's claim: not a
directory), then one attempt of its `EINTR` loop, a `CallBegin` (the log's length at least both
claims' last change, `osNames_next`) and the extension's `Rename` with no error
(`wp_osRenameFileSNE`): errno 0, so `nil`.
-/
module

public import Spec.os.RenameSNE
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.Rename.wp_proofFileSNE : os.Rename.specFileSNE (GF := GF) (hG := hG) := by
  intro Sio _ hS d bs d' bt j j' i N N' R dq dq' h h' qc hbs hbt hN hN' hkey hsrc htgt
  wp_start as ⟨#Hos, #Hsi, Hp, Hp', Hperm, Hn1, Hn2⟩
  imod osNames_next R j N _ h CoPset.subseteq_top $$ Hsi Hn1 with ⟨Hn1, #Hlb1⟩
  imod osNames_next R j' N' _ h' CoPset.subseteq_top $$ Hsi Hn2 with ⟨Hn2, #Hlb2⟩
  ihave #Hlb := osLogLb_max h.next h'.next $$ [Hlb1 Hlb2]
  · iframe #
  iclear Hlb1 Hlb2
  wp_apply wp_osCallBeginS R qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_apply wp_osLstatDirS_mem R d' bt j' N' dq' (DFrac.own 1) h' t s0 qc hbt hN'
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp' Hn2 Hk as %isDir %e %hd Hperm Hp' Hn2
  have hd1 : isDir ≠ 1 := fun h1 => by obtain ⟨⟨J, hJ⟩, -⟩ := hd h1; exact htgt J hJ
  rw [decide_eq_false (show isDir ≠ W64 1 from hd1)]
  wp_auto
  wp_apply +noauto wp_osCallBeginS R qc (max h.next h'.next) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t2 %s1 %hs1 Hk Hls
  iclear Hls
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_osRenameFileSNE Sio hS R d bs d' bt j j' i N N' dq dq' h h' t2 s1 qc hbs hbt hN hN'
    hkey hsrc htgt (Nat.le_trans (Nat.le_max_left _ _) hs1)
    (Nat.le_trans (Nat.le_max_right _ _) hs1) CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hp Hp' Hn1 Hn2 Hk
  iintro Hperm Hp Hp' ⟨%x, -, Hn1, Hn2⟩
  wp_auto
  iapply HΦ
  iframe Hp Hp' Hperm
  iexists _, _
  iframe Hn1 Hn2
  ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
