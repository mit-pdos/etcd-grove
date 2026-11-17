/-
The proof of `Spec/os/File__ReadAtNoErr.lean`: `Proof/os/File__ReadAt.lean`'s racing read, generic in
its `pread`s' errnos (`wp_proofRacyLtQ`), at errno 0 (`pread_noErr`, through `wp_ext_post`): its
`*PathError` branch needs a nonzero errno.
-/
module

public import Spec.os.File__ReadAtNoErr
public import Proof.os.File__ReadAt
public import GooseLang.Ext.Fs.NoErrSpecsOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.ReadAt.wp_proofRacyLtNoErr :
    os.File.ReadAt.specRacyLtNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend
  iintro %Φ Hpre HΦ
  iapply os.File.ReadAt.wp_proofRacyLtQ (· = W64 0)
    (fun fd o n Φ => by
      iintro H
      iapply wp_ext_post "PRead" _ (by simp [val.isPanic])
        (fun r => ∃ r0, r = PairV r0 (#(0 : w64))) (pread_noErr hS fd o n) Φ
      iapply wp_wand $$ H
      iintro %r H %hr
      iapply H
      ipureintro
      intro r0 e he
      obtain ⟨r1, hr1⟩ := hr
      rw [hr1] at he
      exact (go.intoVal_inj (val.PairV.inj he).2).symm)
    f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend $$ Hpre
  inext
  iintro %n %err ⟨Hfo, Hfd, Hbs, %vs', Hsl, %h, Hr⟩
  icases Hr with (%h4 | ⟨%pe, %hpe, -⟩)
  · iapply HΦ
    iframe
    ipureintro; exact ⟨h.1, h.2.1, h.2.2, h4⟩
  · obtain ⟨-, e, he, hne⟩ := hpe
    exact absurd he hne

end proof

end EtcdGrove
end Perennial
