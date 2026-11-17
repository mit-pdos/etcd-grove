/-
The proofs of `Spec/os/File__WriteAtNoErr.lean`: `Proof/os/File__WriteAt.lean`'s and
`File__WriteAtExt.lean`'s loops, generic in their `pwrite`s' errnos (`wp_proofQ`, `wp_proofExtQ`), at
errno 0 below `maxBytes` (`wp_pwFinish_postNE`): their failures need a nonzero errno.
-/
module

public import Spec.os.File__WriteAtNoErr
public import Proof.os.File__WriteAtExt
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

private theorem maxBytes_lt : maxBytes < 2 ^ 63 := by unfold maxBytes; omega

theorem os.File.WriteAt.wp_proofNoErr : os.File.WriteAt.specNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf sl data dqs off dq d m xs hwr hoff hgap hB hn hn2 hxl
  have := maxBytes_lt
  iintro %Φ Hpre HΦ
  iapply os.File.WriteAt.wp_proofQ maxBytes (· = 0)
    (fun t p o dt m xs n Φ ho => wp_pwFinish_postNE hS t o dt ho _ (pwTok_inflight t p o dt m xs n) Φ)
    f fd name dqf sl data dqs off dq d m xs hwr hoff hgap (by omega) hn hn2 hxl hB $$ Hpre
  inext
  iintro %n %err ⟨Hfo, Hsl, Hfd, %j, %ys, %h, Hm, Hbs, Hc, -⟩
  obtain ⟨-, h2, -, h4⟩ := h
  rcases h4 with ⟨rfl, rfl, rfl⟩ | ⟨-, -, e, he, hne⟩
  · iapply HΦ
    iframe Hfo Hsl Hfd
    iexists ys
    iframe Hm Hbs Hc
    ipureintro; exact h2
  · subst he; exact absurd rfl hne

theorem os.File.WriteAt.wp_proofExtNoErr : os.File.WriteAt.specExtNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf sl data dqs off dq d m xs hwr hoff hB hn hxl
  have := maxBytes_lt
  iintro %Φ Hpre HΦ
  iapply os.File.WriteAt.wp_proofExtQ maxBytes (· = 0)
    (fun t p o dt m xs n Φ ho => wp_pwFinish_postNE hS t o dt ho _ (pwTokG_inflight t p o dt m xs n) Φ)
    f fd name dqf sl data dqs off dq d m xs hwr hoff (by omega) hn hxl hB $$ Hpre
  inext
  iintro %n %err ⟨Hfo, Hsl, Hfd, %j, %a, %E, %ys, %h, Hm, Hbs, Hc, -⟩
  obtain ⟨hja, hal, -, -, hE, h6, -, h8⟩ := h
  rcases h8 with ⟨rfl, rfl, rfl⟩ | ⟨-, -, e, he, hne⟩
  · obtain rfl : a = data.length := by omega
    obtain rfl := hE rfl
    iapply HΦ
    iframe Hfo Hsl Hfd
    iexists ys
    iframe Hm Hbs Hc
    ipureintro; exact h6
  · subst he; exact absurd rfl hne

end proof

end EtcdGrove
end Perennial
