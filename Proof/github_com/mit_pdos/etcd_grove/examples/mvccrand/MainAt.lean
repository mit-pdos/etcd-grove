/- Lean-first (no Rocq counterpart).

`MainAt.spec` proved: `dirFits` answers `Fs.DirFits r` (so the database's path fits); the root's claim
split to the database's name (`claims_of_names`), `absent` of it, and, when it answers `true`, the
fresh database file made from the claim on the empty name (`fileHoldsF_of_only`), then `Run.spec`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.MainAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.dirFits
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.absent

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem MainAt.wp_proof (wp_dirFits : dirFits.spec (GF := GF) (hG := hG))
    (wp_absent : absent.spec (GF := GF) (hG := hG)) (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    MainAt.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ _ _ _ _ r
  wp_start as ⟨Hroot, Htok, #Hvoff⟩
  try wp_auto
  wp_apply wp_dirFits as %fits %hfits
  cases fits with
  | false =>
    try wp_auto
    iapply HΦ; itrivial
  | true =>
    have hd : Fs.DirFits r := hfits.1 rfl
    have hfit : Fs.PathFits (Fs.child r go!"mvccrand.db") := Fs.pathFits_of_dirFits hd (by decide)
    have hnm : NameOk go!"mvccrand.db" := by decide
    try wp_auto
    rw [show r ++ go!"/mvccrand.db" = Fs.child r go!"mvccrand.db" from rfl]
    iunfold rootClaimF at Hroot
    icases Hroot with ⟨%R, %j0, %h0, %q, %hr, #Hinv, #Hsh, Hn, Hperm⟩
    imod claims_of_names (hG := hG) R j0 [go!"mvccrand.db"] [] h0 (List.pairwise_singleton _ _)
      (fun _ _ h => absurd h List.not_mem_nil) $$ Hsh Hn with Hcl
    icases BigSepL.bigSepL_cons.1 $$ Hcl with ⟨⟨%hn, Hb⟩, -⟩
    imod Fs.osPathS_root (E := ⊤) (L := hG.goose_localGS) R r j0 (DFrac.own 1) hr
      (fun _ _ => CoPset.mem_full) $$ Hsh with Hpath
    wp_apply wp_absent r go!"mvccrand.db" R j0 1 hn q hnm (fsNoErrAt_of_all hfit)
      $$ [Hpath Hb Hperm] as %res ⟨-, Hb, Hperm, %hres⟩
    · iframe; iframe #
    cases res with
    | false =>
      try wp_auto
      iapply HΦ; itrivial
    | true =>
      imod fileHoldsF_of_only (hG := hG) R r go!"mvccrand.db" j0 hn q hr hnm hfit (hres rfl)
        $$ Hinv Hsh Hb Hperm with Hfile
      ihave Hfile' : backend.fileHolds (GF := GF) (Fs.child r go!"mvccrand.db") ∅ $$ [Hfile]
      · unfold backend.fileHolds
        rw [backend.onFs_eq]
        iexact Hfile
      try wp_auto
      wp_apply (wp_Run _ (by word) (by word) (by word) (by word) (by word) (by word)
          trivial trivial) $$ [Hfile' Htok] as %rep -
      · iframe Hfile' Htok Hvoff
        (try iPkgInit)
      (try wp_auto)
      iapply HΦ
      itrivial

end proof

end mvccrand
end EtcdGrove
end Perennial
