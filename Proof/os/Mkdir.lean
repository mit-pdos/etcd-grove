/-
The proof of `Spec/os/Mkdir.lean`. `os.Mkdir` is Go's (since 2026-11-24, Go-model overlays S5):
`ignoringEINTR` around a closure calling `syscall.Mkdir`, whose model (`models/syscall/model.go`) asks
`PathKind` and, below a root, runs the stub `fsMkdir` (`CallBegin`, then the extension's `Mkdir`).
`os.Mkdir.wp_tree` is that code for a path below a root, for any per-attempt resource (`os.mkdirAttempt`:
one `fsMkdir`); `os.Mkdir.wp_notTree` for a root or an ancestor of one (no step). Each attempt is a
`CallBegin` with the whole call permission. Before the `mkdir` took effect, an attempt opens the
atomic update around the step (`wp_au_step`; the claim whole, `wp_osMkdirS`): an `EINTR` with no
effect aborts, any other result commits. After it took effect, the name holds the new directory in
the caller's fraction and a retry fails (`wp_osMkdirS_some`).
-/
module

public import Spec.os.Mkdir
public import Proof.os.PkgInit
public import Proof.os.ErrorOk
public import Proof.os.ErrnoPathErr
public import Proof.os.SharedExt
public import Proof.os.MkdirParts

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

theorem os.Mkdir.wp_proofSnc : os.Mkdir.specSnc (GF := GF) (hG := hG) := by
  intro d b perm R j dq h q r Q hb hn hq
  have hbN : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  icases osPathS_pathIn_keep R d dq j $$ Hp with ⟨%hpd, Hp⟩
  have hpin : PathIn R (child d b) := pathIn_child hpd.2 hb
  have htn : RootsTreeName R (child d b) := os.treeName_child hpd.2 hb
  imod osLogLb_0 with #Hlb
  wp_apply (os.Mkdir.wp_tree R (child d b) perm
    iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
      ((osAUnc (osNames j (.only [b]) (DFrac.own r) h) (mkOut j b h (DFrac.own r)) Q ∗
          osNames j (.only [b]) (DFrac.own q) h) ∨
        (∃ xs, Q (some xs) ∗ mkOut j b h (DFrac.own q) (some xs) ∗ mkNew (some xs))))
    (fun e => iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) 1 ∗
      ∃ o, ⌜e = 0 → o.isSome⌝ ∗ Q o ∗ mkOut j b h (DFrac.own q) o ∗ mkNew o))
    hpin htn) $$ [Hp Hperm Hn Hau] as %err ⟨%e, ⟨Hp, Hperm, %o, %ho, HQ, Hout, Hnew⟩, %he⟩
  · iframe; iframe #
    isplitl [Hn Hau]
    · ileft; iframe
    iintro !> %m %Φ' ⟨Hp, Hperm, HSt⟩ HΦ'
    icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsMkdir.impl
    wp_apply +noauto wp_osCallBeginS R _ 1 0 CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hnew⟩)
    · wp_apply +noauto (wp_aunc_step "Mkdir" _ (osNames j (.only [b]) (DFrac.own r) h)
        (mkOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ']
      iintro Hr
      ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
      · iframe
      iapply wp_osMkdirS R d b j dq h t s0 hb hn osN_sub_au osShN_sub_au $$ Hos Hsi Hp Hw Hk
      iintro %e Hperm Hp Hres
      icases Hres with (⟨%he, Hw⟩ | ⟨%x, %J, Hlog, Hw, HJ⟩)
      · icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr⟩
        by_cases he4 : e = W64 4
        · ileft
          iframe Hr
          iintro Hau
          iapply HΦ'
          ileft
          isplitr
          · ipureintro; exact he4
          iframe
          ileft; iframe
        · iright
          iexists none
          isplitl [Hr]
          · dsimp only [mkOut]; iframe
          iintro HQ
          iapply HΦ'
          iright
          isplitr
          · ipureintro; exact he4
          iframe
          iexists none
          dsimp only [mkOut, mkNew]
          iframe
          ipureintro; intro h0; exact absurd h0 he
      · icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr⟩
        unfold osLogged
        icases Hlog with ⟨%hst, #He, #Hl⟩
        iright
        iexists some (x, s0, J)
        isplitl [Hr]
        · dsimp only [mkOut, mkEnt, osLogged]; iframe; iframe #; ipureintro; exact hst
        iintro HQ
        ihave Hout : mkOut j b h (DFrac.own q) (some (x, s0, J)) $$ [Hn]
        · dsimp only [mkOut, mkEnt, osLogged]; iframe; iframe #; ipureintro; exact hst
        ihave Hnew : mkNew (some (x, s0, J)) $$ [HJ]
        · dsimp only [mkNew]; iexact HJ
        iapply HΦ'
        by_cases he4 : e = W64 4
        · ileft
          isplitr
          · ipureintro; exact he4
          iframe
          iright; iexists (x, s0, J); iframe
        · iright
          isplitr
          · ipureintro; exact he4
          iframe
          iexists some (x, s0, J)
          iframe
          ipureintro; intro _; rfl
    · obtain ⟨x, sx, J⟩ := xs
      isimp only [mkOut, osLogged] at Hout
      icases Hout with ⟨⟨%hst, #He, #Hl⟩, Hn⟩
      have hsome : ((h.log x (mkEnt j b J sx) (<[b := .dir J]> h.cur)).cur !! b).isSome := by
        simp only [NamesH.log]; rw [GMap.lookup_insert]; rfl
      wp_apply +noauto wp_osMkdirS_some R d b j (.only [b]) dq (DFrac.own q) _ t s0 1 hb hbN hsome
        CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
      ihave Hout : mkOut j b h (DFrac.own q) (some (x, sx, J)) $$ [Hn]
      · dsimp only [mkOut, osLogged]; iframe; iframe #; ipureintro; exact hst
      iapply HΦ'
      by_cases he4 : e = W64 4
      · ileft
        isplitr
        · ipureintro; exact he4
        iframe
        iright; iexists (x, sx, J); iframe
      · iright
        isplitr
        · ipureintro; exact he4
        iframe
        iexists some (x, sx, J)
        iframe
        ipureintro; intro _; rfl
  -- MERGE: lean added `fmtErrorOkOrNil err` to the post (lean proves it by `os.errnoPathErr_fmtErrorOkOrNil ... $$ Hsys Herr`); adapt: `os.Mkdir.wp_tree`'s post needs it (its `&PathError` of `modelErrno e`, `os.wp_modelPathError_ok ... $$ Hsys`)
  iapply HΦ
  iframe
  iexists o
  iframe
  ipureintro; intro hnil; exact ho (he.2.1 hnil)

/-- `specS` from `specSnc`: an `osAU` is an `osAUnc`. -/
theorem os.Mkdir.wp_proofS : os.Mkdir.specS (GF := GF) (hG := hG) := by
  intro d b perm R j dq h q r Q hb hn hq
  iintro %Φ ⟨#Hpk, #Hos, #Hsi, Hp, Hperm, Hn, Hau⟩ HΦ
  iapply os.Mkdir.wp_proofSnc d b perm R j dq h q r Q hb hn hq $$ [Hp Hperm Hn Hau] HΦ
  iframe Hpk Hos Hsi Hp Hperm Hn
  iapply osAU_osAUnc $$ Hau

end proof

end EtcdGrove
end Perennial
