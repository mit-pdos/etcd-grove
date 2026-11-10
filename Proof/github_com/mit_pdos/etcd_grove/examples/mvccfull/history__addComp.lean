/- Lean-first (no Rocq counterpart). The proof of `history.addComp` (as `appendRev`'s, one slice): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__addComp

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem history.addComp.wp_proof :
    history.addComp.spec (GF := GF) (hG := hG) := by
  intro h γ Hs Cs c
  wp_start as ⟨#Hh, Hw⟩
  iunfold isHistory at Hh
  ihave #Hg := Hh
  iunfold histW at Hw
  icases Hw with ⟨%x, %Hx, Hgw, Hlw, Hcap1, Hcap2, Hcap3⟩
  obtain ⟨Hx, Hxc⟩ := Hx
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  iunfold histR at HP
  icases HP with ⟨%x', Hs, Hcs, Hcp, Hg', Hl', #He⟩
  ihave %Hag := ghostVar_agree γ.g _ _ _ _ $$ Hg' Hgw
  obtain ⟨-, rfl⟩ := Hag
  iunfold histElems at He
  icases He with ⟨%H2, #Hms, #Hcss, #Hcps, #Hst, #Hch⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := w64) x.comps x.cps _ [c] (DFrac.own 1))
    $$ [$Hcps $Hcap3 $Hosl] as %s3 ⟨#Hs3, Hcap3, -⟩
  (try wp_auto)
  let x2 : HistCells := ⟨x.states, x.changes, s3, x.ms, x.cs, x.cps ++ [c], x.revs⟩
  imod ghostVar_update_halves x2 γ.g _ _ $$ Hg' Hgw with ⟨Hg', Hgw⟩
  wp_apply +noauto sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hs Hcs Hcp Hg' Hl']
  · inext
    iunfold histR
    iexists x2
    iframe
    iunfold histElems
    iframe #
    ipureintro; exact H2
  wp_auto
  iapply HΦ
  iunfold histW
  iexists x2
  iframe
  ipureintro; exact ⟨Hx, by rw [← Hxc]⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
