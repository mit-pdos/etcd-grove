/-
The proof of `conn.hijacked` (`Net/Spec/net/http/conn__hijacked.lean`).
-/
module

public import Net.Spec.net.http.conn__hijacked

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

theorem conn.hijacked.wp_proof : conn.hijacked.spec (GF := GF) (hG := hG) := by
  intro c γh b
  wp_start as ⟨#Hmu, Hγ⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold connMuInv at Hinv
  icases Hinv with ⟨%b', Hhj, Hγ2⟩
  ihave %Hag := ghostVar_agree γh _ _ _ _ $$ Hγ Hγ2
  subst Hag
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hhj Hγ2]
  · inext; iunfold connMuInv; iexists b; iframe Hhj Hγ2
  iapply HΦ
  iexact Hγ

end proof

end net.http
end Perennial
