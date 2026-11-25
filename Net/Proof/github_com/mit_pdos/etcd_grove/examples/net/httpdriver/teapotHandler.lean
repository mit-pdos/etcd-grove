/- Lean-first (no Rocq counterpart).

# `teapotHandler`'s proof

`WriteHeader(418)` (no header lines), then `Write("short and stout")`: the request's path is `/status`
(`servePre`'s `pathUnder`, `pathUnder_lit`), whose complete answer (`drvRespEnd`) is exactly this; a
failed write leaves the writer failed.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.teapotHandler
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.HandlerOps
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto HdrLine RespSt HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem teapotHandler.wp_proof : teapotHandler.spec (GF := GF) (hG := hG) := by
  intro w r R τ rd I S E _HSb
  iintro ⟨#Hpkg, Hpre⟩
  iunfold net.http.servePre at Hpre
  icases Hpre with ⟨%Hp, -, -, #Hhreq, #Hops, HI, -, HS0, Htok⟩
  obtain ⟨-, -, Hunder⟩ := Hp
  have Hpath : R.path = go!"/status" := pathUnder_lit _ _ (by decide) Hunder
  have hend : ∀ B, drvRespEnd R B (W64 418) [] ([] ++ go!"short and stout") := by
    intro B
    refine ⟨fun h _ => absurd (Hpath.symm.trans h) (by decide), fun _ => ⟨rfl, rfl⟩,
      fun _ h => absurd Hpath h⟩
  isimp only [drvP] at Hhreq
  icases Hhreq with ⟨%B, -, #HgB⟩
  ihave #Hops2 := Hops
  iunfold net.http.respOps at Hops2
  icases Hops2 with ⟨%wi, %Hw, -, -, -⟩
  subst Hw
  wp_func_call
  wp_auto
  have hst : 200 ≤ uint.nat (W64 418) ∧ uint.nat (W64 418) ≤ 999 ∧
      net.http.bodyAllowed (W64 418) = true ∧ net.http.hdrsOk [] :=
    ⟨by word, by word, by unfold net.http.bodyAllowed; decide, hdrsOk_nil⟩
  wp_bind (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #(W64 418)))
  iapply (wp_resp_WriteHeader wi R τ drvP I [] [] true (W64 418) hst) $$ [HI]
  · iframe HI
    isplitr
    · iexact Hops
    imodintro
    simp only [drvP]
    ipureintro; simp
  inext
  iintro HI
  try wp_auto
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply (wp_resp_Write wi R τ drvP I (some (W64 418)) [] [] true sl go!"short and stout"
      (DFrac.own 1) (fun h => by cases h)) $$ [HI Hsl] as %n %err ⟨Hsl, Hres⟩
  · iframe HI Hsl
    isplitr
    · iexact Hops
    simp only [drvP]
    imodintro; ipureintro; simp
  try wp_auto
  isplitr
  · ipureintro; left; rfl
  iunfold net.http.serveDone
  isplitl [Htok]
  · iexact Htok
  isplitl [HS0]
  · iexists _; iexact HS0
  icases Hres with (⟨%He, HI⟩ | ⟨%bs', HI⟩)
  · ileft
    iexists (W64 418), [], ([] ++ go!"short and stout")
    simp only [Option.getD_some]
    iframe HI
    simp only [drvP]
    imodintro
    iexists B
    iframe HgB
    ipureintro; exact hend B
  · iright; ileft
    iexists _, _, _
    iexact HI

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
