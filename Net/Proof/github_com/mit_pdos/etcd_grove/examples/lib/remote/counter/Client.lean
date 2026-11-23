/-
The proof of `Client.spec`: `remote.ServeClient` with no system resource; the operation meets
`opMaybe` by `remote.Do` (with `Codec()` and `attempt()`): its choice gives the update it was handed
if an answer will come, and otherwise nothing (`Ψ := True`) and the update with its result dropped
(`lin_mono`); a read's other attempts take the read's update with no result.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Client
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Codec
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.attempt
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Do

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem Client.wp_proof
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_attempt : attempt.spec (GF := GF) (hG := hG))
    (wp_Do : remote.Do.spec (GF := GF) (hG := hG) (St := w64) (I := Bool) (O := w64))
    (wp_ServeClient : remote.ServeClient.spec (GF := GF) (hG := hG) (I := Bool) (O := w64)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γs c a sa hsa
  wp_start as ⟨#Hra, #Hsa, #Hmap, #Hrd⟩
  wp_auto
  ipersist serverAddr
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_apply (wp_Codec γs) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (cR γs)) c a _ _ cd d
    (fun _ => iprop(True)) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation: a `Do` at the server
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Φ
    iintro !> %Φr ⟨-, HL, -⟩ HΦr
    wp_auto
    wp_apply (wp_Codec γs) as %cd' #Hcd'
    wp_apply wp_attempt as %d' -
    rw [show (boxB i : GoInterface) = (cR (GF := GF) γs).iv i from rfl]
    ihave Hbu := budUnits_none (Gg := hG.goose_globalGS) sa hsa readTries
    wp_apply wp_Do (cR γs) sa i Φ iprop(True) cd' d' $$ [HL] as %v Hv
    · iframe #
      isplitr [HL]
      · cases hw : (cR (GF := GF) γs).B.isWrite i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          imodintro
          iapply Hrd
          ipureintro; exact hw
        · simp only [↓reduceIte]
          itrivial
      · iintro %known %bs
        cases known
        · simp only [Bool.false_eq_true, ↓reduceIte]
          imodintro
          isplitr
          · itrivial
          · ihave HL : lin (Gg := hG.goose_globalGS) (cR γs) i Φ $$ [HL]
            · cases hw : (cR (GF := GF) γs).B.isWrite i
              · rw [slotUpd_read _ hw]
                icases HL with #HL
                iexact HL
              · rw [slotUpd_write _ hw]
                iexact HL
            iapply lin_mono (Gg := hG.goose_globalGS) (cR γs) i Φ (fun _ => iprop(True))
              (fun _ => by iintro -; itrivial) $$ HL
        · simp only [↓reduceIte]
          imodintro
          iexists Φ
          iframe HL
          iintro %o - HΦ -
          imodintro
          iexact HΦ
    iapply HΦr
    isplitr
    · itrivial
    icases Hv with (⟨%o, %Ho, HΦ⟩ | ⟨%Hu, -⟩)
    · ileft
      iexists o
      iframe HΦ
      ipureintro; exact Ho
    · iright
      ipureintro; exact Hu
  · -- the client's system: nothing
    iintro %Φr HΦr
    wp_auto
    iapply HΦr
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
