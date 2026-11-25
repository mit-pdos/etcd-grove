/-
The proof of `jsoncodec.String` (`Net/Spec/models_lab/jsoncodec/String.lean`). Ported from dsverify-lab's `wp_String` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.String
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.Str
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true
set_option maxHeartbeats 2000000

theorem String.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) (wp_Str : Str.spec (GF := GF) (hG := hG)) :
    String.spec (GF := GF) (hG := hG) := by
  intro b dq bs i str rest hs hb
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + str.length + 2 ≤ bs.length := by
    have := congrArg List.length hb; simp at this; omega
  have h0 : bs[uint.nat i]? = some 34#8 := by
    have := congrArg (fun l => l[0]?) hb; simp only [List.getElem?_drop] at this; simpa using this
  have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i := skipEnd_ns' bs _ _ h0 (by decide)
  simp only [models_lab.jsoncodec.Set', models_lab.jsoncodec.Keep,
    models_lab.jsoncodec.TypeErr]
  wp_auto
  wp_apply (wp_At b dq bs i _ (by omega) (by rw [hsk]; exact h0)) $$ Hs as Hs
  rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
  wp_apply (wp_Str b dq bs i str rest hs (by
    have := congrArg (List.drop 1) hb; simpa [List.drop_drop, Nat.add_comm] using this)
    (by omega)) $$ Hs as Hs
  iapply HΦ; iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
