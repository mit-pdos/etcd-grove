/-
The proof of `jsoncodec.Member` (`Net/Spec/models_lab/jsoncodec/Member.lean`). Ported from dsverify-lab's `wp_Member` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Member
public import Net.Spec.models_lab.jsoncodec.SkipSpace
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

theorem Member.wp_proof (wp_SkipSpace : SkipSpace.spec (GF := GF) (hG := hG)) (wp_Str : Str.spec (GF := GF) (hG := hG)) :
    Member.spec (GF := GF) (hG := hG) := by
  intro b dq bs i k rest hk hb k ++ 34#8
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + k.length + 3 ≤ bs.length := by
    have := congrArg List.length hb; simp at this; omega
  have h0 : bs[uint.nat i]? = some 34#8 := by
    have := congrArg (fun l => l[0]?) hb; simp only [List.getElem?_drop] at this; simpa using this
  have hcol : bs[uint.nat i + k.length + 2]? = some 58#8 := by
    have := congrArg (fun l => l[k.length + 2]?) hb
    simp only [List.getElem?_drop] at this
    rw [show uint.nat i + k.length + 2 = uint.nat i + (k.length + 2) by omega, this]
    simp [List.getElem?_append_right]
  wp_auto
  wp_apply (wp_SkipSpace_ns wp_SkipSpace b dq bs i _ h0 (by decide)) $$ Hs as Hs
  wp_apply (wp_Str b dq bs i k (58#8 :: rest) hk (by
    have := congrArg (List.drop 1) hb; simpa [List.drop_drop, Nat.add_comm] using this)
    (by omega)) $$ Hs as Hs
  wp_apply (wp_SkipSpace_ns wp_SkipSpace b dq bs _ _ (by rw [show uint.nat (W64 ((uint.nat i + 1 + k.length + 1 : Nat) : Int)) = uint.nat i + k.length + 2 by word]; exact hcol) (by decide)) $$ Hs as Hs
  rw [show W64 ((uint.nat i + 1 + k.length + 1 : Nat) : Int) + W64 1 =
    W64 ((uint.nat i + k.length + 3 : Nat) : Int) by word]
  iapply HΦ; iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
