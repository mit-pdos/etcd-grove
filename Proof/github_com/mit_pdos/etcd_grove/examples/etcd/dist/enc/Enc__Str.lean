/-
The proof of `Enc.Str` (`Spec/.../dist/enc/Enc__Str.lean`): `U64` of the length, then the string's
bytes appended (`wp_string_to_bytes`, `wp_slice_append`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__U64
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem Enc.Str.wp_proof (wp_U64 : Enc.U64.spec (GF := GF) (hG := hG)) :
    Enc.Str.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hxl
  try wp_auto
  wp_apply wp_U64 e bs (W64 x.length) $$ [He] as He
  · iframe
  unfold ownEnc
  icases He with ⟨%s, He, Hs, Hcap⟩
  wp_auto
  wp_apply wp_string_to_bytes as %xs ⟨Hxs, -⟩
  wp_apply wp_slice_append $$ [$Hs $Hcap $Hxs] as %s' ⟨Hs, Hcap, -⟩
  try wp_auto
  iapply HΦ
  iexists s'
  rw [encStr, List.append_assoc]
  iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
