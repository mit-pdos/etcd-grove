/-
Port of election_proof/proof_fmt_Sprintf.v.
-/
module

public import Spec.fmt.Sprintf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The trust boundary**: Go's `fmt.Sprintf("%x", n)` for a `uint64` `n` returns the
hexadecimal digits of `n`, without leading zeros (`fmt.fmtInteger`, base 16): at most 16
bytes, and it does not panic (the argument is of a predeclared basic type, so no method of it
is called). Perennial's model of `Sprintf` formats `%x` as an unknown directive (arbitrary
output), so the bound is not provable from it. -/
axiom fmt.Sprintf.wp_hex :
  ∀ (args : GoSlice) (n : w64) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        args ↦*{dq} [interface.mkOk go.uint64 #n] }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #(go!"%x")))
        (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} [interface.mkOk go.uint64 #n] ∗
        ⌜s.length ≤ 16⌝ }}

/-- The general triple from Perennial's `fmt.wp_Sprintf`, proved from its model of `Sprintf`
(`Perennial/TrustedCode/fmt.lean`); the `%x` triple is `fmt.Sprintf.wp_hex`. -/
theorem fmt.Sprintf.wp_proof : fmt.Sprintf.spec (GF := GF) (hG := hG) := by
  refine ⟨?_, fmt.Sprintf.wp_hex⟩
  intro format args xs dq
  iintro %Φ ⟨#Hpkg, Hargs, %Hwf⟩ HΦ
  wp_apply _root_.Perennial.fmt.wp_Sprintf format args xs dq Hwf $$ [$Hargs] as %s ⟨Hargs, -⟩
  iapply HΦ $$ Hargs

end proof

end EtcdGrove
end Perennial
