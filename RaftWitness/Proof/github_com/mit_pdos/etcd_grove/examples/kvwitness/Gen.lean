/-
Lean-first (no Rocq counterpart).

The proof of `Gen`: whatever `primitive.RandomUint64` returns, the result is a boxed `Input`
whose key and value are one and three bytes long.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Gen
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  intro id
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n _
  wp_if_destruct
  rotate_left
  wp_if_destruct
  all_goals (try wp_auto)
  all_goals
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %ksl ⟨Hksl, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    wp_apply wp_bytes_to_string $$ Hksl as Hksl
    wp_apply wp_slice_literal (V := w8) [_, _, _]
    isplitr
    · ipureintro; rfl
    iintro %vsl ⟨Hvsl, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    wp_apply wp_bytes_to_string $$ Hvsl as Hvsl
    iapply HΦ
    imodintro
    ipureintro
    exact ⟨_, rfl, by simp, by simp⟩

end proof

end kv
end EtcdGrove
end Perennial
