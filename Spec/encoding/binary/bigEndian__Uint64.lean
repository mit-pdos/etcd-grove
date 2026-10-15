/-
`binary.BigEndian.Uint64(b)`, of Go's `encoding/binary`, stated as Perennial's
`encoding.binary.wp_BigEndian_Uint64` (which proves it; Perennial translates `bigEndian`).
Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- `BigEndian.Uint64(b)` decodes the first 8 bytes of `b`, big-endian. -/
abbrev binary.bigEndian.Uint64.spec : Prop :=
  ∀ (b : GoSlice) (bs rem : List w8) (dq : DFrac), bs.length = 8 →
  {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
    (App (Val (globalAddr encoding.binary.BigEndian @!!
      go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"Uint64")) (Val #b))
  {{ RET #(beToU64 bs); b ↦*{dq} (bs ++ rem) }}

open Iris.ProofMode in
/-- Decoding exactly an encoding (from the spec). -/
theorem wp_beUint64 (h : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)) (b : GoSlice)
    (x : w64) (dq : DFrac) :
    {{ (b ↦*{dq} u64Be x : IProp GF) }}
      (App (Val (globalAddr encoding.binary.BigEndian @!!
        go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"Uint64")) (Val #b))
    {{ RET #x; b ↦*{dq} u64Be x }} := by
  have hspec := h b (u64Be x) [] dq (u64Be_length x)
  rw [List.append_nil, beToU64_u64Be] at hspec
  exact hspec

end spec

end EtcdGrove
end Perennial
