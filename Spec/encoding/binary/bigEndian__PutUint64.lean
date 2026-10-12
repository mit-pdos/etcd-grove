/-
`binary.BigEndian.PutUint64(b, v)`, of Go's `encoding/binary`, stated as Perennial's
`encoding.binary.wp_BigEndian_PutUint64` (which proves it; Perennial translates `bigEndian`).
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

/-- `BigEndian.PutUint64(b, v)` writes the big-endian encoding of `v` to the first 8 bytes
of `b`. -/
abbrev binary.bigEndian.PutUint64.spec : Prop :=
  ∀ (b : GoSlice) (space rem : List w8) (v : w64), space.length = 8 →
  {{ (b ↦* (space ++ rem) : IProp GF) }}
    (App (App (Val (globalAddr encoding.binary.BigEndian @!!
      go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"PutUint64")) (Val #b)) (Val #v))
  {{ RET #(); b ↦* (u64Be v ++ rem) }}

/-- Encoding into exactly 8 bytes (from the spec). -/
theorem wp_bePutUint64 (h : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (b : GoSlice) (space : List w8) (v : w64) (hl : space.length = 8) :
    {{ (b ↦* space : IProp GF) }}
      (App (App (Val (globalAddr encoding.binary.BigEndian @!!
        go.GoType.PointerType encoding.binary.bigEndian.ty @!! go!"PutUint64")) (Val #b)) (Val #v))
    {{ RET #(); b ↦* u64Be v }} := by
  have hspec := h b space [] v hl
  rw [List.append_nil, List.append_nil] at hspec
  exact hspec

end spec

end EtcdGrove
end Perennial
