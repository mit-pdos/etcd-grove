/-
`d.Sum32()` (`crc32.go:230`): the digest's checksum. Lean-first (prove-etcdint3, 2026-11-21).
-/
module

public import GeneratedProof.hash.crc32

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

/-- See the file header. -/
abbrev hash.crc32.digest.Sum32.spec : Prop :=
  ∀ (d : Loc) (dq : DFrac) (x : _root_.Perennial.hash.crc32.digest),
  {{ (d ↦{dq} x : IProp GF) }}
    (App (Val (d @!! go.GoType.PointerType _root_.Perennial.hash.crc32.digest.ty @!! go!"Sum32"))
      (Val #()))
  {{ RET #x.crc'; d ↦{dq} x }}

end spec

end EtcdGrove
end Perennial
