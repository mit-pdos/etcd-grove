/-
The trust boundary: `fmt.Sscanf` (Perennial translates `fmt` names-only and has no model of its
scanner), for `Sscanf(s, "%d", &n)` with an `int` `n`.
-/
module

public import Spec.fmt.Sscanf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **The trust boundary**: Go's `fmt.Sscanf(s, "%d", &n)` into an `int` (`fmt`'s scanner is not
translated: it reaches `reflect`) stores the parsed value on success (`fmt.scanInt`, where
defined) and leaves `n` unchanged on an error. Checked against Go 1.27 on `" 5"`, `"+5"`,
`"-0007"`, `"5abc"`, `"0000000000000005"`, `"-9223372036854775808"` (parsed), `""`, `"+-5"`,
`"9223372036854775808"` (errors, `n` unchanged). -/
axiom fmt.Sscanf.wp_proof : fmt.Sscanf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
