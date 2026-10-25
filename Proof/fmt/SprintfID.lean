/-
Proof of `Spec/fmt/SprintfID.lean`: a trust-boundary axiom (rafthttp stage 4d). Lean-first.
-/
module

public import Spec.fmt.SprintfID

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **Trust boundary** (rafthttp stage 4d): Go's `fmt.Sprintf` formats a `types.ID` by calling its
`String` method (`fmt.(*pp).handleMethods`: it implements `Stringer`), which is
`strconv.FormatUint(uint64(i), 16)`, reading no memory and not panicking; the model of `Sprintf`
(`Perennial/TrustedCode/fmt.lean`) describes the output up to the first directive it does not
interpret, as for any argument. -/
axiom fmt.SprintfID.wp_proof : fmt.SprintfID.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
