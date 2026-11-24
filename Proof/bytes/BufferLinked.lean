/-
`bytes.Buffer.Write`'s spec linked to Perennial's proof (mit-pdos/perennial#670), for the
linking modules that pass it by name (the server's `rafthttp.createSnapBody`,
`etc/link-lean-first-server.txt`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.bytes.Buffer__Write
public import Perennial.Proof.bytes.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bytes.Assumptions]

theorem bytes.Buffer.Write.wp_linked : bytes.Buffer.Write.spec (GF := GF) (hG := hG) :=
  bytes.Buffer.Write.wp_proof _root_.Perennial.bytes.Buffer.wp_Write

end linked

end EtcdGrove
end Perennial
