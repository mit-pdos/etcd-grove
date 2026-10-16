/-
`math.Ceil(x)`: Perennial translates `math` but specifies no float operation. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `math.Ceil(x)`: some `float64` (floats are outside the model: Perennial's 64-bit word, as
`time.Duration.Seconds`'s). -/
abbrev math.Ceil.spec : Prop :=
  ∀ (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
    (App (Val (@! math.Ceil)) (Val #x))
  {{ (y : w64), RET #y; True }}

end spec

end EtcdGrove
end Perennial
