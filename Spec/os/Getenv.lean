/-
`os.Getenv(key)` (names-only in Perennial): the value of the environment variable `key`, or
`""`; the spec says it returns some string (the environment is the deployment's). The trust boundary: an axiom, `Proof/os/Getenv.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Perennial.Code.os
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev os.Getenv.spec : Prop :=
  ∀ (key : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! os.Getenv)) (Val #key))
  {{ (v : GoString), RET #v; True }}

end spec

end EtcdGrove
end Perennial
