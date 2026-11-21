/-
`strings.TrimSuffix(s, suffix)`: `s` without `suffix` if it ends with it, else `s`. Proved
(`Proof/strings/TrimSuffix.lean`) over Perennial's translation of Go's body
(`internal/stringslite`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Code.strings
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev strings.TrimSuffix.spec : Prop :=
  ∀ (s suffix : GoString),
  {{ (True : IProp GF) }}
    (App (App (Val #(functions _root_.Perennial.strings.TrimSuffix [])) (Val #s)) (Val #suffix))
  {{ RET #(if suffix <:+ s then s.take (s.length - suffix.length) else s); True }}

end spec

end EtcdGrove
end Perennial
