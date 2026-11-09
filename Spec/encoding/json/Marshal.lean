/-
`json.Marshal(v)` (`encoding/json`, names only) of the one shape the verified code passes,
`storage.EncodeContinue`'s `&continueToken{APIVersion: "meta.k8s.io/v1", ResourceVersion: rv,
StartKey: start}`: no error, fresh bytes `tokJson rv start` (`Proof/encoding/json/Token.lean`, opaque),
the token unchanged.

Faithful: `encoding/json` marshals a struct of two strings and an `int64` without error (invalid UTF-8
is replaced, never an error; no `MarshalJSON` methods, no cycles, no unsupported types), and
deterministically, so its output is a function of the two varying fields (`TestMarshalToken`). The
trust boundary (stage 7e-2, `notes/k8s-7e-2-draft.md` §5.4, attacked T14): an axiom,
`Proof/encoding/json/Marshal.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Token
public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev encoding.json.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (t : k8s_io.apiserver.pkg.storage.continueToken),
  t.APIVersion' = go!"meta.k8s.io/v1" →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ l ↦{dq} t }}
    (App (Val (@! _root_.Perennial.encoding.json.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.continueToken.ty) #l)))
  {{ (sl : GoSlice), RET (PairV #sl #GoInterface.nil); l ↦{dq} t ∗
      sl ↦* (_root_.Perennial.encoding.json.tokJson t.ResourceVersion' t.StartKey') }}

end spec

end EtcdGrove
end Perennial
