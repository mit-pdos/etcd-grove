/-
`proto.Size` of a registered message type at its wire content (per-type models, stage A; the
Scope's `[v6]` §4): the trust boundary (`google.golang.org/protobuf` is names-only), over a
registered pair (`pbModelOf`, `InvProto.lean`). Next to today's `proto.SizePb.spec` (CP3 rewires the
users). Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto

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

/-- **`proto.Size(m)` of a frozen `*T` of a registered type holding the wire content `c`**: no
premise; if `c`'s size (protobuf's formula, the instance's `size`) is below `2^63`, the result is
it. Above, Go's `int` sum wraps silently, without panicking, so the post says nothing of the result.

Against protobuf-go v1.36.11 (`proto/size.go:19`, `:40`): the size of the encoding `Marshal`
produces; the size cache is stored atomically (a hidden field in the instance's `pbMsg` invariant);
the wrapping additions are at `internal/impl/encode.go:34-45` and `:63-117`. Measured by the harness
`/shared/tmp/c9-entsize-harness` (`run.sh`; raft at `565c2bd`, protobuf-go v1.36.11, go1.27.3): an aliased message of true size `2^64` sizes without a panic (`TestC9SizeWrap`). Go's stack exhaustion on a deep chain of `Message` responses (a recursion through `Responses`, a fatal error, not a panic) is outside the model, as memory exhaustion is (`notes/txn-nested.md`, the axiom review's note on very deep trees). -/
abbrev proto.SizePb.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I →
  ∀ (l : Loc) (c : I.data.C),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ I.data.roC l c }}
    (App (Val (@! google_golang_org.protobuf.proto.Size))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (n : w64), RET #n; ⌜I.data.size c < 2 ^ 63 → sint.Z n = I.data.size c⌝ }}

end spec

end EtcdGrove
end Perennial
