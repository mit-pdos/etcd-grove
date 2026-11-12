/-
## `(*Meta).Sum64()` (`internal/common/meta.go`)

**Users.** db.go:703 (`init`), tx.go:453 (`writeMeta`); `Validate`, `Write`. Snippet `ReqMetaRoundTrip`.
**Proof sketch.** the first 56 bytes of `*m` through its byte view (`BytesView Meta`: `l ↦{dq} v` is `bytesPointsto l dq (encMeta v)`), `fnv.New64a()`, `h.Write`, `h.Sum64()` (hash/fnv's specs, `req/hash_fnv.md`).
**Changes.** from `specs-ref`'s file of the same name (unchanged); `fnv64a` spelled out here (the old one was `hash/fnv`'s model).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `m.Sum64()`: FNV-64a over the meta's bytes before the checksum (`metaSum`). -/
def Meta.Sum64.spec : Prop :=
  ∀ (l : Loc) (v : Meta) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗ ⌜0 < l.addr⌝ }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Sum64")) (Val #()))
  {{ RET #(metaSum v); l ↦{dq} v }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
