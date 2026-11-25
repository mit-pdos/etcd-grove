/-
`metadata.MD.Get` (grpc, `metadata/metadata.go`): the trust boundary (grpc's `metadata` is types
and names only; unit P3b: the server's unary interceptor reads the client's API version with
it). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.strings.Lower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `md.Get(k)` (through a `*MD` `l` holding the map `md`, read-only, as Goose calls a
value-receiver method on a variable): `md[strings.ToLower(k)]`, the slice the map holds under the
lower-cased key `r` or `nil` if it holds none. `r` is what `strings.ToLower(k)` returns, of which
`strings.ToLower`'s spec says it is a lower-case ASCII word `w` exactly when `k` lower-cases to `w`
(`strings.lowersTo`). (grpc-trusted-T, T11, 2026-11-24: the post said only that `sl` was `nil` or some
key's slice; the body, translated and proved, gives the key's.) -/
abbrev metadata.MD.Get.spec : Prop :=
  ∀ (l : Loc) (md : GoMap) (m : GMap GoString GoSlice) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ l ↦□ md ∗
      md ↦$□ m }}
    (App (Val (l @!! go.GoType.PointerType google_golang_org.grpc.metadata.MD.ty @!! go!"Get"))
      (Val #k))
  {{ (sl : GoSlice), RET #sl;
      ⌜∃ r : GoString, (∀ w : GoString, strings.lowerWord w → (r = w ↔ strings.lowersTo k w = true)) ∧
        ((sl = slice.nil ∧ m !! r = none) ∨ m !! r = some sl)⌝ }}

end spec

end EtcdGrove
end Perennial
