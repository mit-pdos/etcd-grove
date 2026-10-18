/-
`utf8.ValidString` (Go's `unicode/utf8`, names-only here: the trust boundary of unit P3b; the
server's unary interceptor checks the client's API version with it). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.unicode.utf8.Valid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `utf8.ValidString(s)` returns whether `s` is valid UTF-8 (`utf8Valid`, Go's definition;
D19l (iii), 2026-10-18: until then some boolean). -/
abbrev utf8.ValidString.spec : Prop :=
  ∀ (str : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }}
    (App (Val (@! unicode.utf8.ValidString)) (Val #str))
  {{ (b : Bool), RET #b; ⌜b = decide (utf8Valid str)⌝ }}

end spec

end EtcdGrove
end Perennial
