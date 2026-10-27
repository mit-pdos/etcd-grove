/-
`strconv.ParseInt(s, base, bitSize)` (names-only in Perennial): the integer `s` spells, or an
error; the spec says it returns some integer and error (for client-go's store, whose resource
version metric parses it, `parseRVForMetricsWithTruncation`). The trust boundary: an axiom,
`Proof/strconv/ParseInt.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Code.strconv
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
abbrev strconv.ParseInt.spec : Prop :=
  ∀ (s : GoString) (base bitSize : w64),
  {{ (True : IProp GF) }}
    (App (App (App (Val (@! strconv.ParseInt)) (Val #s)) (Val #base)) (Val #bitSize))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); True }}

end spec

end EtcdGrove
end Perennial
