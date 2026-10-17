/-
`strconv.ParseUint` (the standard library, names-only here: no file-system model). The trust boundary.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046`), for
`(*snap.Snapshotter).ReleaseSnapDBs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

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

/-- `strconv.ParseUint(s, base, bitSize)`: nil and `x` with `str.parseUint s base bitSize = some x` (an
abstract function: the parse is deterministic), or an error. -/
abbrev strconv.ParseUint.spec : Prop :=
  ∀ (s : GoString) (base bitSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
    (App (App (App (Val (@! _root_.Perennial.strconv.ParseUint)) (Val #s)) (Val #base)) (Val #bitSize))
  {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
      fsResult err iprop(⌜str.parseUint s base bitSize = some x⌝) iprop(True) }}

end spec

end EtcdGrove
end Perennial
