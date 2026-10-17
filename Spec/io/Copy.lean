/-
`io.Copy` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
PR #22046 (branch `pr-verify/etcd-22046`), for `(*snap.Snapshotter).SaveDBFrom`.
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

/-- `io.Copy(dst, src)` from a reader `src` it may read to its end (`ioReader src`): some count, and
nil or an error. -/
abbrev io.Copy.spec : Prop :=
  ∀ (dst src : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ ioReader src }}
    (App (App (Val (@! _root_.Perennial.io.Copy)) (Val #dst)) (Val #src))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
