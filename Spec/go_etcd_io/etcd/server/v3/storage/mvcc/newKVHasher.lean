/-
`newKVHasher` (`hash.go`): the trust boundary (crc32 has no Perennial model; `hash.go` is names-only).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `newKVHasher(prev, rev, keep)` returns some hasher, one `kvHasherOk` (its `crc32` digest,
which has no model: the value is otherwise unconstrained; audit B4b, 2026-10-18, for
`WriteKeyValue` and `Hash`). -/
abbrev mvcc.newKVHasher.spec : Prop :=
  ∀ (prev rev : w64) (keep : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher)) (Val #prev))
      (Val #rev)) (Val #keep))
  {{ (h : kvHasher), RET #h; ⌜mvcc.kvHasherOk h⌝ }}

end spec

end EtcdGrove
end Perennial
