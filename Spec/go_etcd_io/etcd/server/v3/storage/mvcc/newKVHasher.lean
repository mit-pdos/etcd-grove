/-
`newKVHasher` (`hash.go:49-58`). (prove-etcdint3, 2026-11-21: proved over `hash/crc32`'s; until then
the trust boundary, `hash.go` names-only.)-/
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

/-- `newKVHasher(prev, rev, keep)` returns a hasher of these fields whose `hash` is a fresh `crc32`
digest over a Castagnoli table (`kvHasherOk`: `crc32.New(crc32.MakeTable(crc32.Castagnoli))`, to which
the `Key` bucket's name is written; audit B4b, 2026-10-18: for `WriteKeyValue` and `Hash`; 2026-11-21:
its points-to and the fields, until then an opaque `Prop` and no field). -/
abbrev mvcc.newKVHasher.spec : Prop :=
  ∀ (prev rev : w64) (keep : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher)) (Val #prev))
      (Val #rev)) (Val #keep))
  {{ (h : kvHasher), RET #h; mvcc.kvHasherOk h ∗
      ⌜h.compactRevision' = prev ∧ h.revision' = rev ∧ h.keep' = keep⌝ }}

end spec

end EtcdGrove
end Perennial
