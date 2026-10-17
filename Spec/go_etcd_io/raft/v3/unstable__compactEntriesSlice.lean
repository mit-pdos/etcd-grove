/-
Lean-first (etcd-io/raft#96).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `u.compactEntriesSlice(k)` (`log_unstable.go:200`, raft#96): `u.entries` becomes a copy of
`u.entries[k:]` in a fresh array of exactly its length; the state loses its first `k` entries.
`0 ≤ k ≤ len(u.entries)` (else the slice expression panics). -/
abbrev unstable.compactEntriesSlice.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (k : w64),
  0 ≤ sint.Z k → sint.Z k ≤ (us.ents.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"compactEntriesSlice")) (Val #k))
  {{ RET #(); ownUnstable u { us with ents := us.ents.drop (sint.Z k).toNat } }}

end spec

end EtcdGrove
end Perennial
