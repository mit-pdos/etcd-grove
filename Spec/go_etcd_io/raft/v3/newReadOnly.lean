/-
Port of election_proof/spec_newReadOnly.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `newReadOnly(option)` allocates a fresh `readOnly` object and returns it. It reads
and writes nothing else, so it owns nothing going in and hands back only the new object
(`ownReadOnly`, `InvMisc.lean`): no pending requests, no
acknowledgements, nothing confirmed (the option it stores is in no spec, so not in the
record; until 2026-10-08 a `safe` field said whether it is `ReadOnlySafe`). `reset`
installs it with `ownRaftPhys_readOnly`, which
needs the new object's ownership -- so the predicate can only be re-pointed at an
object that was actually allocated. (Until 2026-09-23 this spec consumed and returned
the whole of `own_raft_misc`, a raw piece of the raft struct.) -/
abbrev newReadOnly.spec : Prop :=
  ∀ (o : ReadOnlyOption),
  -- `ReadOnlySafe` (2026-10-12; `ownReadOnly` records it)
  o = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions newReadOnly [])) (Val #o))
  {{ (ro' : Loc), RET #ro';
      ownReadOnly ro' (ReadOnly.mk [] ∅ (W64 0)) }}

end spec

end EtcdGrove
end Perennial
