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

/-- `u.doEntriesNeedCompaction(k)` (`log_unstable.go:179`, raft#96): whether to copy the entries
after the first `k` into a fresh array -- true if `k > cap(u.entries)/2`, or else if the first
`k` entries' encoded sizes (`proto.Size`) sum to more than half of all the entries'. Read-only:
the state is unchanged. The answer is left unspecified: the capacity is not part of the state
(`UnstableSt`) and the sizes are not fixed by `proto.SizeEntry.spec`, and either answer is safe
for the caller (`shrinkEntriesSlice`). Any `k` (the loop only compares indices with it; the sums
are `int` and wrap, which only changes the answer). -/
abbrev unstable.doEntriesNeedCompaction.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"doEntriesNeedCompaction")) (Val #k))
  {{ (b : Bool), RET #b; ownUnstable u us }}

end spec

end EtcdGrove
end Perennial
