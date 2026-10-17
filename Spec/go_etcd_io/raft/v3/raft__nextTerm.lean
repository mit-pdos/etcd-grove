/- (PR raft#86) The new `raft.nextTerm`. -/
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

/-- `r.nextTerm()` (PR raft#86) reads `r.Term` and returns the next epoch's term with a random
low half: `nextTermOf r.Term x` (`Defs.lean`) for a draw `x` of the global RNG, about which
nothing is said (`nextTermOf` keeps its low 16 bits only). It changes nothing.
`nextTermOf_bounds` is what callers use: below the last epoch the result is later than
`r.Term`, by less than `2^17`; `nextTermOf_wraps`: in the last epoch it wraps below it. -/
abbrev raft.nextTerm.spec : Prop :=
  ∀ (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"nextTerm")) (Val #()))
  {{ (x : w64), RET #(nextTermOf s.term x); ownRaftPhysCV c V r id s }}

end spec

end EtcdGrove
end Perennial
