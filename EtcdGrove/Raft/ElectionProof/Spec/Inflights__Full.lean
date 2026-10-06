/- Port of election_proof/spec_Inflights__Full.v (feb5c73d4). -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `in.Full()` -- no more messages may be dispatched (`tracker.Inflights.Full.impl`,
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`):

    in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)

The answer is `inflightsFull i` (`Defs.lean`), a function of the record -- which is why
`ownInflights` is indexed by one that determines it. The point is not this triple but
`Inflights.Add`, which *panics* unless `Full()` is false; stating `Add` truthfully needs
a name for "not full" that a caller can carry from the test to the use, and this is
it. -/
abbrev tracker.Inflights.Full.spec : Prop :=
  ∀ (l : Loc) (i : Inflights),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hin" ∷ ownInflights l i }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"Full")) (Val #()))
  {{ RET #(inflightsFull i); ownInflights l i }}

end spec

end EtcdGrove
end Perennial
