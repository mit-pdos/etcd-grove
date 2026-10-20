/-
`(*ReplicationSet).String` (raft#168, `tracker/tracker.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvEpoch
public import Proof.go_etcd_io.raft.v3.InvStorage

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

/-- `r.String()` of a replication set holding `m` (read-only, as an installed epoch's): some
string (the sorted ids of the replication set in hexadecimal, `{a,b,c}`), which only the
leader's `Infof`s print. At most `2^62` ids (`RSM.strLen`), as `slices.Sort` needs: a tracker's
halves have (`EpochOkC.strLen`). -/
abbrev tracker.ReplicationSet.String.spec : Prop :=
  ∀ (l : Loc) (rv : tracker.ReplicationSet) (m : RSM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ l ↦□ rv ∗ ownRS rv m ∗
      ⌜(m.strLen : Int) ≤ 2 ^ 62⌝ }}
    (App (Val (l @!! go.GoType.PointerType tracker.ReplicationSet.ty @!! go!"String")) (Val #()))
  {{ (str : GoString), RET #str; True }}

end spec

end EtcdGrove
end Perennial
