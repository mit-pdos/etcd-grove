/- Lean-first (no Rocq counterpart).

`(*Storage).InitialState()` (register.go:56): the empty hard state and the voters, no error.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Storage.InitialState.spec : Prop :=
  ∀ (s : Loc) (vsl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ s.[RStorage, go!"voters"] ↦□ vsl }}
    (App (Val (s @!! go.GoType.PointerType rStorageTy @!! go!"InitialState")) (Val #()))
  {{ RET (PairV (PairV #(zero_val raftpb.HardState)
        #({ (zero_val raftpb.ConfState) with Voters' := vsl } : raftpb.ConfState)) #interface.nil);
      True }}

end spec

end register
end EtcdGrove
end Perennial
