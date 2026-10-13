/- Lean-first (no Rocq counterpart, 2026-10-13). -/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rn.BasicStatus()` (rawnode.go): `getBasicStatus(rn.raft)`, read-only. What a client
can know of it, in terms of `RNState`: the node's id and term; the applied index at most
the length of the committed log handed out so far (`delivered`), which is at most the
commit index, itself at least the commit lower bound `clb`. (The rest -- vote, leader,
role, leader-transfer target -- is of the node's hidden physical state.) -/
abbrev RawNode.BasicStatus.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"BasicStatus")) (Val #()))
  {{ (bs : BasicStatus), RET #bs;
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "%Hbs" ∷ ⌜bs.ID' = id ∧ bs.HardState'.Term' = rs.term ∧
        uint.Z bs.Applied' ≤ (rs.delivered.length : Int) ∧
        (rs.delivered.length : Int) ≤ uint.Z bs.HardState'.Commit' ∧
        uint.Z rs.clb ≤ uint.Z bs.HardState'.Commit'⌝ }}

end spec

end EtcdGrove
end Perennial
