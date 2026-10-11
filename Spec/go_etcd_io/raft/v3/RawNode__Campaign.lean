/- Lean-first (no Rocq counterpart).

## `RawNode.Campaign` (rawnode.go:83)

`Campaign()` is `rn.raft.Step(pb.Message{Type: MsgHup})`: the node starts an election
(or a pre-election, with `Config.PreVote`), unless it is a leader or cannot be one. The
client sees only the term, which moves up by at most one (`TermStep`); the committed log
handed out, the entries to persist and the queue `Advance` steps are kept, so a campaign
may come between `Ready` and `Advance`.

Go panics when the campaign wraps the term (`send` refuses a vote request of term `0`),
hence `rs.term + 1 < 2^64`.

Lean notes: like `RawNode.Propose.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
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

/-- See the file header. -/
abbrev RawNode.Campaign.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState),
  uint.Z rs.term + 1 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Campaign")) (Val #()))
  {{ (err : GoInterface) (t : w64), RET #err;
      "Hrn" ∷ ownRawNode γ rn id { rs with term := t } ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ ∗
      "%Herr" ∷ ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
