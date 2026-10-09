/-
Port of `election_proof/spec_raftLog__matchTerm.v` (feb5c73d4).

Lean notes: `raft.entryID.t` is `entryID`; `plog_matches`/`plog_term_at` are
`PlogMatches`/`plogTermAt` (`Plog.lean`); `bool_decide` is `decide`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.Plog

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

/-- `l.matchTerm(id)`: whether the log has term `id.term` at `id.index` --
`PlogMatches` (`Plog.lean`) of the log the protocol sees.

The body (`raftLog.matchTerm.impl`, `Code/go_etcd_io/raft/v3.lean`; Rocq
new/code/go_etcd_io/raft/v3.v:1159) is `t, err := l.term(id.index); if err != nil {
return false }; return t == id.term`. `term`'s spec makes both halves exact: the error
is non-`nil` exactly when `id.index` is outside `[prev.index, last]`, where
`plogTermAt` is `none`, and otherwise `t` is `plogTermAt`'s value. No premise, no
panic. -/
abbrev raftLog.matchTerm.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (id : entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"matchTerm")) (Val #id))
  {{ (b : Bool), RET #b;
      ownRaftLog l ls ∗
      ⌜b = decide (PlogMatches ls.prev (ls.sents ++ ls.uents) id)⌝ }}

end spec

end EtcdGrove
end Perennial
