/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

## `raft.committedEntryInCurrentTerm()` (raft.go:2054)

    return r.raftLog.zeroTermOnOutOfBounds(r.raftLog.term(r.raftLog.committed)) == r.Term

Whether the entry at the commit index is of the node's term. The commit index is always
within the log (`ownRaftLog`), so `term` answers it; with a nonzero term (a leader's, the
only caller's) the out-of-bounds `0` would not compare equal anyway.
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

/-- See the file header. -/
abbrev raft.committedEntryInCurrentTerm.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysC c r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"committedEntryInCurrentTerm"))
      (Val #()))
  {{ (b : Bool), RET #b;
      ownRaftPhysC c r id s ∗
      ⌜b = true ↔ plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed
                    = some s.term⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.committedEntryInCurrentTerm.spec` by `raft.committedEntryInCurrentTerm.spec_simple`. -/
abbrev raft.committedEntryInCurrentTerm.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.term ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"committedEntryInCurrentTerm"))
      (Val #()))
  {{ (b : Bool), RET #b;
      ownRaftPhys cfg r id s ∗
      ⌜b = true ↔ plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed
                    = some s.term⌝ }}

open Iris.ProofMode in
theorem raft.committedEntryInCurrentTerm.spec_simple
    (H : raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG)) :
    raft.committedEntryInCurrentTerm.specS (GF := GF) (hG := hG) := by
  intro cfg r id s Ht
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s Ht $$ [$Hpkg $Hphys]
  inext
  iintro %b ⟨Hphys, %Hb⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; exact Hb

end spec

end EtcdGrove
end Perennial
