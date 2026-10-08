/-
Port of election_proof/spec_raftLog__zeroTermOnOutOfBounds.v (feb5c73d4).

Lean notes:
* The reference `raftLog__zeroTermOnOutOfBoundsⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:1393`
  is to the Lean generated code `raftLog.zeroTermOnOutOfBounds.impl`; Rocq's
  `is_initialized`/`is_new_error` (`v3_proof/base.v`) are this repository's
  `Proof/go_etcd_io/raft/v3/Base.lean`; `global_addr` is `globalAddr`.
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

/-- `l.zeroTermOnOutOfBounds(t, err)`: `t` for a `nil` error, `0` for `ErrCompacted` /
`ErrUnavailable`.

The body (`raftLog.zeroTermOnOutOfBounds.impl`, `Code/go_etcd_io/raft/v3.lean`)
returns `t` for `err == nil`, `0` for `err == ErrCompacted || err == ErrUnavailable`,
and `Panicf`s otherwise. The premise -- `err` is `nil` or the value of one of the two
globals -- is exactly what `raftLog.term`'s last conjunct gives, and every caller passes
`term`'s result straight in.

Until 2026-10-01 only the `nil` case was specified (as a pure premise): comparing a
non-`nil` `err` against `ErrCompacted` is stuck on `CheckComparable` unless the dynamic
type is known to be a pointer, and the package-init predicate did not say so. It now
does (`is_new_error` for both globals, `Proof/go_etcd_io/raft/v3/Base.lean`). Widened for
`handleAppendEntries`, whose reject path calls `zeroTermOnOutOfBounds(term(m.Index))`
with `m.Index` possibly past the last index, i.e. with `ErrUnavailable`. The result only
feeds a `Debugf` there (and an `Infof` in `findConflict`), so all that is said about it
is that it is `t` on the `nil` branch.

The receiver is read only on the `Panicf` path, so the spec needs no ownership of the
log. -/
abbrev raftLog.zeroTermOnOutOfBounds.spec : Prop :=
  ∀ (l : Loc) (t : w64) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "#Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrCompacted ↦□ err ∨
                 globalAddr ErrUnavailable ↦□ err) }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"zeroTermOnOutOfBounds"))
      (Val #t)) (Val #err))
  {{ (t' : w64), RET #t'; ⌜err = interface.nil → t' = t⌝ }}

end spec

end EtcdGrove
end Perennial
