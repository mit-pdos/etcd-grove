/- Port of election_proof/spec_raftLog__scan.v. -/
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

/-- `l.scan(lo, hi, pageSize, v)`: page through the entries at `[lo, hi)`, handing
each page to `v`; `nil` unless a page is empty or `v` errs (`log.go`).

The callback is described by `scanClosure f I P` (`InvRaftlog.lean`): it gets each
page (read-only), with `I` and the fact that every entry on the page satisfies `P` --
which follows from `∀ e ∈ sents ++ uents, P e`, the premise, because every page is a
sub-list of the log -- and must return `nil`. With that, the "got 0 entries" error is
dead (`slice` returns a non-empty page on `lo < hi`) and so is the propagated callback
error, whence `RET #interface.nil`.

`lo <= hi` rather than `lo < hi`: with `lo = hi` the loop does not run and the result
is `nil` at once, and `hasUnappliedConfChanges` only knows
`applied + 1 <= committed + 1`. -/
abbrev raftLog.scan.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi pageSize : w64) (f : GoFunc)
    (I : IProp GF) (P : raftpb.Entry → Prop),
  uint.Z ls.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo ≤ uint.Z hi ∧
    uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1 →
  (∀ e ∈ ls.sents ++ ls.uents, P e) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "HI" ∷ I ∗ "#Hf" ∷ □ scanClosure f I P }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"scan"))
      (Val #lo)) (Val #hi)) (Val #pageSize)) (Val #f))
  {{ RET #interface.nil; ownRaftLog l ls ∗ I }}

end spec

end EtcdGrove
end Perennial
