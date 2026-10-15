/- Port of election_proof/spec_raftLog__scan.v (feb5c73d4). -/
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

/-- `l.scan(lo, hi, pageSize, v)`: page through the entries at `[lo, hi)`, handing
each page to `v`; `nil` unless a page is empty or `v` errs (`log.go`).

The callback is described by `scanClosure f L I B` (`InvRaftlog.lean`), at the scanned
range `L = scanRange ls lo hi`: it gets each page (read-only) with the caller's state
`I acc` for the pages `acc` before it, and either returns `nil` with `I (acc ++ es)` or
stops the scan with an error `err` and `B err`. The "got 0 entries" error is dead
(`slice` returns a non-empty page on `lo < hi`), so `scan` returns `nil` after the
whole range (`I L`), or the callback's error (`B err`). (Until 2026-10-13 the callback had
to return `nil`, and got a fact `P` of every entry instead of the page's position.)

`lo <= hi` rather than `lo < hi`: with `lo = hi` the loop does not run and the result
is `nil` at once, and `hasUnappliedConfChanges` only knows
`applied + 1 <= committed + 1`. -/
abbrev raftLog.scan.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi pageSize : w64) (f : GoFunc)
    (I : List raftpb.Entry → IProp GF) (B : GoInterface → IProp GF),
  uint.Z ls.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo ≤ uint.Z hi ∧
    uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "HI" ∷ I [] ∗ "#Hf" ∷ □ scanClosure f (scanRange ls lo hi) I B }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"scan"))
      (Val #lo)) (Val #hi)) (Val #pageSize)) (Val #f))
  {{ (err : GoInterface), RET #err; ownRaftLog l ls ∗
      ((⌜err = interface.nil⌝ ∗ I (scanRange ls lo hi)) ∨ (⌜err ≠ interface.nil⌝ ∗ B err)) }}

end spec

end EtcdGrove
end Perennial
