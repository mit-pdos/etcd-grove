/-
Port of `election_proof/spec_unstable__slice.v`.
-/
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

/-- `u.slice(lo, hi)`: the entries at `[lo, hi)` of the unstable suffix, as a
three-index sub-slice `u.entries[lo-off : hi-off : hi-off]` of the entry slice.

The result **aliases** `u.entries`, and is handed out read-only and for good
(`s ↦*□ es`): `ownUnstable` holds the entries read-only, because nothing ever writes
one again (`InvRaftlog.lean`). Its capacity equals its length (that is what the third
index buys: an `append` to the result reallocates instead of writing into the suffix's
slack), which `raftLog.slice` relies on through `extend`. (Until 2026-09-29 the
sub-slice was lent, with a wand back, and `ownUnstable` carried a `page` argument
recording the loan.)

The entries are described only as far as the callers need: their number, and that each
is an entry of the suffix. `lo < hi` is required rather than `lo <= hi` so that the
result is non-empty, which the ownership transfer needs (see `ownSlice_same_ptr_len`)
and which `raftLog.scan` needs anyway. -/
abbrev unstable.slice.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry) (lo hi : w64),
  uint.Z uv.offset' ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
    uint.Z hi ≤ uint.Z uv.offset' + (uents.length : Int) →
  uint.Z uv.offset' + (uents.length : Int) < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hun" ∷ ownUnstable u uv uents }}
    (App (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"slice"))
      (Val #lo)) (Val #hi))
  {{ (s : GoSlice) (es : List raftpb.Entry), RET #s;
      ownUnstable u uv uents ∗ s ↦*□ es ∗
      ⌜(es.length : Int) = uint.Z hi - uint.Z lo ∧
        (∀ e, e ∈ es → e ∈ uents) ∧
        s.cap = s.len⌝ }}

end spec

end EtcdGrove
end Perennial
