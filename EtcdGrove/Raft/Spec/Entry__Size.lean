/- Port of election_proof/spec_Entry__Size.v (feb5c73d4).

Lean notes: the precondition is ascribed `(… : IProp GF)`, since with no `isPkgInit`
conjunct nothing else fixes the logic the points-to lives in (Rocq infers it from `Σ`).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `Entry.Size()` (pointer receiver): the protobuf-encoded size of an entry.

**Not translated.** `Perennial/Code/go_etcd_io/raft/v3/raftpb.lean` carries only the
message types, the enum constants and the field accessors; the gogoproto-generated
marshalling code (`Size`, `Marshal`, `Unmarshal`, ...) is not in the translated set, so
`raftpb.Assumptions` has no `MethodUnfold` for `Size` and the call cannot be stepped.
This axiom stands in for it, exactly as `Spec/slices_Sort.lean` does for `slices.Sort`.

It is reached on the election path: `raftLog.slice` applies `limitSize` to every slice
it returns and `limitSize` calls `ents[0].Size()` on any non-empty input, so
`hasUnappliedConfChanges`'s `scan` hits it whenever `applied < committed`.

The postcondition says **nothing about the value**: `limitSize` and `entsSize` only use
the sizes to decide where to cut a slice, and no caller on this path depends on where
the cut falls -- `scan` pages until `lo` reaches `hi` whatever the page sizes are. So
this is the weakest triple that lets the call be stepped: it owns the receiver (the
method reads every field through the pointer) and hands it back.

To discharge it: add `raftpb`'s `Size` methods to the translated set in
`new/etc/update-goose-new.py`, regenerate, and prove it from the body. -/
abbrev raftpb.Entry.Size.spec : Prop :=
  ∀ (e : Loc) (dq : DFrac) (ev : raftpb.Entry),
  {{ (e ↦{dq} ev : IProp GF) }}
    (App (Val (e @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; e ↦{dq} ev }}

end spec

end EtcdGrove
end Perennial
