/-
Port of `election_proof/spec_unstable__truncateAndAppend.v`.
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

/-- `u.truncateAndAppend(ents)`: splice a batch into the unstable suffix
(`unstable.truncateAndAppend.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`).

The body switches on where the batch starts, `fromIndex = ents[0].Index`:

  - `fromIndex == u.offset+len(u.entries)`: it continues the suffix, so
    `u.entries = append(u.entries, ents...)`;
  - `fromIndex <= u.offset`: it replaces the suffix outright;
  - otherwise: keep `u.entries[:fromIndex]` and append.

Only the first is specified, and the premise `Hcont` is exactly its guard. That is not
a weakening of what the function does: the other two arms truncate, and the only caller
in this development is `raftLog.append`, which is called from `appendEntry` with
indices that continue the log by construction (`appendEntry` stamps `lastIndex()+1+i`
into every entry before calling it). Both other arms also start with an `Infof`, which
is fine, but they would need a spec saying which entries survive -- state it when a
`MsgApp` path needs it.

Ownership. A pointer-receiver method that *writes* `u.entries` needs the receiver's
fields (`notes/gotchas.md`), so `u ↦ uv` is here, and the suffix's own slice comes with
its capacity: Go's `append` may reallocate, which is why the new slice value `sl` is
existential in the postcondition and the struct comes back at
`{ uv with entries' := sl }`. The batch `es` is *lent* -- `append` copies the values --
so it is returned unchanged at the caller's fraction.

No no-wrap premise is needed for the guard's `u.offset+len(u.entries)`: `Hcont`
equates it with `uint.Z` of a `w64`, so it is below `2^64` already. -/
abbrev unstable.truncateAndAppend.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents ents : List raftpb.Entry)
    (e0 : raftpb.Entry) (es : GoSlice) (dq : DFrac),
  ents[0]? = some e0 →
  uint.Z e0.Index' = uint.Z uv.offset' + (uents.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents ∗
      "Hes" ∷ es ↦*{dq} ents }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"truncateAndAppend"))
      (Val #es))
  {{ (sl : GoSlice), RET #();
      ownUnstable u { uv with entries' := sl } (uents ++ ents) ∗
      es ↦*{dq} ents }}

end spec

end EtcdGrove
end Perennial
