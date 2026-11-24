-- The copy for the part `RaftNoAx/` of `Spec/strings/Join.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Port of `election_proof/spec_strings_Join.v` (feb5c73d4) (stage R4 of the raft v3.7 retarget, for `newRaft`).
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.InvStorage
public import Perennial.Proof.strings.JoinBounded

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `strings.Join(elems, sep)` of a fully owned slice of elements of at most `B` bytes each, with
`maxAddr * (B + |sep|) ≤ joinMax`: some string. Go's `Join` panics when its output's length
overflows an `int`; a fully owned slice has fewer than `maxAddr` elements, so per-element lengths
bound the output (Perennial's `strings.Join_owned_bounded_of`). `newRaft` joins the hexadecimal
node IDs (at most 16 bytes each) for a log line. Since 2026-11-24 (Perennial `8e9f1ee59`, real
`Join` with its length premise); until then any slice. -/
abbrev strings.Join.spec : Prop :=
  ∀ (elems : GoSlice) (xs : List GoString) (sep : GoString) (B : Nat),
  (∀ x ∈ xs, x.length ≤ B) → maxAddr.toNat * (B + sep.length) ≤ _root_.Perennial.strings.joinMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦* xs }}
    (App (App (Val #(functions _root_.Perennial.strings.Join [])) (Val #elems)) (Val #sep))
  {{ (s : GoString), RET #s; elems ↦* xs }}

end spec

end EtcdGrove
end Perennial
