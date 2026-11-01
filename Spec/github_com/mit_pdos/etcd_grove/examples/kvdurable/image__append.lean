/- Lean-first (no Rocq counterpart).

`m.append(entries)` (storage.go): `MemoryStorage.Append` of the entries `es` (consecutive from index
`k`, the slice only read) on the image: it holds `imgAppend I k es` (no change if there are none or
all are at or below the log's start; otherwise those above the start replace the log's from the
first of them on). It does not panic: the entries start at most one past the log's last index (when
there are any), and the log with them stays within a Go slice's length.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev image.append.spec : Prop :=
  ∀ (p : Loc) (I : StorFile) (s : GoSlice) (dq : DFrac) (k : Nat) (es : List EntryM),
  (∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j) →
  (es ≠ [] → k ≤ uint.nat I.prev + 1 + I.ents.length) →
  uint.nat I.prev + 1 + I.ents.length + es.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      ownImage p I ∗ entsPts s dq es }}
    (App (Val (p @!! go.GoType.PointerType kImageTy @!! go!"append")) (Val #s))
  {{ RET #(); ownImage p (imgAppend I k es) ∗ entsPts s dq es }}

end spec

end kvdurable
end EtcdGrove
end Perennial
