/- Lean-first (no Rocq counterpart).

`fits(es)` (kv.go): whether appending `es` keeps a storage's log within `2^61`
(`MemoryStorage.Append`'s premise). raft v3.7 (2026-10-16, stage R6b): `es` is a `[]*pb.Entry`
(`entsPts`, at any fraction; the first entry's index read through `GetIndex`).
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

/-- `MemoryStorage.Append`'s premise on the batch. -/
def FitsOk (es : List EntryM) : Prop :=
  ∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ 2 ^ 61

/-- See the file header. -/
abbrev fits.spec : Prop :=
  ∀ (sl : GoSlice) (es : List EntryM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗
      entsPts sl dq es }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.fits)) (Val #sl))
  {{ (b : Bool), RET #b; entsPts sl dq es ∗ ⌜b = true → FitsOk es⌝ }}

end spec

end kvwitness
end EtcdGrove
end Perennial
