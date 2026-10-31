/- Lean-first (no Rocq counterpart).

`getIDs(b)` (storage.go): what `putIDs` wrote at the start of `b` (`encIDs xs`), read back into a
fresh slice, the rest (a slice of `b`, which gives it back) and `ok`. Stated of bytes `putIDs`
wrote, so `ok` is `true`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Codec

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

/-- See the file header. -/
abbrev getIDs.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (xs : List w64) (r : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ b ↦*{dq} (encIDs xs ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.getIDs)) (Val #b))
  {{ (ids rest : GoSlice), RET (PairV (PairV #ids #rest) #true);
      ids ↦* xs ∗ rest ↦*{dq} r ∗ (rest ↦*{dq} r -∗ b ↦*{dq} (encIDs xs ++ r)) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
