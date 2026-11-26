/-
`internal/mem.newBinaryTiered(f, fallback, exps...)` (grpc-mem, 2026-11-26): the binary-tiered pool
`mem`'s `init` builds (through `NewBinaryTieredBufferPool`).
-/
module

public import GeneratedProof.google_golang_org.grpc.internal.mem
public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `newBinaryTiered(f, fallback, exps...)` of exponents at most `maxExponent` (`uintSize - 2`, `62`: no
`fmt.Errorf`) and a pool factory `f` whose calls return a pool returns a new pool and no error. Its
reads of `uintSize` are through `internal/mem`'s package fact. -/
abbrev grpc.internal.mem.newBinaryTiered.spec : Prop :=
  ∀ (f : GoFunc) (fb : GoInterface) (s : GoSlice) (xs : List w8),
  (∀ x ∈ xs, uint.Z x ≤ 62) → xs.length ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.mem ∗ s ↦* xs ∗
      □ (∀ n : w64, WP (App (Val #f) (Val #n)) {{ v, ⌜∃ i : GoInterface, v = #i⌝ }}) }}
    (App (App (App (Val (@! google_golang_org.grpc.internal.mem.newBinaryTiered)) (Val #f)) (Val #fb))
      (Val #s))
  {{ (l : Loc), RET (PairV #l #(interface.nil : GoInterface)); True }}

end spec

end EtcdGrove
end Perennial
