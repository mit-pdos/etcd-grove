/-
`strings.SplitN(s, sep, n)` (Perennial models `strings` but does not specify `SplitN`; item 5:
`clientv3`'s `authority`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `strings.SplitN(s, sep, n)`: some owned slice of strings. -/
abbrev strings.SplitN.spec : Prop :=
  ∀ (s sep : GoString) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (App (Val (@! _root_.Perennial.strings.SplitN)) (Val #s)) (Val #sep)) (Val #n))
  {{ (sl : GoSlice), RET #sl; ∃ xs : List GoString, sl ↦* xs }}

end spec

end EtcdGrove
end Perennial
