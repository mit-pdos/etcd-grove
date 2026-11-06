/- Lean-first (no Rocq counterpart).

`lastVal(evs, key, r)` (etcd_cache.go; the cache's `Get` check, 2026-11-02): the value of the last of
the events `evs` of `key` at or below revision `r`, and whether there is one (`lastValL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.GetCheck

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

/-- See the file header. -/
abbrev lastVal.spec : Prop :=
  ∀ (sl : GoSlice) (evs : List cev) (dq : DFrac) (key : GoString) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.cache ∗
      sl ↦*{dq} evs }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.cache.lastVal)) (Val #sl))
      (Val #key)) (Val #r))
  {{ (v : GoString) (ok : Bool), RET (PairV #v #ok);
      sl ↦*{dq} evs ∗ ⌜(if ok then some v else none) = lastValL evs key r⌝ }}

end spec

end etcd_cache
end EtcdGrove
end Perennial
