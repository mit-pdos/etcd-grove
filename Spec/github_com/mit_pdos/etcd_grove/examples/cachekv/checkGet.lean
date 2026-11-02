/- Lean-first (no Rocq counterpart).

`checkGet(evs, r, kvs)` (cachekv.go; the cache's `Get` check, 2026-11-02): with the key-values
`kvs` (pointers `ps` holding `s`, `kvsHold`) what `CheckGetOk` says of the events `evs` at `r`
(each one's value its key's last event's at or below `r`, each key with such an event among them),
it returns: it does not panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.hasKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.lastVal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.cachekv go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- See the file header. -/
abbrev checkGet.spec : Prop :=
  ∀ (esl : GoSlice) (evs : List cev) (r : w64) (ksl : GoSlice) (ps : List Loc) (s : List EtcdKv),
  CheckGetOk evs r s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv ∗
      esl ↦*□ evs ∗ ksl ↦*□ ps ∗ kvsHold ps s }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.checkGet)) (Val #esl))
      (Val #r)) (Val #ksl))
  {{ RET #(); True }}

end spec

end cachekv
end EtcdGrove
end Perennial
