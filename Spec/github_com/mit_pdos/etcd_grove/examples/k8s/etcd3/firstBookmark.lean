/- Lean-first (no Rocq counterpart).

`firstBookmark(evs)` (watch.go): the index of the first bookmark, or `-1`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev firstBookmark.spec : Prop :=
  ∀ (s : GoSlice) (evs : List WEv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ wevsOwn s evs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.firstBookmark)) (Val #s))
  {{ (b : w64), RET #b; ⌜sint.Z b = match evs.findIdx? (fun e => e.t = 3) with
      | none => -1
      | some k => (k : Int)⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
