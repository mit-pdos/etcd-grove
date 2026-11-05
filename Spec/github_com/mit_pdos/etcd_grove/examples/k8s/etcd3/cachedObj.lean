/- Lean-first (no Rocq counterpart).

`cachedObj(in)` (k8setcd3.go; stage 7b): the input's cached object, a new copy (`nil` if the input
uses none).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev cachedObj.spec : Prop :=
  ∀ (x : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cachedObj)) (Val #x))
  {{ (cx : GoInterface), RET #cx;
      if x.UseCached' then
        iprop(∃ p : Loc, ⌜cx = interface.mkOk (go.GoType.PointerType objTyD) #p⌝ ∗ p ↦ x.Cached')
      else iprop(⌜cx = GoInterface.nil⌝) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
