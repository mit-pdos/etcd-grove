/- Lean-first (no Rocq counterpart).

`listOut(l)` (k8setcd3.go; stage 7e-4): the output of the list `l` (`driverListSpec`'s list at
`l`, with its items `os`, resource version, continue token and remaining count): `listObjOutL` of the
Go items the list holds (`itemRelD`: each the item's object at a resource version whose string is
the item's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListSpecD

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev listOut.spec : Prop :=
  ∀ (pl : Loc) (os : List (DObj × GoString)) (rv : w64) (cont : GoString) (rem : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      (driverListSpec (GF := GF)).listAtItems pl os rv cont rem }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOut)) (Val #pl))
  {{ (y : Output), RET #y;
      ⌜∃ vs : List Obj, List.Forall₂ itemRelD os vs ∧ y = listObjOutL vs rv cont rem⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
