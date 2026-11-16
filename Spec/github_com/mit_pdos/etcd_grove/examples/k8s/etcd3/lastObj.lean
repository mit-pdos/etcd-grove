/- Lean-first (no Rocq counterpart).

`lastObj(evs)` (watch.go): the object of the last event that is not an Error or bad event
(`lastObjL`), or false.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev lastObj.spec : Prop :=
  ∀ (s : GoSlice) (evs : List WEv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      wevsOwn s evs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.lastObj)) (Val #s))
  {{ (o : Obj) (ok : Bool), RET (PairV #o #ok); ⌜lastObjL evs = if ok then some o else none⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
