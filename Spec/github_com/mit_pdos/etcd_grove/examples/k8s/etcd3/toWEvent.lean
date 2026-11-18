/- Lean-first (no Rocq counterpart).

`toWEvent(ev)` (watch.go): an event the store's watch delivered (`wevAt driverSpec driverW v e`) as
the driver records it: its type, and for any event but an Error event the object `kToWEv e`
(`kWEvRel`, what the bridge `streamOkL_of_kStreamOk` takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input WEvent)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev toWEvent.spec : Prop :=
  ∀ (v : k8s_io.apimachinery.pkg.watch.Event) (e : KWEv DObj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      wevAt driverSpec driverW v e }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toWEvent)) (Val #v))
  {{ (w : WEvent), RET #w; ⌜kWEvRel e (wevOf w)⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
