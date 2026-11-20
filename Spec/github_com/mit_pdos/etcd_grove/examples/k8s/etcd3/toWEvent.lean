/- Lean-first (no Rocq counterpart).

`toWEvent(ev)` (watch.go): an event the store's watch delivered (`wevAt driverSpec driverW v e`) as
the driver records it: its type, and for any event but an Error event the object `kToWEv e`
(`kWEvRel`, what the bridge `streamOkL_of_kStreamOk` takes); and the event as Kubernetes' checker
reads it (k8s 7g): a view `r` (`evRep`, the object frozen: the driver never writes a received
object) of which the record is `toWEvL r`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep

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
  {{ (w : WEvent), RET #w; ∃ r : k8s_correctness.REv,
      ⌜kWEvRel e (wevOf w) ∧ wevOf w = k8s_correctness.toWEvL r⌝ ∗ k8s_correctness.evRep v r }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
