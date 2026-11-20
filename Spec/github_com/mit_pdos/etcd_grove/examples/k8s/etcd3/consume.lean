/- Lean-first (no Rocq counterpart).

`consume(w, in)` (watch.go): reads the store watch `w` (`k8sWatch`, over the driver's objects) as
`in.Behavior` says, until its timer fires, `maxEvents` events or the channel closes, and returns the
events it received as the driver records them (`wes`, each `kWEvRel` of the store event `kes` it
models). The driver holds the watch live (`kLive`) and its Done token (`doneTok`, its context's
`PDone` being `donePD`), so every element's cancellation branch is refuted: the store events are
`kSeen` (a prefix of the ideal stream at a firing of the read update `Q`, or all Error events).
The events as received (`raw`, k8s 7g) are returned too, one for one, read-only, with views `rs` of
which the records are `toWEvL` (`toWEvent`'s post). It returns `Stop()` (`kStopOk`), `kLive` and the token, for `watchEvents`.
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
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev consume.spec : Prop :=
  ∀ (c : StoreCfg GF DObj) (wi : GoInterface) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (γd : GName) (sel : DObj → Bool) (emp : Bool)
    (inS : GoString → Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF) (x : Input),
  c.S = driverSpec → cd.PDone = donePD γd →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      k8sWatch c driverW wi γ cd sel emp inS m Q ∗ doneTok γd }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.consume)) (Val #wi))
      (Val #x))
  {{ (sl rsl : GoSlice), RET (PairV #sl #rsl);
      ∃ (rs : List k8s_correctness.REv) (kes : List (KWEv DObj)),
      wevsOwnM sl (rs.map k8s_correctness.toWEvL) ∗ k8s_correctness.evsRO rsl rs ∗
      ⌜List.Forall₂ kWEvRel kes (rs.map k8s_correctness.toWEvL)⌝ ∗ kSeen c sel emp inS m Q kes ∗
      kStopOk wi γ ∗ kLive γ ∗ doneTok γd }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
