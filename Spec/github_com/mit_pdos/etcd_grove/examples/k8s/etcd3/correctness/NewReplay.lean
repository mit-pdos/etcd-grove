/- Lean-first (no Rocq counterpart).

`NewReplay(initialState, history)` (`correctness/replay.go`): on a history every operation of which
`Step`s from the state the replay reached before it (`replayL init ops = some R`, with
`Model.Step`'s premises at each such state, `ReplayPre`), the replay `R`, frozen (`replayAt`), and
no error (k8s 7g step 5). Only the accepting run is specified: a failing step's error formats the
request and the response with `%+v` (structs holding closures), which the `fmt` model does not
cover, and `realCheck` calls it only on histories it replays (B4, `realReplay_ok`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ReplayRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev NewReplay.spec : Prop :=
  ∀ (mp : Loc) (init : RM) (sl : GoSlice)
    (vs : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (ops : List (Input × RResp)) (R : RReplay),
  ReplayPre init ops → replayL init ops = some R →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      modelAt mp init ∗ sl ↦*□ vs ∗ [∗list] v;op ∈ vs;ops, opRep v op }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewReplay))
      (Val #mp)) (Val #sl))
  {{ (rp : Loc) (err : GoInterface), RET (PairV #rp #err); ⌜err = GoInterface.nil⌝ ∗ replayAt rp R }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
