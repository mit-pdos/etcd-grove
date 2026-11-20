/-
Lean-first (no Rocq counterpart).

`(*Replay).validateGet(req, resp)` (`correctness/replay.go`) on the frozen replay `R`, the request
`realRequest(x)` of a get (`reqRep`) and a response of view `out` (`respRep`): `nil` when the pure
check accepts (`rreplayGetL R x out`), for an operation with its own premises (`opPre`) and a key
`PrepareKey` accepts (`keyOkL`: the model's `get` then answers a deep error on every state the loop
compares, as `reflect.DeepEqual`'s spec needs) (k8s 7g step 5). Only the accepting run is specified,
as for `Replay.Validate` (the rejection formats `%+v` of a `Response`).
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
abbrev Replay.validateGet.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)
    (ro : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) (x : Input) (out : RResp),
  x.Kind' ≠ W64 4 → x.Kind' ≠ W64 0 → x.Kind' ≠ W64 1 → x.Kind' ≠ W64 2 →
  opPre x out → keyOkL (k8s_etcd3.storeKeyL x.Key') = true → rreplayGetL R x out = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ reqRep r x ∗ respRep ro out }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay.ty) go!"validateGet" #rp))
      (Val #r)) (Val #ro))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
