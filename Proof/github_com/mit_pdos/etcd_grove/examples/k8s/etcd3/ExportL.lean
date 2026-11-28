/-
Lean-first (no Rocq counterpart).

# The exported helpers of the etcd3 driver as Lean functions (k8s-dist K9 step 5, `notes/k8s-dist-k9.md` §2.8)

`PastRead` and `PinnedRead` (`examples/k8s/etcd3/export.go`), consumed by K8 and K12:
- `pastReadPubL x`: `x` reads at an explicit old revision: a List that reads at its parsed minimum
  resource version (`pastReadL`), or a watch from a parsed resource version above 0;
- `pinnedReadL x`: a paged List (a positive limit) or any watch.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section pure
variable [GooseExts]

/-- `PastRead(in)` (see the file header). -/
def pastReadPubL (x : Input) : Bool :=
  match parseRVD x.MinRV' with
  | none => false
  | some r => if x.Kind' = W64 4 then pastReadL x r else decide (x.Kind' = W64 5) && decide (r ≠ W64 0)

/-- `PinnedRead(in)` (see the file header). -/
def pinnedReadL (x : Input) : Bool :=
  (decide (x.Kind' = W64 4) && decide (0 < sint.Z x.Limit')) || decide (x.Kind' = W64 5)

end pure

end k8s_etcd3
end EtcdGrove
end Perennial
