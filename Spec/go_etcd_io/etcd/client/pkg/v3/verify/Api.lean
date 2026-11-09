/-
# `client/pkg/v3/verify` (batch 1c): the `ETCD_VERIFY` assertions

* `verifyOff` (persistent): the environment variable `ETCD_VERIFY` is neither `all` nor `assert`,
  and nothing sets it (`EnableVerifications`, `os.Setenv`). A fact of the program's environment,
  stated by the program at its start (the closed theorem's premise); with it `Verify` never runs its
  check.
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.verify
public import Spec.PkgInit.go_etcd_io.etcd.client.pkg.v3.verify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Verify

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`ETCD_VERIFY` is off, for good** (persistent). -/
opaque verifyOff : IProp GF := iprop(True)

def verifyOff_persistent.spec : Prop := Persistent (verifyOff (GF := GF))

end res

end Verify
end EtcdGrove
end Perennial
