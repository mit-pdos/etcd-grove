/-
gogo `proto`'s registration specs (`Spec.lean`'s class `Hyps`; until dsv-fix4 a premise of rabia's
statement) **hold**, from the per-function trust-boundary axioms (`RegisterEnum.lean`,
`RegisterType.lean`, `RegisterFile.lean`). A linking module: rabia's top-level proof discharges the
former premise with `hyps_holds`.
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.proto.RegisterEnum
public import Dsverify.Proof.github_com.gogo.protobuf.proto.RegisterType
public import Dsverify.Proof.github_com.gogo.protobuf.proto.RegisterFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.gogo.protobuf.proto

/-- **gogo `proto.Hyps` holds** (a theorem, not an instance): the file header. -/
theorem hyps_holds [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics] : Hyps GF :=
  ⟨RegisterEnum.wp_proofMsgType, RegisterType.wp_proof, RegisterFile.wp_proof⟩

end github_com.gogo.protobuf.proto
end Perennial
