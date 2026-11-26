/-
The counter instance's linked results: each function's proof applied to its callees' linked proofs
(`remote`'s `Link.lean`, lintest/counter's `New`, Perennial's `primitive`); each command's `main`
is applied to them in `TopLevelRobustness.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.step
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Model
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Codec
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Gen
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.attempt
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.CounterApply
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Server
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Client
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Orch
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.orch.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client0.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.client1.Main
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.cmd.server.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.New

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [NaInvG GF]
variable [π : NetProtoGS] [ρ : RemoteGS]

section pkg
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

theorem wp_step : step.spec (GF := GF) (hG := hG) := step.wp_proof
theorem wp_Model : Model.spec (GF := GF) (hG := hG) := Model.wp_proof wp_step
theorem wp_Codec : Codec.spec (GF := GF) (hG := hG) := Codec.wp_proof
theorem wp_Gen : Gen.spec (GF := GF) (hG := hG) :=
  Gen.wp_proof github_com.goose_lang.primitive.wp_RandomUint64
theorem wp_attempt : attempt.spec (GF := GF) (hG := hG) := attempt.wp_proof
theorem wp_CounterApply : CounterApply.spec (GF := GF) (hG := hG) := CounterApply.wp_proof
theorem wp_Server : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof EtcdGrove.lintest.counter.New.wp_proof wp_CounterApply wp_Codec wp_attempt
    EtcdGrove.remote.wp_Serve
theorem wp_Client : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof wp_Codec wp_attempt EtcdGrove.remote.wp_Do EtcdGrove.remote.wp_ServeClient
theorem wp_Orch : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof wp_Model wp_Codec wp_Gen wp_attempt EtcdGrove.remote.wp_Check

end pkg

end linked

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
