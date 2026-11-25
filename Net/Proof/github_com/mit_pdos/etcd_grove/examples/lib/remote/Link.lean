/-
`examples/lib/remote`'s linked results: every function's proof applied to its callees' linked
proofs (the frame helpers' in `FramesLinked.lean`, the net package's, Perennial's `time` and
`primitive`, lintest's `CounterClock`, perclient's `Run`). The exported results are `wp_Check`,
`wp_ServeClient`, `wp_Serve`, `wp_Do` (a client node whose operation calls another node) and
`wp_Report` (an orchestrator's call of a client machine's loop, for its report).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.FramesLinked
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.hang
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.deadline
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.attempt
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Do
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Report
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.listen
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.serveConn
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Serve
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Run
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Proof.net.DialTimeout
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__SetDeadline
public import Net.Proof.net.Conn__Close
public import Perennial.Proof.time.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace EtcdGrove.remote

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [lintest_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]
variable [perclient_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Assumptions]
variable [NaInvG GF]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem wp_hang : hang.spec (GF := GF) (hG := hG) := hang.wp_proof

theorem wp_deadline : deadline.spec (GF := GF) (hG := hG) :=
  deadline.wp_proof time.wp_Now time.Time.wp_Add

theorem wp_attempt : attempt.spec (GF := GF) (hG := hG) (I := I) (O := O) :=
  attempt.wp_proof net.DialTimeout.wp_proof net.Conn.SetDeadline.wp_proof net.Conn.Close.wp_proof
    wp_deadline wp_writeFrame wp_readFrame

theorem wp_Do : Do.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O) :=
  Do.wp_proof wp_attempt wp_hang github_com.goose_lang.primitive.wp_NewProph
    github_com.goose_lang.primitive.ProphId.wp_ResolveU64

theorem wp_Report : Report.spec (GF := GF) (hG := hG) (I := I) (O := O) :=
  Report.wp_proof wp_attempt wp_hang

theorem wp_listen : listen.spec (GF := GF) (hG := hG) (I := I) (O := O) :=
  listen.wp_proof net.Listen.wp_proof time.wp_Sleep

theorem wp_serveConn : serveConn.spec (GF := GF) (hG := hG) (I := I) (O := O) :=
  serveConn.wp_proof wp_deadline net.Conn.SetDeadline.wp_proof wp_readFrame wp_writeFrame
    net.Conn.Close.wp_proof

theorem wp_Serve : Serve.spec (GF := GF) (hG := hG) (I := I) (O := O) :=
  Serve.wp_proof wp_listen net.Listener.Accept.wp_proof wp_serveConn

theorem wp_ServeClient : ServeClient.spec (GF := GF) (hG := hG) (I := I) (O := O) :=
  ServeClient.wp_proof wp_Serve

theorem wp_Run : Run.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O) :=
  Run.wp_proof wp_Do EtcdGrove.perclient.wp_Run EtcdGrove.lintest.wp_CounterClock

theorem wp_Check : Check.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O) :=
  Check.wp_proof wp_Run

end linked

end EtcdGrove.remote
end Perennial
