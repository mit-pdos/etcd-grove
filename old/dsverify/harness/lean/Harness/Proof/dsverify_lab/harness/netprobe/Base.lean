/-
Shared definitions of the probe's proofs (`harness/netprobe/netprobe.go`; M2c,
`notes/harness-m2a.md`, "M2c result"):
* the package's `isPkgInit` (nothing of its own: `net`'s and `time`'s);
* the message `msg` (`netprobe.Msg`, as bytes) and the protocol of the server's address
  (`echoProto`, prefix-closed): in both directions, every byte sequence written on a connection to it is a
  prefix of `msg`. The client writes `msg`; the server writes back what it read, which the
  dialer's protocol says is a prefix of `msg`; so what the client reads back is one too, which is
  what its `check` tests.
-/
module

public import Harness.GeneratedProof.dsverify_lab.harness.netprobe
public import Harness.Proof.net.Listen
public import Harness.Proof.net.DialTimeout
public import Harness.Proof.net.TCPListener__Accept
public import Harness.Proof.net.TCPListener__Close
public import Harness.Proof.net.TCPConn__Read
public import Harness.Proof.net.TCPConn__Write
public import Harness.Proof.net.TCPConn__Close
public import Harness.Proof.net.TCPConn__SetReadDeadline
public import Harness.Proof.net.TCPConn__SetWriteDeadline
public import Harness.Proof.net.initialize
public import Perennial.Proof.time.Link
public import Harness.NetLib

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace dsverify_lab.harness.netprobe

/-- The server's address, `ServerAddr`. -/
abbrev serverAddr : GoString := go!"10.77.0.11:7000"

/-- The client's message, `Msg`, as bytes. -/
abbrev msg : List w8 := go!"hello, echo"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.dsverify_lab.harness.netprobe :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.dsverify_lab.harness.netprobe :=
  build_get_is_pkg_init_wf

/-- The protocol of both directions of a connection to the server: what is written is a prefix
of `msg`. -/
def echoProto : Proto GF := fun _ bs => iprop(⌜bs <+: msg⌝)

instance echoProto_persistent (cid : w64) (bs : List w8) :
    Persistent (echoProto (GF := GF) cid bs) := by
  unfold echoProto; infer_instance

/-- `echoProto` is closed under prefixes (`recvTok_proto_closed` applies). -/
theorem echoProto_closed : ProtoPrefixClosed (GF := GF) echoProto :=
  ProtoPrefixClosed.of_pure _ (fun _ => List.nil_prefix) (fun _ _ _ h h' => h.trans h')

theorem net_init_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe ⊢
      isPkgInit (PROP := IProp GF) pkg_id.net := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.dsverify_lab.harness.netprobe).trans ?_
  show iprop(isPkgInit pkg_id.net ∗ isPkgInit pkg_id.time ∗ True) ⊢ _
  iintro ⟨H, -, -⟩
  iexact H

end defs

end dsverify_lab.harness.netprobe

end Perennial
