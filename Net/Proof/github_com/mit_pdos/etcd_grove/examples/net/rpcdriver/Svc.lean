/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: its service's spec and the run's rpc world

The driver's one service, `"Svc"` with its method `Echo` (`service/service.go`), as Net's
`MethodSpec` (`Net/Proof/net/rpc/Proto.lean`), over its codec's bytes (`Wire.lean`).

**Each request id runs at most once** (the client's `call-success` check: `Runs == 1`). The client
hands out ids from a counter; each id comes with an exclusive token `idTok γid id` (an element of
the ghost map `γid`, whose authority the client's counter keeps: `Client`'s proof). A request's
deposit carries its id's token; the service's state (`Svc`'s `mu`, `isSvc`) keeps the token of every
id it has run, so a second run of an id would hold two tokens of it: it does not happen, and the
first run counts `1`.

**The method's spec** (`echoSpec`): on the encoding of `Args{id, data, fail}` with `id`'s token, the
continuation `Φ` gets the encoding of `Reply{id, data, 1}` with no message if `fail` is empty;
`fail` itself (with no reply) if it is not; and accepts every one of net/rpc's own error answers
(`srvErrMsg`: the service then meets `errOk`). The client's continuation is pure (`answerOk`): what
it may read back for the request it sent.

**The world** (`drvWorld`): the service at the server's two addresses (`TCPAddr`: raw net/rpc, no
handshake; `HTTPAddr`: behind the `CONNECT` handshake of `rpc.DialHTTP` and `rpc.HandleHTTP`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Wire
public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

/-- The server's addresses (`rpcdriver.go`'s `TCPAddr`, `HTTPAddr`). -/
abbrev tcpAddr : GoString := go!"127.0.0.1:7211"
abbrev httpAddr : GoString := go!"127.0.0.1:7212"

/-- What the client may read back for its request `Args{id, data, fail}`: the method's reply (no
message, `fail` empty), the method's error `fail` (no reply), or one of net/rpc's own error
answers. -/
def answerOk (id : w64) (data : List w8) (fail : GoString) (rep : List w8) (msg : GoString) :
    Prop :=
  (fail = [] ∧ msg = [] ∧ rep = encReply id data (W64 1)) ∨
  (fail ≠ [] ∧ msg = fail ∧ rep = []) ∨
  (net.rpc.srvErrMsg msg ∧ rep = [])

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The token of request id `id` (exclusive): an element of the ghost map `γid`. -/
def idTok (γid : GName) (id : w64) : IProp GF :=
  ghostMapElem (K := w64) (V := Unit) γid id (DFrac.own 1) ()

/-- `Svc.Echo`'s spec (see the file header). -/
def echoSpec (γid : GName) (args : List w8) (Φ : List w8 → GoString → IProp GF) : IProp GF :=
  iprop(∃ (id : w64) (data : List w8) (fail : GoString),
    ⌜args = encArgs id data fail⌝ ∗ idTok γid id ∗
    ((⌜fail = []⌝ -∗ Φ (encReply id data (W64 1)) []) ∧
      (⌜fail ≠ []⌝ -∗ Φ [] fail) ∧
      (∀ msg : GoString, ⌜net.rpc.srvErrMsg msg⌝ -∗ Φ [] msg)))

/-- The `Svc` service. -/
def echoSvc (γid : GName) : net.rpc.MethodSpec GF := fun m args Φ =>
  if m = go!"Echo" then echoSpec γid args Φ else iprop(False)

/-- The services of the run's addresses: `"Svc"` at both of the server's. -/
def drvSS (γid : GName) (a svc : GoString) : Option (net.rpc.MethodSpec GF) :=
  if (a = tcpAddr ∨ a = httpAddr) ∧ svc = go!"Svc" then some (echoSvc γid) else none

/-- The handshake at each address: `rpc.DialHTTP`'s `CONNECT` and its answer at `HTTPAddr`, none at
`TCPAddr`. -/
def drvHs (a : GoString) : List w8 :=
  if a = httpAddr then net.rpc.connectReq net.rpc.defaultRPCPath else []

def drvHsAns (a : GoString) : List w8 :=
  if a = httpAddr then net.rpc.connectAns else []

/-- The run's rpc world, over the connections' registry `reg`. -/
def drvWorld (γid reg : GName) : net.rpc.RpcWorld GF where
  SS := drvSS γid
  reg := reg
  hs := drvHs
  hsAns := drvHsAns

theorem drvWorld_tcp (γid reg : GName) :
    (drvWorld (GF := GF) γid reg).SS tcpAddr go!"Svc" = some (echoSvc γid) ∧
    (drvWorld (GF := GF) γid reg).hs tcpAddr = [] ∧
    (drvWorld (GF := GF) γid reg).hsAns tcpAddr = [] := by
  simp [drvWorld, drvSS, drvHs, drvHsAns]

theorem drvWorld_http (γid reg : GName) :
    (drvWorld (GF := GF) γid reg).SS httpAddr go!"Svc" = some (echoSvc γid) ∧
    (drvWorld (GF := GF) γid reg).hs httpAddr = net.rpc.connectReq net.rpc.defaultRPCPath ∧
    (drvWorld (GF := GF) γid reg).hsAns httpAddr = net.rpc.connectAns := by
  simp [drvWorld, drvSS, drvHs, drvHsAns]

/-- The only service of the run is `"Svc"`, with `echoSvc` (what `srvServes` asks of the server's
registrations). -/
theorem drvSS_only (γid : GName) (a svc : GoString) (S : net.rpc.MethodSpec GF)
    (h : drvSS γid a svc = some S) : svc = go!"Svc" ∧ S = echoSvc γid := by
  unfold drvSS at h
  split at h
  · rename_i hc
    exact ⟨hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

end specs

/-! ## Error answers (Net's `errOk`) -/

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem echoSvc_errOk (γid : GName) : ⊢ net.rpc.errOk (GF := GF) (echoSvc γid) := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %hmsg HS
  unfold echoSvc
  split
  · unfold echoSpec
    icases HS with ⟨%id, %data, %fail, %_, -, ⟨-, -, HE⟩⟩
    imodintro
    iapply HE
    ipureintro; exact hmsg
  · iexfalso; iexact HS

end errs

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

end Perennial
