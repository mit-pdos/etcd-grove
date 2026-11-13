/-
Shared definitions of the specs of `net`'s trusted models (`NetTcp/TrustedCode/net.lean`, project
nettcp's `net`, over the TCP extension `GooseLang/Ext/Tcp`): `net`'s package fact (`True`: the
package has no variables), the model's types as goose names them, and the handles:

* `connAt t cn s a` (persistent): the `*TCPConn` `t`'s `conn` holds the id of the end `s` of the
  connection `cn`, dialed to `a` (`tcpConnAt`); `isConn c cn s a`: the `Conn` `c` is such a `t`.
* `isListener li l` (persistent): the `Listener` `li` is a `*TCPListener` holding the listener
  id `l` (its state is the node's `tcpLis l a o`, which its owner keeps).
* `netErr err`: a failure's error, a non-nil `*OpError` as an `error`, which is not `io.EOF`.
-/
module

public import NetTcp.GeneratedProof.net
public import NetTcp.ManualProof.net
public import GooseLang.Ext.Tcp.Specs
public import Perennial.Proof.io.Base
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Tcp

namespace net

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net :=
  build_get_is_pkg_init_wf

theorem conn_ty_eq' : model.conn = conn.ty := by unfold conn.ty; rfl
theorem TCPConn_ty_eq : model.TCPConn = TCPConn.ty := by unfold TCPConn.ty; rfl
theorem TCPListener_ty_eq : model.TCPListener = TCPListener.ty := by unfold TCPListener.ty; rfl
theorem OpError_ty_eq : model.OpError = OpError.ty := by unfold OpError.ty; rfl
theorem Conn_ty_eq : model.Conn = Conn.ty := by unfold Conn.ty; rfl
theorem Listener_ty_eq : model.Listener = Listener.ty := by unfold Listener.ty; rfl

/-- The `*TCPConn` `t` is the end `s` of the connection `cn`, dialed to `a`. -/
def connAt (t : Loc) (cn : Nat) (s : Bool) (a : GoString) : IProp GF :=
  iprop(t ↦□ (TCPConn.mk (conn.mk (endId cn s))) ∗
    tcpConnAt (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn a)

instance connAt_persistent (t : Loc) (cn : Nat) (s : Bool) (a : GoString) :
    Persistent (connAt (GF := GF) t cn s a) := by
  unfold connAt; infer_instance

/-- The `Conn` `c` is the end `s` of the connection `cn`, dialed to `a`: a `*TCPConn` `t` with
`connAt t cn s a`. A method call on `c` resolves (`wp_auto`, once `c` is destructed) to the
`*TCPConn`'s method, the form the `Conn` specs are stated in. -/
def isConn (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) : IProp GF :=
  iprop(∃ t : Loc, ⌜c = interface.mkOk (go.GoType.PointerType TCPConn.ty) #t⌝ ∗ connAt t cn s a)

instance isConn_persistent (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) :
    Persistent (isConn (GF := GF) c cn s a) := by
  unfold isConn; infer_instance

/-- The `Listener` `li` is the listener `l` of this node. -/
def isListener (li : GoInterface) (l : w64) : IProp GF :=
  iprop(∃ t : Loc, ⌜li = interface.mkOk (go.GoType.PointerType TCPListener.ty) #t⌝ ∗
    t ↦□ (TCPListener.mk l))

instance isListener_persistent (li : GoInterface) (l : w64) :
    Persistent (isListener (GF := GF) li l) := by
  unfold isListener; infer_instance

/-- A failure's error: a non-nil `*OpError`. -/
def netErr (err : GoInterface) : Prop :=
  ∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType OpError.ty) #pe

theorem netErr_ne_nil {err : GoInterface} (h : netErr err) : err ≠ interface.nil := by
  obtain ⟨pe, rfl⟩ := h; intro h; cases h

end def_

end net
end Perennial
