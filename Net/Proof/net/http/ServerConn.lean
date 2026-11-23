/-
The vocabulary of the model's server's connection (`conn`) and response (`response`) for net/http's
server up to a hijack (2026-11-23, `notes/dsverify-net-port-plan.md`, phase 5.2), beside the
connection reader's (`ConnReader.lean`):

* `srvConst s` (persistent): what the connection's methods read of its `*Server` `s`: its mutex
  (`s.mu`, over the set of active connections, `s.activeConn`, and of listeners), and its
  `ConnState` hook `nil` (no hook: `ListenAndServe`'s and `Serve`'s servers); the packages
  `time`, `sync`, `sync/atomic` initialized.
* `connMuInv c γh`: the invariant of the connection's mutex `c.mu`: its `hijackedv`, agreeing with
  a ghost variable (`γh`, half here, half with the serving thread, which learns from it after the
  handler that the connection was hijacked).
* `wPool sz` (persistent): `bufioWriter2kPool` (`sz = 2048`) or `bufioWriter4kPool` (`4096`) holds
  `*bufio.Writer`s holding nothing with a buffer of `sz` bytes (`bufio.rawWriter`); its `New` is
  `nil` (Go's zero `sync.Pool`). Given by net/http's initialization (not proved yet: a premise).
* `hjPre ...`: what `response.Hijack` needs (`response.Hijack.spec`), which `conn.serve` has when it
  calls the handler on a `CONNECT` request whose head `hs` it read; `hjDone ...`: what it gives
  back to the serving thread through the handler (`hijackOk`'s `D`).
-/
module

public import Net.Proof.net.http.ConnReader
public import Proof.bufio.RawWriter
public import Perennial.Proof.sync.PoolDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- A map field of a set of pointers (`map[*T]struct{}`): `nil` or a map. -/
def mapField (l : Loc) : IProp GF :=
  iprop(∃ m : GoMap, l ↦ m ∗ (⌜m = map.nil⌝ ∨ ∃ g : GMap Loc Unit, m ↦$ g))

/-- The invariant of the server's mutex (the parts the connection path uses). -/
def srvMuInv (s : Loc) : IProp GF :=
  iprop(mapField (structFieldRef net.http.Server go!"activeConn" s) ∗
    mapField (structFieldRef net.http.Server go!"listeners" s))

/-- See the file header. -/
def srvConst (s : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.time ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
    sync.isMutex (structFieldRef net.http.Server go!"mu" s) (srvMuInv s) ∗
    structFieldRef net.http.Server go!"ConnState" s ↦□ (func.nil : GoFunc))

instance srvConst_persistent (s : Loc) : Persistent (srvConst (GF := GF) s) := by
  unfold srvConst; infer_instance

/-- See the file header. -/
def connMuInv (c : Loc) (γh : GName) : IProp GF :=
  iprop(∃ b : Bool, structFieldRef net.http.conn go!"hijackedv" c ↦ b ∗ ghostVar γh (1 : Qp).half b)

/-- See the file header. -/
def wPoolP (sz : Nat) (v : GoAny) : IProp GF :=
  iprop(∃ bw : Loc, ⌜v = interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw⌝ ∗
    EtcdGrove.bufio.rawWriter bw sz)

/-- See the file header. -/
def wPools : IProp GF :=
  iprop(sync.isPool (globalAddr net.http.bufioWriter2kPool) func.nil iprop(True) (wPoolP 2048) ∗
    sync.isPool (globalAddr net.http.bufioWriter4kPool) func.nil iprop(True) (wPoolP 4096))

instance wPools_persistent : Persistent (wPools (GF := GF)) := by
  unfold wPools; infer_instance

end defs

end net.http
end Perennial
