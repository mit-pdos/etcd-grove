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

/-- The names and places of a connection being served, up to its hijack (`hjPre`). -/
structure HjNames where
  /-- The connection's reader's ghost names. -/
  γ : CrNames
  /-- The hijacked flag's ghost variable (`connMuInv`). -/
  γh : GName
  /-- The response, the connection, its reader, its server. -/
  w : Loc
  c : Loc
  cr : Loc
  s : Loc
  /-- The connection's `*TCPConn`, its number, the address it was dialed to, its end's addresses. -/
  t : Loc
  cn : Nat
  a : GoString
  la : GoInterface
  ra : GoInterface
  /-- `aLongTimeAgo`'s value; the connection's buffered reader and writer; the response's writer. -/
  tm : time.Time
  br : Loc
  bw : Loc
  ww : Loc

/-- What `Hijack` needs of the response `w` (its `handlerDone` false, no expect-continue reader,
nothing written, its buffered writer of 2048 bytes), of its connection (its mutex, the hijacked flag
false, its reader in the background phase, its writer of 4096 bytes holding nothing, its server)
and of the network (nothing written yet, the reader's protocol facts `zLaw`): see the file
header. -/
def hjPre (N : HjNames) (P Q : Proto GF) (hs : List w8) (Z : Nat → IProp GF) : IProp GF :=
  iprop(sync.atomic.ownBool (structFieldRef net.http.response go!"handlerDone" N.w) (DFrac.own 1)
      false ∗
    structFieldRef net.http.response go!"ecReader" N.w ↦ (null : Loc) ∗
    structFieldRef net.http.response go!"wroteHeader" N.w ↦ false ∗
    structFieldRef net.http.response go!"conn" N.w ↦□ N.c ∗
    structFieldRef net.http.response go!"w" N.w ↦ N.ww ∗ EtcdGrove.bufio.rawWriter N.ww 2048 ∗
    sync.isMutex (structFieldRef net.http.conn go!"mu" N.c) (connMuInv N.c N.γh) ∗
    ghostVar N.γh (1 : Qp).half false ∗
    structFieldRef net.http.conn go!"r" N.c ↦□ N.cr ∗
    structFieldRef net.http.conn go!"rwc" N.c ↦□
      interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #N.t ∗
    structFieldRef net.http.conn go!"bufr" N.c ↦□ N.br ∗
    structFieldRef net.http.conn go!"bufw" N.c ↦□ N.bw ∗ EtcdGrove.bufio.rawWriter N.bw 4096 ∗
    structFieldRef net.http.conn go!"server" N.c ↦□ N.s ∗ srvConst N.s ∗
    (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" N.c)
      (DFrac.own 1) v) ∗
    crIs N.cr N.γ N.cn P hs Z ∗ globalAddr net.http.aLongTimeAgo ↦□ N.tm ∗
    structFieldRef net.http.connReader go!"rwc" N.cr ↦□
      interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #N.t ∗
    ghostVar N.γ.ph (1 : Qp).half true ∗ ghostVar N.γ.r (1 : Qp).half hs ∗
    connAt N.t N.cn true N.a N.la N.ra ∗ sendTok (Gg := hG.goose_globalGS) N.cn true Q [] ∗
    connFresh (Gg := hG.goose_globalGS) N.cn true ∗ zLaw Z Q ∗ wPools)

/-- What a hijack gives back to the serving thread (`hijackOk`'s `D`): the hijacked flag, the
reader's fields, the connection's state word, the response's `handlerDone`. -/
def hjDone (N : HjNames) (hs : List w8) : IProp GF :=
  iprop(ghostVar N.γh (1 : Qp).half true ∗ crLeft N.cr N.γ hs ∗
    (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" N.c)
      (DFrac.own 1) v) ∗
    sync.atomic.ownBool (structFieldRef net.http.response go!"handlerDone" N.w) (DFrac.own 1) false)

end defs

end net.http
end Perennial
