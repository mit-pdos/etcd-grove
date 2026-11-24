/-
The vocabulary of the model's server's connection reader (`connReader`, `models/net/http/server.go`)
for net/http's server up to a hijack (2026-11-23, `notes/dsverify-net-port-plan.md`, phase 5.2): the
reader of a connection's head, then of nothing but its background read, which a `Hijack` aborts.

**The head and the dialer** (`headLaw P hs Z`, persistent): what the dialer of the connection writes
(its protocol `P`) is, as far as it goes, a prefix of the head `hs`, or `Z cn` holds, which the
acceptor refutes with its own end not yet written (`zLaw Z Q`: `Z cn` and `sendTok cn true Q []` are
not both). For net/rpc's dialers `hs` is `connectReq path` and `Z cn` the acceptor's answer written
(`reqProto`'s last clause): a dialer writes nothing past its head before the answer. So the
background read, started once the head is read, finds no byte while the handler has written
nothing (`hasByte` is refuted in `hijackLocked`).

**The connection reader** `cr`, with ghost names `γ : CrNames`:
* `crIs cr γ cn P hs Z` (persistent): `cr.mu` is a mutex whose invariant is `crInv`: `cr.cond`
  (made by the first `lock`, a `*sync.Cond` on `cr.mu` once set) and, by phase (`γ.ph`, a ghost
  variable, half here and half with the main thread), either nothing but the background reader's
  token (`token γ.bg`, phase "main": the main thread owns the fields), or the fields (`crBg`: phase
  "background", from `startBackgroundRead` to the abort): `conn`, `hasByte`, `inRead`, `aborted`,
  and while no read runs (`inRead` false) the token, the byte buffer and the reader's
  token at `R0` (half of `γ.r`) or, with a byte, `R0 ++ [b]` with `Z cn`; `R0 = hs`.
* `crConnOk cn` (persistent): what `handleReadErrorLocked` reads of the reader's `*conn` (here: only
  its `cancelCtx`, a cancel function callable at any time, and its `curReq`, an atomic pointer in
  an invariant holding `nil` or a response whose close notification is a mutex over a `nil`
  channel).
-/
module

public import Net.Proof.net.http.ServerDefs
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.CondDefs
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.context.Base
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

/-- The ghost names of a connection reader: its phase (`ph`), the background reader's token (`bg`)
and the bytes read when the background read started (`r`). -/
structure CrNames where
  ph : GName
  bg : GName
  r : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- What the server's reads need of the package state: `io.EOF`'s value (an `*errorString`) and
`poll.ErrDeadlineExceeded`'s. -/
def readEnv : IProp GF :=
  iprop(errors.newVar io.EOF go!"EOF" ∗ ∃ ed : GoInterface,
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed)

instance readEnv_persistent : Persistent (readEnv (GF := GF)) := by
  unfold readEnv; infer_instance

/-- See the file header. -/
def headLaw (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) : IProp GF :=
  iprop(□ ∀ (cn : Nat) (bs : List w8), P cn bs -∗ ⌜bs <+: hs⌝ ∨ Z cn)

instance headLaw_persistent (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) :
    Persistent (headLaw P hs Z) := by
  unfold headLaw; infer_instance

/-- See the file header. -/
def zLaw (Z : Nat → IProp GF) (Q : Proto GF) : IProp GF :=
  iprop(□ ∀ cn : Nat, Z cn -∗ sendTok (Gg := hG.goose_globalGS) cn true Q [] -∗ False)

instance zLaw_persistent (Z : Nat → IProp GF) (Q : Proto GF) : Persistent (zLaw Z Q) := by
  unfold zLaw; infer_instance

/-- A response's close notification: its mutex over a `nil` channel (no `CloseNotify`). -/
def respNotify (w : Loc) : IProp GF :=
  iprop(sync.isMutex (structFieldRef net.http.response go!"lazyCloseNotifyMu" w)
    iprop(∃ t : Bool, structFieldRef net.http.response go!"closeNotifyTriggered" w ↦ t ∗
      structFieldRef net.http.response go!"closeNotifyCh" w ↦ (chan.nil : GoChan)))

instance respNotify_persistent (w : Loc) : Persistent (respNotify (GF := GF) w) := by
  unfold respNotify; infer_instance

/-- See the file header. -/
def curReqInv (c : Loc) : IProp GF :=
  iprop(∃ v : Loc, sync.atomic.ownPointer (T' := net.http.response)
      (structFieldRef net.http.conn go!"curReq" c) (DFrac.own 1) v ∗
    (⌜v = null⌝ ∨ ⌜v ≠ null⌝ ∗ respNotify v))

def curReqN : Namespace := (nroot.@"net.http").@"curReq"

/-- See the file header. -/
def crConnOk (c : Loc) : IProp GF :=
  iprop(⌜c = null⌝ ∨ (∃ (f : GoFunc) (γc : context.ContextNames), ⌜c ≠ null⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
    structFieldRef net.http.conn go!"cancelCtx" c ↦□ f ∗ context.cancelSpec f γc iprop(True) ∗
    inv curReqN (curReqInv c)))

instance crConnOk_persistent (c : Loc) : Persistent (crConnOk (GF := GF) c) := by
  unfold crConnOk; infer_instance

/-- What the reader holds while no read runs: the byte buffer, and the reader's token, at `R0` with
no byte kept, or anywhere with `Z cn` (a byte read past the head). -/
def crRead (cr : Loc) (cn : Nat) (P : Proto GF) (Z : Nat → IProp GF) (R0 : List w8) (hb : Bool) :
    IProp GF :=
  iprop((∃ arr : GoArray w8 1, structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr) ∗
    ∃ R : List w8, recvTok (Gg := hG.goose_globalGS) cn true P R ∗
      (⌜R = R0 ∧ hb = false⌝ ∨ Z cn))

/-- The fields in the background phase (see the file header). -/
def crBg (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) :
    IProp GF :=
  iprop(∃ (c : Loc) (hb ir ab : Bool),
    structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
    structFieldRef net.http.connReader go!"hasByte" cr ↦ hb ∗
    structFieldRef net.http.connReader go!"inRead" cr ↦ ir ∗
    structFieldRef net.http.connReader go!"aborted" cr ↦ ab ∗
    ghostVar γ.r (1 : Qp).half hs ∗ crConnOk c ∗
    if ir then iprop(⌜hb = false⌝) else iprop(token γ.bg ∗ crRead cr cn P Z hs hb))

/-- The connection reader's invariant but its condition variable (by phase). -/
def crPh (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) :
    IProp GF :=
  iprop(∃ ph : Bool, ghostVar γ.ph (1 : Qp).half ph ∗
      if ph then crBg cr γ cn P hs Z else token γ.bg)

/-- The condition variable, once made. -/
def crCond (cr : Loc) (cv : Loc) : IProp GF :=
  iprop(⌜cv ≠ null⌝ ∗ structFieldRef net.http.connReader go!"cond" cr ↦□ cv ∗
    sync.isCond cv (interface.mk (go.GoType.PointerType sync.Mutex.ty)
      #(structFieldRef net.http.connReader go!"mu" cr)))

instance crCond_persistent (cr cv : Loc) : Persistent (crCond (GF := GF) cr cv) := by
  unfold crCond; infer_instance

/-- The connection reader's mutex invariant (see the file header). -/
def crInv (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) :
    IProp GF :=
  iprop((structFieldRef net.http.connReader go!"cond" cr ↦ (null : Loc) ∨ ∃ cv, crCond cr cv) ∗
    crPh cr γ cn P hs Z)

/-- The fields as the main thread owns them in the main phase, no read running (`inRead` false):
the reader's connection `c`, `hasByte` `hb`, `aborted`, and the reader's resources. -/
def crOwn (cr : Loc) (cn : Nat) (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) : IProp GF :=
  iprop(∃ (c : Loc) (hb ab : Bool),
    structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
    structFieldRef net.http.connReader go!"hasByte" cr ↦ hb ∗
    structFieldRef net.http.connReader go!"inRead" cr ↦ false ∗
    structFieldRef net.http.connReader go!"aborted" cr ↦ ab ∗
    crConnOk c ∗ crRead cr cn P Z hs hb)

/-- What a hijack leaves of the reader with the main thread: the main phase, the fields. -/
def crLeft (cr : Loc) (γ : CrNames) (hs : List w8) : IProp GF :=
  iprop(ghostVar γ.ph (1 : Qp).half false ∗ ghostVar γ.r (1 : Qp) hs ∗
    ∃ (c : Loc) (hb ab : Bool),
    structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
    structFieldRef net.http.connReader go!"hasByte" cr ↦ hb ∗
    structFieldRef net.http.connReader go!"inRead" cr ↦ false ∗
    structFieldRef net.http.connReader go!"aborted" cr ↦ ab ∗
    ∃ arr : GoArray w8 1, structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr)

/-- See the file header. -/
def crIs (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) :
    IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isMutex (structFieldRef net.http.connReader go!"mu" cr) (crInv cr γ cn P hs Z))

instance crIs_persistent (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8)
    (Z : Nat → IProp GF) : Persistent (crIs cr γ cn P hs Z) := by
  unfold crIs; infer_instance

end defs

end net.http
end Perennial
