-- The copy for the part `KvNet/` of `Net/Spec/net/Conn__Read.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`c.Read(b)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`, with the end's
addresses `la`, `ra`), through the interface (a `*TCPConn`, whose `Read` is `conn`'s, promoted; Go's
`conn.Read`, over the model's `netFD.Read`): the extension's `Read` of `len(b)` bytes,
whose outcome (`ReadOutcome`, `GooseLang/Ext/Net/Impl.lean`, D1) the caller takes by a logically
atomic update over the end's state and the direction towards it (`netEnd`, `netDir`), then the
bytes copied into `b`. The update's result `Q r` is handed back with what the call returns
(`ReadOut`, `ReadErr`): `(len bs, nil)` and `b` starting with `bs` for bytes, `(0, io.EOF)` for EOF,
`(0, err)` for a failure of kind `k`, `err` an `*OpError{Op: "read", Source: la, Addr: ra}` whose
`Err` is the kind's (D14: `net.ErrClosed`, `poll.ErrDeadlineExceeded`'s value `ed`, or an
`*os.SyscallError` of `"read"`), `b` unchanged. Proved in `Net/Proof/net/Conn__Read.lean`.

(2026-11-24, Go-model overlays S6: decided overnight by the lead, for Upamanyu's review) It takes
`isPkgInit io` and `isPkgInit internal/poll`: Go's `conn.Read` wraps the error only `if err != nil
&& err != io.EOF`, which compares with `io.EOF`'s value (an `*errorString`, io's package fact) and
needs the deadline's error (`*DeadlineExceededError`, poll's) to be neither nil nor `io.EOF`.
-/
module

public import KvNet.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- What `c.Read(b)` returns for the extension's result `r`: the count `k` and `b`'s bytes after,
from its bytes before, `bs0`. -/
def ReadOut (bs0 : List w8) (r : ReadRes) (k : w64) (bs' : List w8) : Prop :=
  match r with
  | .bytes bs => sint.nat k = min bs0.length bs.length ∧
      bs' = bs.take bs0.length ++ bs0.drop bs.length
  | _ => k = 0 ∧ bs' = bs0

/-- `ReadOut` with the count as a signed integer (`sint.Z k`, not its natural part). -/
def ReadOutZ (bs0 : List w8) (r : ReadRes) (k : w64) (bs' : List w8) : Prop :=
  match r with
  | .bytes bs => sint.Z k = min bs0.length bs.length ∧
      bs' = bs.take bs0.length ++ bs0.drop bs.length
  | _ => k = 0 ∧ bs' = bs0

/-- The error `c.Read(b)` returns for the extension's result `r`: `nil` for bytes, `eof` (`io.EOF`)
for EOF, and the `*OpError` of the failure's kind. -/
def ReadErr (r : ReadRes) (eof la ra ed err : GoInterface) : IProp GF :=
  match r with
  | .bytes _ => iprop(⌜err = interface.nil⌝)
  | .eof => iprop(⌜err = eof⌝)
  | .err k => resErr (some k) go!"read" la ra (some ed) (· = go!"read") err

/-- See the file header. -/
abbrev Conn.Read.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : GoSlice)
    (bs0 : List w8) (eof ed : GoInterface) (Q : ReadRes → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.internal.poll ∗
      connAt (GF := GF) t cn s a la ra ∗ b ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (|={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d b.len.toNat r d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗ Q r) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Read" #t)) (Val #b))
  {{ (k : w64) (err : GoInterface), RET (PairV #k #err);
      ∃ (r : ReadRes) (bs' : List w8), Q r ∗ b ↦* bs' ∗ ⌜ReadOut bs0 r k bs'⌝ ∗
        ReadErr r eof la ra ed err }}

/-- `Conn.Read.spec` with two later credits in the post (from the steps after the extension's `Read`)
and the count exact (`ReadOutZ`):
for a caller whose own post follows the call at once (a stream reader's `Read` is the connection's,
`DialHTTPPath`'s `bufio.Reader`), to strip the later off the update's result. -/
abbrev Conn.Read.specLc : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : GoSlice)
    (bs0 : List w8) (eof ed : GoInterface) (Q : ReadRes → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.internal.poll ∗
      connAt (GF := GF) t cn s a la ra ∗ b ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (|={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d b.len.toNat r d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗ Q r) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Read" #t)) (Val #b))
  {{ (k : w64) (err : GoInterface), RET (PairV #k #err);
      ∃ (r : ReadRes) (bs' : List w8), Q r ∗ b ↦* bs' ∗ ⌜ReadOutZ bs0 r k bs'⌝ ∗
        ReadErr r eof la ra ed err ∗ £ 1 ∗ £ 1 }}

end spec

end net
end Perennial
