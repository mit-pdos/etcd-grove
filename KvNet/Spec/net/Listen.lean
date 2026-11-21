-- The copy for the part `KvNet/` of `Net/Spec/net/Listen.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`net.Listen("tcp", a)` for a valid address `a` (`addrOk`, `GooseLang/Ext/Net/Impl.lean`, D6, D20:
any machine may listen at any valid address; the wildcards of D21, which the semantics allows, are
not covered), by the holder of `a`'s listening token (`netLisTok`, exclusive, one per valid address
from the extension's start resources: an atomic update gives it at the step and takes it back, so a
node that re-listens after every restart may keep it in an invariant; a proof that only one node's
invariant holds it shows that no other node ever listens at `a`), through `Listen.impl`
(`Net/TrustedCode/net.lean`): the extension's `Listen`. A new open listener `l` at `a`, as a
`Listener` (`isListener`, the node's `netLis l a true`, and `netLisAt l a`, persistent, which
`Accept` and `Close` need), or the
`*OpError{Op: "listen", Source: nil, Addr: x}`, `x` a `*TCPAddr`, whose `Err` is an
`*os.SyscallError` (`resErr`, D14). Proved in `Net/Proof/net/Listen.lean`.

The network `nw` is `"tcp"` or `"tcp4"` (`tcpNet`, D23): the same on the valid IPv4
addresses, the network kept in the connection or listener and put in its errors.
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev Listen.spec : Prop :=
  ∀ (nw : GoString), tcpNet nw → ∀ (a : GoString),
  {{ ⌜addrOk a = true⌝ ∗
      (|={⊤,∅}=> netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) a ∗
        (netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) a ={∅,⊤}=∗ True)) }}
    (App (App (Val (@! net.Listen)) (Val #nw)) (Val #a))
  {{ (li : GoInterface) (err : GoInterface), RET (PairV #li #err);
      (⌜err = interface.nil⌝ ∗ ∃ l, isListener li l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a) ∨
      (∃ x, netAddr x ∗ resErr (some .sys) go!"listen" interface.nil x none (fun _ => True) err) }}

end spec

end net
end Perennial
