/-
The lab's connection specs the replica's transport and the client's `Disconnect` name
(dsverify-lab `harness/lean/Harness/Spec/net/TCPConn__{RemoteAddr,Close}.lean`, `Harness/Proof/net/Base.lean`
`wp_TCPAddr_String`), stated over `lib/NetLab.lean`'s `net.ownTCPConn` and proved from `Net/`'s
(`Net/Proof/net/Conn__{RemoteAddr,Close}.lean`, `GooseLang/Ext/Net/Proto.lean`'s `close_au`), as
`net.DialTimeout.labProof`.

**Port change.** `TCPConn.Close`'s result: the lab's post named its error (`net.connErr` of a code);
nothing in the swift proof uses it (every caller drops it), so the post here is `True`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetLab
public import Net.Proof.net.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [π : NetProtoGS]

/-- The lab's `net.isTCPAddr`: a non-`nil` `*TCPAddr`. -/
def net.isTCPAddr (ad : GoInterface) : Prop :=
  ∃ x : Loc, ad = interface.mkOk (go.GoType.PointerType net.TCPAddr.ty) #x

/-- lab `Harness/Spec/net/TCPConn__RemoteAddr.lean` `net.TCPConn.RemoteAddr.spec` (`cid : Nat` here). -/
abbrev net.TCPConn.RemoteAddr.spec : Prop :=
  ∀ (c : Loc) (cid : Nat) (side : Bool),
  {{ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"RemoteAddr")) (Val #()))
  {{ (ad : GoInterface), RET #ad; ⌜net.isTCPAddr ad⌝ }}

/-- lab `Harness/Spec/net/TCPConn__Close.lean` `net.TCPConn.Close.spec` (see the file header). -/
abbrev net.TCPConn.Close.spec : Prop :=
  ∀ (c : Loc) (cid : Nat) (side : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

theorem net.TCPConn.RemoteAddr.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] : net.TCPConn.RemoteAddr.spec (GF := GF) := by
  intro c cid side
  iintro %Φ Hc HΦ
  unfold net.ownTCPConn
  icases Hc with ⟨%a, %la, %ra, #Hat, -⟩
  ihave #Hat' := Hat
  iunfold net.connAt at Hat'
  icases Hat' with ⟨%nw, -, -, -, #Hra, -⟩
  iunfold net.netAddr at Hra
  icases Hra with ⟨%p, %v, %Hra, -⟩
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.connRemoteAddr (GF := GF)) c cid side a la ra $$ Hat
  iintro !> -
  iapply HΦ
  ipureintro; exact ⟨p, Hra⟩

theorem net.TCPConn.Close.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] : net.TCPConn.Close.spec (GF := GF) := by
  intro c cid side
  iintro %Φ ⟨-, Hc⟩ HΦ
  unfold net.ownTCPConn
  icases Hc with ⟨%a, %la, %ra, #Hat, #Hcs⟩
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.connClose (GF := GF)) c cid side a la ra (fun _ => iprop(True)) $$ [Hcs]
  · iframe Hat
    imod close_au cid side $$ Hcs with ⟨%st, %d, Hend, Hdir, Hk⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %res %st' %d' %Hc Hend Hdir
    imod Hk $$ %res %st' %d' %Hc Hend Hdir with -
    imodintro
    itrivial
  iintro !> %err -
  iapply HΦ
  itrivial

/-- lab `Harness/Proof/net/Base.lean` `net.wp_TCPAddr_String`: an arbitrary string (`Net/`'s model,
`models/net/model.go`'s `TCPAddr.String`: `extAnyString`). -/
theorem net.wp_TCPAddr_String (x : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (x @!! go.GoType.PointerType net.TCPAddr.ty @!! go!"String")) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start
  wp_auto
  wp_apply net.wp_extAnyString as %s
  iapply HΦ
  itrivial

end specs

end Perennial
