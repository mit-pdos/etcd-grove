/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchSend.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`sendConf(a, b)` (`kit.go`), for the orchestrator: on a fresh connection to `a` it writes the
message `bs` (meeting `a`'s dialer protocol `P`), reads one byte back and closes the connection;
`true` only if the byte is `confAck`, and then the acceptor's protocol `Q` held of a reply that
starts with `confAck` (for a predicted node's configuration port, `conf.ackQP`: its prediction is
registered).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

-- PORT: lab imports dropped: Harness.Proof.net.Dial, Harness.Proof.net.TCPConn__Write, Harness.Proof.net.TCPConn__Read, Harness.Proof.net.TCPConn__Close, Harness.Proof.bufio.ReadFull, Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]

/-- `sendConf(a, b)`: the message `bs` meets `a`'s dialers' protocol; an acknowledgment carries
`a`'s acceptors' protocol of a reply starting with `confAck`. -/
abbrev sendConf.spec : Prop :=
  ∀ (a : GoString) (b : GoSlice) (bs : List w8) (P Q : Proto netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      addrProto a P Q ∗ □ (∀ cid, P cid bs) ∗ b ↦* bs }}
    (App (App (Val (@! examples.swiftnet.sendConf)) (Val #a)) (Val #b))
  {{ (ok : Bool), RET #ok;
      if ok then ∃ (cid : w64) (ext : List w8), ⌜[confAck] <+: ext⌝ ∗ □ Q cid ext else True }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

set_option goose.wp.extras true

theorem sendConf.wp_proof : sendConf.spec := by
  intro a b bs P Q
  wp_start as ⟨#Hpr, #HP, Hb⟩
  wp_auto
  wp_apply net.Dial.wp_proof a P Q $$ [Hpr] as %cv %err Hres
  · iexact Hpr
  unfold net.newConnResult
  icases Hres with (⟨%cn, %cid, %Hcv, #Hcn, ⟨Hsend, Hrecv⟩, Hf⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  rotate_left
  · wp_auto
    (iapply HΦ $$ %false; simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial)
  wp_auto
  ihave #Hnet : isPkgInit (PROP := IProp netDistGF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp netDistGF) pkg_id.io $$ []
  · iPkgInit
  wp_apply net.TCPConn.Write.wp_proof cn cid false b bs (DFrac.own 1) P []
    $$ [$Hnet $Hcn $Hsend $Hb] as %nw %errw ⟨%k, %code, %Hk, Hb, Hsend, -⟩
  · iintro !>
    rw [List.nil_append]
    iapply HP
  cases errw with
  | ok ei =>
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof cn cid false $$ [$Hnet $Hcn] as %err2 -
    (iapply HΦ $$ %false; simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial)
  | nil =>
    wp_auto
    have hsl : slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) a_ptr) (W64 1 - W64 0) (W64 1 - W64 0) =
        slice.mk a_ptr (W64 1) (W64 1) := by
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]; rfl
    rw [hsl]
    ihave Ha := slice_array (GF := netDistGF) a_ptr _ _ (by decide) $$ a
    ihave #Hrd := bufio.readsOk_conn (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #cn)
      cid false Q $$ [$Hnet]
    · unfold net.rpc.connIface; iexists cn; iframe Hcn; ipureintro; rfl
    wp_apply bufio.wp_ReadFull _ (recvTok cid false Q) [] _ _ $$ [$Hio $Hrd $Hrecv $Ha]
      as %n %err ⟨%data, %Hd, Ha, Hrecv, #He⟩
    cases err with
    | ok i =>
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof cn cid false $$ [$Hnet $Hcn] as %err2 -
      (iapply HΦ $$ %false; simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial)
    | nil =>
      wp_auto
      obtain ⟨-, -, Hdl⟩ := Hd
      have hd1 : data.length = 1 := Hdl.1 rfl
      obtain ⟨x, hx⟩ : ∃ x, (data ++ List.drop data.length (List.replicate 1 (zero_val w8)))[
          (sint.Z (W64 0)).toNat]? = some x := by
        match data, hd1 with
        | [x], _ => exact ⟨x, rfl⟩
      rw [show arrayIndexRef w8 (sint.Z (W64 0)) a_ptr =
        sliceIndexRef w8 (sint.Z (W64 0)) (slice.mk a_ptr (W64 1) (W64 1)) from rfl]
      wp_apply wp_load_slice_index (slice.mk a_ptr (W64 1) (W64 1)) (sint.Z (W64 0)) _ _ x
        (by decide) $$ [Ha] as Ha
      · iframe Ha; ipureintro; exact hx
      ihave ⟨Hrecv, #Hpp⟩ := recvTok_proto cid false Q _ $$ Hrecv
      wp_if_destruct
      · wp_apply net.TCPConn.Close.wp_proof cn cid false $$ [$Hnet $Hcn] as %err2 -
        iapply HΦ $$ %true
        simp only [↓reduceIte]
        unfold protoPrefix
        icases Hpp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
        · exfalso
          simp only [List.nil_append] at Hnil
          subst Hnil; simp at hd1
        · iexists cid, ext
          iframe HQ
          ipureintro
          match data, hd1, hx with
          | [y], _, hx =>
            simp only [List.nil_append] at Hext
            have : y = confAck := by
              have h : y = W8 107 := by simpa using hx
              rw [h]; rfl
            subst this; exact Hext
      · wp_apply net.TCPConn.Close.wp_proof cn cid false $$ [$Hnet $Hcn] as %err2 -
        (iapply HΦ $$ %false; simp only [Bool.false_eq_true, ↓reduceIte]; ipureintro; trivial)

end proof

end orch

end Perennial.github_com.imdea_software.swiftpaxos
