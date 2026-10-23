/-
**The stream writer's steps** (rafthttp stage 5b): what `streamWriter.run`'s proof uses of its
connection, independent of the stream's type (`Writer.lean`). Lean-first.

* `wp_stream_encode`: `enc.encode(m)` through the `encoder` interface, of the writer's type: a frame
  of the stream's codec from the encoder's state, or an error (whose `Error()` returns).
* `stream_perm`: what the encoder may write next on a live connection, a frame of a message whose
  facts are its next frame's (`frameDep`), is in the response's protocol (`streamResp`).
* `respWriter_writerAt`: a response writer at a `200` is a writer (`writerAt`) whose permission is
  the response's protocol.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageEncoder__encode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder__encode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- **`enc.encode(m)`** of the writer's encoder, of a message it may be given (it marshals, and on
the msgappv2 stream is an `MsgApp` of raft's shape from `lid` to `pid`), with the permission to
write any prefix of a frame of it from the encoder's state `s`: such a frame, or an error. -/
theorem wp_stream_encode
    (hMsg : rafthttp.messageEncoder.encode.spec (GF := GF) (hG := hG))
    (hV2 : rafthttp.msgAppV2Encoder.encode.spec (GF := GF) (hG := hG))
    (ty : StreamTy) (lid pid : w64) (fs : Loc) (enc : GoInterface) (wi : GoInterfaceOk)
    (s : (ty.codec lid pid).S) (Wr A : List w8 → IProp GF) (h : List w8) (ml : Loc) (st : MsgSt)
    (hok : MsgMarshals st ∧ (ty = .msgAppV2 → V2EncOk lid pid st)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        encOwn lid pid fs ty enc wi s ∗ writerAt wi Wr A ∗ Wr h ∗ msgOwn ml DFrac.discard st ∗
        □ (∀ (bs : List w8) (s' : (ty.codec lid pid).S) (k : Nat),
          ⌜(ty.codec lid pid).F s (wireOf st) bs s'⌝ -∗ A (h ++ bs.take k)) }}
      (App (App (Val (GoInstruction (MethodResolve rafthttp.encoder.ty go!"encode"))) (Val #enc))
        (Val #ml))
    {{ (err : GoInterface), RET #err; http.errStrOk err ∗
        ∃ (h' : List w8) (s' : (ty.codec lid pid).S), Wr h' ∗ encOwn lid pid fs ty enc wi s' ∗
          (⌜err = GoInterface.nil⌝ -∗
            ⌜∃ bs, (ty.codec lid pid).F s (wireOf st) bs s' ∧ h' = h ++ bs⌝) }} := by
  cases ty with
  | msgAppV2 =>
    simp only [encOwn]
    wp_start as ⟨Henc, #Hwr, HWr, #Hm, #HA⟩
    icases Henc with ⟨%e, %He, Henc⟩
    subst He
    wp_auto
    wp_apply hV2 e wi fs s lid pid ml st Wr A h (hok.2 rfl) $$ [$Henc $HWr]
      as %err ⟨#Herr, %h', %s', HWr, Henc, %Hok⟩
    · iframe #
      iintro !> %bs %cs' %k %Hf
      iapply HA $$ %bs %cs' %k %Hf
    iapply HΦ
    iframe #
    iexists h', s'
    iframe HWr
    isplitl [Henc]
    · iexists e
      iframe
      ipureintro; rfl
    iintro %Hnil
    ipureintro
    exact Hok Hnil
  | message =>
    simp only [encOwn]
    wp_start as ⟨Henc, #Hwr, HWr, #Hm, #HA⟩
    icases Henc with ⟨%e, %He, #Hew⟩
    subst He
    wp_auto
    wp_apply hMsg e wi ml st Wr A h hok.1 $$ [$HWr]
      as %err ⟨#Herr, %h', HWr, %Hok⟩
    · iframe #
      iintro !> %bs %Hw
      isplitl
      · rw [show u64Be (W64 bs.length) = (msgFrame bs).take 8 by
          simp [msgFrame, List.take_append_of_le_length, u64Be_length]]
        iapply HA $$ %(msgFrame bs) %() %8 %(MsgFrameOf.of_wire Hw.1 Hw.2)
      · rw [show h ++ msgFrame bs = h ++ (msgFrame bs).take (msgFrame bs).length by
          rw [List.take_length]]
        iapply HA $$ %(msgFrame bs) %() %(msgFrame bs).length %(MsgFrameOf.of_wire Hw.1 Hw.2)
    iapply HΦ
    isplitr
    · iexact Herr
    iexists h', ()
    iframe HWr
    isplitl []
    · iexists e
      iframe #
      ipureintro; rfl
    iintro %Hnil
    ipureintro
    obtain ⟨bs, Hw, Hl, rfl⟩ := Hok Hnil
    exact ⟨msgFrame bs, MsgFrameOf.of_wire Hw Hl, rfl⟩

end lemmas

end EtcdGrove
end Perennial
