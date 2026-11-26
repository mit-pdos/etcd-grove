/- Lean-first (no Rocq counterpart).

# `randomRequest`'s proof

By `below(4)`'s value: an `/echo` request (method `POST` or `PUT`, two words; its bytes are
`DReq.wire`, `strconv.Itoa(len(b))` being `fmt.decimalNat |b|` by `fmtInt_small`), `GET /status`,
`GET /nope/<word>`, or the junk line.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.randomRequest
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.randomWord
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.below
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas
public import Perennial.Spec.strconv.Itoa
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-- The bytes `randomRequest` builds for `/echo` are the request's wire. -/
theorem echo_raw_wire (m v b : GoString) (hb : b.length ≤ 32) :
    m ++ go!" /echo HTTP/1.1\r\nHost: driver\r\nX-Driver: " ++ v ++ go!"\r\nContent-Length: " ++
      internal.strconv.fmtInt (W64 b.length) (W64 10) ++ go!"\r\n\r\n" ++ b =
    (DReq.echo m v b).wire := by
  rw [fmtInt_small _ hb]
  simp [DReq.wire, DReq.hreq, DReq.body, net.http.reqWire, net.http.hdrWire, net.http.hdrLineWire,
    driverHost]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

theorem randomRequest.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_randomWord : randomWord.spec (GF := GF) (hG := hG))
    (wp_Itoa : strconv.Itoa.spec (GF := GF) (hG := hG)) :
    randomRequest.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  wp_apply wp_below (W64 4) as %sw -
  wp_if_destruct
  · -- `/echo`
    wp_apply wp_below (W64 2) as %c -
    wp_if_destruct
    all_goals
      wp_apply wp_randomWord as %v %Hv
      wp_apply wp_randomWord as %b %Hb
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply wp_Itoa
      iapply HΦ
      ipureintro
      first
        | (refine ⟨.echo go!"PUT" v b, ?_, ?_⟩
           · exact ⟨by decide, Hv, Hb⟩
           · exact ⟨echo_raw_wire _ v b Hb.1, rfl, rfl, rfl, rfl⟩)
        | (refine ⟨.echo go!"POST" v b, ?_, ?_⟩
           · exact ⟨by decide, Hv, Hb⟩
           · exact ⟨echo_raw_wire _ v b Hb.1, rfl, rfl, rfl, rfl⟩)
  · wp_if_destruct
    · -- `GET /status`
      iapply HΦ
      ipureintro
      refine ⟨.status, trivial, ?_⟩
      simp [qOf, DReq.wire, DReq.kind, DReq.hreq, DReq.body, net.http.reqWire, net.http.hdrWire,
        net.http.hdrLineWire, driverHost]
    · wp_if_destruct
      · -- `GET /nope/<w>`
        wp_apply wp_randomWord as %w %Hw
        iapply HΦ
        ipureintro
        refine ⟨.nope w, Hw, ?_⟩
        simp [qOf, DReq.wire, DReq.kind, DReq.hreq, DReq.body, net.http.reqWire,
          net.http.hdrWire, net.http.hdrLineWire, driverHost]
      · -- junk
        iapply HΦ
        ipureintro
        refine ⟨.junk, trivial, ?_⟩
        simp [qOf, DReq.wire, DReq.kind, junkWire]

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
