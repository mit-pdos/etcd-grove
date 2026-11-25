/- Lean-first (no Rocq counterpart).

# `check`'s proof

By the request's kind (`qOf`: `d.kind`) and the status, from `chkPre`: the server's `400`, or the
handler's complete answer (`drvRespEnd`), whose lines `hs` the client reads through `hdrView` and
`dropConn` (`hdr_client`: the keys it reads are outside `srvKeys` and not `Connection`). So every
check holds and no `panic` is reached; each `reached` call returns (`drvFacts`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.check
public import Net.Spec.net.http.Header__Get
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HdrLine)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-! ## What `check` reads of an answer (pure) -/

/-- A key outside `srvKeys` (and not `Connection`) reads, in the client's map, the handler's line. -/
theorem hdr_client (hs hc : List HdrLine) (k : GoString) (hv : net.http.hdrView hs hc)
    (hk : k ∉ net.http.srvKeys) (hk' : k ≠ go!"Connection") :
    net.http.hdrGetL (net.http.dropConn hc) k = net.http.hdrGetL hs k := by
  rw [hdrGetL_dropConn hc k hk']
  exact hv k hk

/-- An `/echo` answer `200`: its headers and body echo the request. -/
theorem echo_facts (m v b : GoString) (st : w64) (hc : List HdrLine) (body : List w8)
    (hpre : chkPre (.echo m v b) st hc body) (h200 : st = W64 200) :
    net.http.hdrGetL (net.http.dropConn hc) go!"X-Method" = m ∧
    net.http.hdrGetL (net.http.dropConn hc) go!"X-Path" = go!"/echo" ∧
    net.http.hdrGetL (net.http.dropConn hc) go!"X-Echo" = v ∧ body = b := by
  rcases hpre with h400 | ⟨-, hs, hv, hend⟩
  · rw [h200] at h400
    exact absurd h400 (by decide)
  · obtain ⟨h1, h2, h3, h4⟩ := hend.1 rfl h200
    have hx : net.http.hdrGetL [(go!"X-Driver", v), (go!"Content-Length", fmt.decimalNat b.length)]
        go!"X-Driver" = v := by
      simp [net.http.hdrGetL]
    refine ⟨?_, ?_, ?_, h4⟩
    · rw [hdr_client hs hc _ hv (by decide) (by decide)]; exact h1
    · rw [hdr_client hs hc _ hv (by decide) (by decide)]; exact h2
    · rw [hdr_client hs hc _ hv (by decide) (by decide)]; exact h3.trans hx

/-- A `/status` answer: `418` with the handler's body, or the server's `400`. -/
theorem status_facts (st : w64) (hc : List HdrLine) (body : List w8)
    (hpre : chkPre .status st hc body) :
    (st = W64 418 → body = go!"short and stout") ∧ (st ≠ W64 418 → st = W64 400) := by
  rcases hpre with h400 | ⟨-, hs, -, hend⟩
  · subst h400
    exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩
  · have h := hend.2.1 rfl
    exact ⟨fun _ => h.2, fun hne => absurd h.1 hne⟩

/-- `/nope/<w>` is neither of the mux's paths. -/
theorem nope_ne (w : GoString) : go!"/nope/" ++ w ≠ go!"/echo" ∧ go!"/nope/" ++ w ≠ go!"/status" := by
  constructor <;> intro h <;> have h1 := congrArg (fun l : List w8 => l[1]?) h <;>
    simp (config := { decide := true }) at h1

/-- A `/nope/<w>` answer: `404`, or the server's `400`. -/
theorem nope_facts (w : GoString) (st : w64) (hc : List HdrLine) (body : List w8)
    (hpre : chkPre (.nope w) st hc body) : st ≠ W64 404 → st = W64 400 := by
  intro hne
  rcases hpre with h400 | ⟨-, hs, -, hend⟩
  · exact h400
  · exact absurd (hend.2.2 (nope_ne w).1 (nope_ne w).2) hne

/-- The junk request's answer is the server's `400`. -/
theorem junk_facts (st : w64) (hc : List HdrLine) (body : List w8)
    (hpre : chkPre .junk st hc body) : st = W64 400 := by
  rcases hpre with h400 | ⟨hj, -⟩
  · exact h400
  · exact absurd rfl hj

/-! ## The proof -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : net.http.HttpProtoGS]

theorem check.wp_proof (wp_Get : net.http.Header.Get.spec (GF := GF) (hG := hG)) :
    check.spec (GF := GF) (hG := hG) := by
  intro q d resp rv hc body hq hpre
  rcases q with ⟨qraw, qkind, qmeth, qval, qbody⟩
  wp_start as ⟨#Hf, Hresp, Hh⟩
  iunfold drvFacts at Hf
  icases Hf with ⟨%f, #Hrg, #Hrf⟩
  cases d with
  | echo m v b =>
    simp only [qOf, DReq.kind] at hq
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hq
    wp_auto
    wp_if_destruct
    · -- `200`: the handler's echo
      obtain ⟨h1, h2, h3, rfl⟩ := echo_facts _ _ _ _ hc body hpre Hif
      wp_method_call; wp_call
      wp_apply wp_Get rv.Header' (net.http.dropConn hc) go!"X-Method" (by decide) $$ Hh as Hh
      rw [h1]
      wp_auto
      wp_method_call; wp_call
      wp_apply wp_Get rv.Header' (net.http.dropConn hc) go!"X-Path" (by decide) $$ Hh as Hh
      rw [h2]
      wp_auto
      wp_method_call; wp_call
      wp_apply wp_Get rv.Header' (net.http.dropConn hc) go!"X-Echo" (by decide) $$ Hh as Hh
      rw [h3]
      wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hrf $$ %go!"echo")
      iintro %r %Hr
      subst Hr
      wp_auto
      iapply HΦ
      itrivial
    · -- another status: nothing to check
      iapply HΦ
      itrivial
  | status =>
    simp only [qOf, DReq.kind] at hq
    obtain ⟨-, rfl, -⟩ := hq
    have hs := status_facts _ hc body hpre
    wp_auto
    wp_if_destruct
    · -- `418`: the handler's body
      obtain rfl := hs.1 Hif
      wp_auto
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hrf $$ %go!"status")
      iintro %r %Hr
      subst Hr
      wp_auto
      iapply HΦ
      itrivial
    · -- otherwise the server's `400`
      rw [hs.2 Hif]
      wp_auto
      iapply HΦ
      itrivial
  | nope w =>
    simp only [qOf, DReq.kind] at hq
    obtain ⟨-, rfl, -⟩ := hq
    wp_auto
    wp_if_destruct
    · -- `404`
      try wp_bind (App (Val #f) (Val _))
      iapply wp_wand $$ (Hrf $$ %go!"mux")
      iintro %r %Hr
      subst Hr
      wp_auto
      iapply HΦ
      itrivial
    · -- otherwise the server's `400`
      rw [nope_facts w _ hc body hpre Hif]
      wp_auto
      iapply HΦ
      itrivial
  | junk =>
    simp only [qOf, DReq.kind] at hq
    obtain ⟨-, rfl, -⟩ := hq
    wp_auto
    rw [junk_facts _ hc body hpre]
    wp_auto
    try wp_bind (App (Val #f) (Val _))
    iapply wp_wand $$ (Hrf $$ %go!"bad-request")
    iintro %r %Hr
    subst Hr
    wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
