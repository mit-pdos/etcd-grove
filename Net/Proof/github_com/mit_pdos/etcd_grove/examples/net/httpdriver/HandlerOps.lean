/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: a handler's calls, as triples

The response writer's methods (`respOps`'s `Header`, `WriteHeader`, `Write`) as Hoare triples on a
writer `interface.ok wi`, for `wp_apply` in the handlers' proofs (`echo`, `teapotHandler`); and the
pure facts of `echo`'s three header lines (`echoHdrs`: `hdrsOk`, their values by `hdrGetL`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto HdrLine RespSt)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section pure

/-- `echo`'s header lines, as its three `Set`s leave them. -/
def echoHdrs (m v : GoString) : List HdrLine :=
  [(go!"X-Method", m), (go!"X-Path", go!"/echo"), (go!"X-Echo", v)]

theorem echoHdrs_eq (m v : GoString) :
    net.http.hdrSetL (net.http.hdrSetL (net.http.hdrSetL [] go!"X-Method" m) go!"X-Path" go!"/echo")
      go!"X-Echo" v = echoHdrs m v := by
  have h1 : (go!"X-Method" : GoString) ≠ go!"X-Path" := by decide
  have h2 : (go!"X-Method" : GoString) ≠ go!"X-Echo" := by decide
  have h3 : (go!"X-Path" : GoString) ≠ go!"X-Echo" := by decide
  simp [net.http.hdrSetL, echoHdrs, h1, h2, h3]

/-- A word's bytes are header-value bytes, none a space. -/
theorem isWord_val (v : GoString) (hv : isWord v) :
    v.all net.http.valByte = true ∧ v.head? ≠ some (W8 32) ∧ v.getLast? ≠ some (W8 32) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro c hc
    have := hv.2 c hc
    simp only [net.http.valByte, decide_eq_true_eq]
    omega
  · intro h
    exact absurd (hv.2 _ (List.mem_of_mem_head? h)) (by decide)
  · intro h
    exact absurd (hv.2 _ (List.mem_of_getLast? h)) (by decide)

theorem echoHdrs_ok (m v : GoString) (hm : m = go!"POST" ∨ m = go!"PUT") (hv : isWord v) :
    net.http.hdrsOk (echoHdrs m v) := by
  obtain ⟨hvv, hvh, hvl⟩ := isWord_val v hv
  refine ⟨⟨by simp only [echoHdrs, List.map]; decide, ?_⟩, ?_, ?_⟩
  · intro kv hkv
    simp only [echoHdrs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hkv
    rcases hkv with rfl | rfl | rfl
    · rcases hm with rfl | rfl <;> decide
    · decide
    · exact ⟨(by decide : (go!"X-Echo" : GoString) ≠ []),
        (by decide : (go!"X-Echo" : GoString).all net.http.fieldByte = true),
        (by decide : net.http.canonQuick go!"X-Echo" = true), hvv, hvh, hvl⟩
  · intro kv hkv
    simp only [echoHdrs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hkv
    rcases hkv with rfl | rfl | rfl
    · exact (by decide : (go!"X-Method" : GoString) ∉ net.http.respKeysOut)
    · exact (by decide : (go!"X-Path" : GoString) ∉ net.http.respKeysOut)
    · exact (by decide : (go!"X-Echo" : GoString) ∉ net.http.respKeysOut)
  · have := hv.1
    rcases hm with rfl | rfl <;>
      simp [echoHdrs, net.http.hdrLineWire] <;> omega

theorem echoHdrs_get (m v : GoString) :
    net.http.hdrGetL (echoHdrs m v) go!"X-Method" = m ∧
    net.http.hdrGetL (echoHdrs m v) go!"X-Path" = go!"/echo" ∧
    net.http.hdrGetL (echoHdrs m v) go!"X-Echo" = v := by
  have h1 : (go!"X-Method" : GoString) ≠ go!"X-Path" := by decide
  have h2 : (go!"X-Method" : GoString) ≠ go!"X-Echo" := by decide
  have h3 : (go!"X-Path" : GoString) ≠ go!"X-Echo" := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [net.http.hdrGetL, echoHdrs, h1, h2, h3]

/-- The `X-Driver` value of an `/echo` request's lines. -/
theorem echoReq_xdriver (v n : GoString) :
    net.http.hdrGetL [(go!"X-Driver", v), (go!"Content-Length", n)] go!"X-Driver" = v := by
  simp [net.http.hdrGetL]

theorem hdrsOk_nil : net.http.hdrsOk [] := by
  unfold net.http.hdrsOk; decide

end pure

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `w.Header()` before the commit: the header map, lent. -/
theorem wp_resp_Header (wi : GoInterfaceOk) (R : HReq) (τ : GName) (P : HProto GF)
    (I : RespSt → IProp GF) (hs : List HdrLine) (bs : List w8) (ok : Bool) :
    {{ net.http.respOps (interface.ok wi) R τ P I ∗ I (none, hs, bs, ok) }}
      (App (Val #(methods wi.ty go!"Header" wi.v)) (Val #()))
    {{ (hm : Loc), RET #hm; net.http.hdrOwn hm hs ∗
        (∀ hs', net.http.hdrOwn hm hs' -∗ I (none, hs', bs, ok)) }} := by
  iintro %Φ ⟨#Hops, HI⟩ HΦ
  iunfold net.http.respOps at Hops
  icases Hops with ⟨%i, %Hi, #Hh, -, -⟩
  cases Hi
  iapply Hh $$ %hs %bs %ok %Φ HI
  inext
  iintro %hm Hm Hback
  iapply HΦ
  iframe

/-- `w.WriteHeader(st)` before the commit. -/
theorem wp_resp_WriteHeader (wi : GoInterfaceOk) (R : HReq) (τ : GName) (P : HProto GF)
    (I : RespSt → IProp GF) (hs : List HdrLine) (bs : List w8) (ok : Bool) (st : w64)
    (h : 200 ≤ uint.nat st ∧ uint.nat st ≤ 999 ∧ net.http.bodyAllowed st = true ∧
      net.http.hdrsOk hs) :
    {{ net.http.respOps (interface.ok wi) R τ P I ∗ I (none, hs, bs, ok) ∗ □ P.resp R τ st hs [] }}
      (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #st))
    {{ RET #(); I (some st, hs, bs, ok) }} := by
  iintro %Φ ⟨#Hops, HI, #Hr⟩ HΦ
  iunfold net.http.respOps at Hops
  icases Hops with ⟨%i, %Hi, -, #Hw, -⟩
  cases Hi
  iapply Hw $$ %hs %bs %ok %st %Φ %h HI Hr
  inext
  iexact HΦ

/-- `w.Write(b)`: all written, or an error with a prefix written and the writer failed. -/
theorem wp_resp_Write (wi : GoInterfaceOk) (R : HReq) (τ : GName) (P : HProto GF)
    (I : RespSt → IProp GF) (c : Option w64) (hs : List HdrLine) (bs : List w8) (ok : Bool)
    (b : GoSlice) (ys : List w8) (dq : DFrac) (h : c = none → net.http.hdrsOk hs) :
    {{ net.http.respOps (interface.ok wi) R τ P I ∗ I (c, hs, bs, ok) ∗ b ↦*{dq} ys ∗
        □ P.resp R τ (c.getD (W64 200)) hs (bs ++ ys) }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #b))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); b ↦*{dq} ys ∗
        ((⌜err = interface.nil⌝ ∗ I (some (c.getD (W64 200)), hs, bs ++ ys, ok)) ∨
         (∃ bs', I (some (c.getD (W64 200)), hs, bs', false))) }} := by
  iintro %Φ ⟨#Hops, HI, Hb, #Hr⟩ HΦ
  iunfold net.http.respOps at Hops
  icases Hops with ⟨%i, %Hi, -, -, #Hw⟩
  cases Hi
  iapply Hw $$ %c %hs %bs %ok %b %ys %dq %Φ %h HI Hb Hr
  inext
  iintro %n %err Hb %Hn Hres
  iapply HΦ
  iframe Hb
  icases Hres with (⟨%He, HI⟩ | ⟨%He, HI⟩)
  · ileft; iframe HI; ipureintro; exact He.1
  · iright; iexists _; iexact HI

end ops

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
