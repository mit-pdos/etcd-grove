/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: pure facts of the wire

* **The answers' wire is prefix-free** (`respsWire_prefix_decode`): if the wire of answers `A`, each
  delimited by its `Content-Length` (`respOk`, not `close`), followed by more bytes is a prefix of the wire
  of answers `Rs` (each such an answer or net/http's `400`), then `Rs` starts with `A` and has one more.
  By a decoder of an answer's wire (status line, header lines up to the empty line, the body by its
  `Content-Length`) that reads `respWire ρ ++ t` as `ρ` and `t`, and that a longer stream does not change.
* The driver's requests are ones the server reads as written (`DReq.reqOk`), its junk is junk
  (`junkWire_ok`), their paths and the mux's two patterns (`DReq.route`: `/echo` and `/status` are routed
  to their handlers, every other path is not redirected and under neither pattern).
* Header lines: `hdrGetL` through `dropConn`, `Content-Length`'s value (`fmtInt_small`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial

open net.http (HReq Resp RespSlot ReqSlot HdrLine)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-- See the file header. -/
theorem respsWire_prefix_decode (A : List Resp) (Rs : List RespSlot) (y : List w8)
    (hA : ∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false)
    (hRs : ∀ x ∈ Rs, (∃ ρ, x = .ans ρ ∧ net.http.respOk ρ ∧ ρ.close = false) ∨ x = .bad)
    (hp : net.http.respsWire (A.map RespSlot.ans) ++ y <+: net.http.respsWire Rs) (hy : y ≠ []) :
    ∃ x rest, Rs = A.map RespSlot.ans ++ x :: rest := by
  sorry

/-- The driver's requests are read as written. -/
theorem DReq.reqOk (d : DReq) (hd : d.ok) (hj : d ≠ .junk) : net.http.reqOk d.hreq d.body := by
  sorry

/-- The junk request is rejected at its request line. -/
theorem junkWire_ok : net.http.junkOk junkWire := by
  sorry

/-- The mux's patterns, as `HandleFunc` registers them (`/echo`, then `/status`). -/
def drvPats : List GoString := [go!"/status", go!"/echo"]

theorem drvPats_ok : ∀ p ∈ drvPats, net.http.litPattern p ∧ net.http.pathClean p := by
  sorry

/-- The driver's paths and the mux: `/echo` and `/status` are routed to their handlers (the path is
the pattern), and no other path is redirected or under a pattern. -/
theorem DReq.route (d : DReq) (hd : d.ok) (hj : d ≠ .junk) :
    ¬ net.http.muxRedirect drvPats d.hreq.path ∧
    (d.hreq.path ≠ go!"/echo" → d.hreq.path ≠ go!"/status" →
      ∀ p ∈ drvPats, ¬ net.http.pathUnder p d.hreq.path) := by
  sorry

/-- A path under `/echo` (or `/status`) is it. -/
theorem pathUnder_lit (p q : GoString) (hp : p.getLast? ≠ some (W8 47))
    (h : net.http.pathUnder p q) : q = p := by
  sorry

/-- `dropConn` keeps every other key's value. -/
theorem hdrGetL_dropConn (hc : List HdrLine) (k : GoString) (hk : k ≠ go!"Connection") :
    net.http.hdrGetL (net.http.dropConn hc) k = net.http.hdrGetL hc k := by
  sorry

/-- `strconv.Itoa` of a body's length (at most `32`) is its decimal. -/
theorem fmtInt_small (n : Nat) (hn : n ≤ 32) :
    internal.strconv.fmtInt (W64 n) (W64 10) = fmt.decimalNat n := by
  sorry

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
