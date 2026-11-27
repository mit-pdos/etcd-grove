/-
`RequestWithin(addr, kind, timeout, total, payload)` (`examples/raft/kvraft/client.go`):
`RequestVia(DialTCP, ...)`. As `RequestVia`'s spec, with the dialer `DialTCP` (`net.DialTimeout` at
`"tcp"`): for a valid address `addr`, the caller's update of the dial (`DialTCP`'s) takes the new
connection's resources `connRes cn false T W Rd` (`Client.lean`: nothing written or read, the caller's
write, read and close accessors for the end `false` of `cn`) or, the dial abandoned, gives `Fl`.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev RequestWithin.spec : Prop :=
  ∀ (addr : GoString) (kind : w8) (tmo total : _root_.Perennial.time.Duration)
    (payload : GoSlice) (pl : List w8) (dqp : DFrac) (W Rd : Nat → Bool → List w8 → IProp GF)
    (Fl : IProp GF) (eof ed et : GoInterface),
  (pl.length : Int) + 17 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      payload ↦*{dqp} pl ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr net.errTimeout ↦□ et ∗
      ⌜addrOk addr = true⌝ ∗
      (Fl ∧
        |={⊤,∅}=> ∃ S, netPend (extGlobalGS netExt (G := hG.goose_globalGS)) addr S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) addr (S ∪ {[cn]}) -∗
            netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn addr -∗
            netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn true -∗
            ((netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ={∅,⊤}=∗
                connRes cn false (helloClientB :: putB (reqBytes kind tmo pl)) W Rd) ∧
             (netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false
                { NetEnd.fresh with closed := true } -∗
              netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ⟨[], .fin⟩ ={∅,⊤}=∗
                Fl))) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RequestWithin))
      (Val #addr)) (Val #kind)) (Val #tmo)) (Val #total)) (Val #payload))
  {{ (b : GoSlice) (ok : Bool), RET (PairV #b #ok); payload ↦*{dqp} pl ∗
      ((⌜ok = true⌝ ∗ ∃ (b' : List w8) (cn : Nat) (s : Bool), b ↦* b' ∗
          W cn s (helloClientB :: putB (reqBytes kind tmo pl)) ∗ Rd cn s (putB (W8 1 :: b'))) ∨
        (⌜ok = false⌝ ∗ (Fl ∨ ∃ (cn : Nat) (s : Bool) (w got : List w8), W cn s w ∗ Rd cn s got))) }}

end spec

end kvraft
end EtcdGrove
end Perennial
