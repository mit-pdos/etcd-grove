/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/ipv4port.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension. The configured addresses are the port's (`VsrWire.addrs`,
kit.go's `Addrs()`: `127.0.0.1`, a port per machine), not the lab's (`10.77.0.x`, one port), so
`Less` on them compares ports and `ByLess` sorts by the port order (`ipv4port.portLt`), not by the
empty order; `ipCfg` keeps the IP bytes exact (`127.0.0.1`) instead of the lab's last byte `x`.
-/
/-
Cross-package specs of `pkg/ipv4port`: an `IPv4Port` value's string (`ipOwn`), the parsed
configured addresses (`ipCfg`), `FromHostPort` on a configured address, `FromAddrString`,
`String`, and `ByLess` as a `sort.Interface` (`sort.Sort` in `client.New`, `replica.New`).

On the configured addresses (`VsrWire.addrs`: one IP, `127.0.0.1`, distinct ports) `Less`
compares the ports, so `ByLess` sorts by the port order (`portLt`): `sort.Sort` gives back a
permutation, which is all its callers need (the members' order is not needed, notes/hubs.md).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.ipv4port.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Addrs
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The order `ByLess` sorts the configured addresses by: their ports' (`Less` on equal IPs). -/
def ipv4port.portLt [GooseExts] (a b : ipv4port.IPv4Port) : Prop := sint.Z a.Second' < sint.Z b.Second'

/-- The `IPv4Port` value `v`'s `String()` is `s`. -/
def ipv4port.ipOwn [GooseExts] (v : ipv4port.IPv4Port) (s : GoString) : Prop := v.str' = s

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

/-- The body of `ipCfg` (the package's: callers use `ipCfg` and its laws). -/
def ipv4port.ipCfgDef (v : ipv4port.IPv4Port) (a : GoString) : IProp GF :=
  iprop(⌜a ∈ VsrWire.addrs ∧ v.str' = a⌝ ∗
    v.First' ↦*□ ([W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0,
      W8 255, W8 255, W8 127, W8 0, W8 0, W8 1] : List w8))

/-- `v` is the parse of the configured address `a` (`FromHostPort`'s result): its string is `a`,
and its IP bytes are readable (what `Less` reads). Persistent.
-- sealed: the package's choice -/
@[irreducible] def ipv4port.ipCfg (v : ipv4port.IPv4Port) (a : GoString) : IProp GF :=
  ipv4port.ipCfgDef v a

instance ipv4port.ipCfg_persistent (v : ipv4port.IPv4Port) (a : GoString) :
    Persistent (ipv4port.ipCfg (GF := GF) (hG := hG) v a) := by
  rw [show ipv4port.ipCfg v a = ipv4port.ipCfgDef v a by with_unfolding_all rfl]
  unfold ipv4port.ipCfgDef; infer_instance
instance ipv4port.ipCfg_timeless (v : ipv4port.IPv4Port) (a : GoString) :
    Timeless (ipv4port.ipCfg (GF := GF) (hG := hG) v a) := by
  rw [show ipv4port.ipCfg v a = ipv4port.ipCfgDef v a by with_unfolding_all rfl]
  unfold ipv4port.ipCfgDef; infer_instance

/-- A parsed configured address has its string, and is configured. -/
theorem ipv4port.ipCfg_str (v : ipv4port.IPv4Port) (a : GoString) :
    ipv4port.ipCfg (GF := GF) (hG := hG) v a ⊢ ⌜ipv4port.ipOwn v a ∧ a ∈ VsrWire.addrs⌝ := by
  rw [show ipv4port.ipCfg v a = ipv4port.ipCfgDef v a by with_unfolding_all rfl]
  unfold ipv4port.ipCfgDef
  iintro ⟨%h, -⟩
  ipureintro
  exact ⟨h.2, h.1⟩

/-- A slice of parsed configured addresses (the elements of a `ByLess` being sorted). -/
def ipv4port.cfgList (sl : GoSlice) (l : List ipv4port.IPv4Port) : IProp GF :=
  iprop(sl ↦* l ∗ [∗list] v ∈ l, ∃ a : GoString, ipv4port.ipCfg v a)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

set_option goose.wp.extras true

/-- `p.FromHostPort(a)` on a configured address `a`: no error, `*p` is `a`'s parse. -/
abbrev ipv4port.IPv4Port.FromHostPort.spec : Prop :=
  ∀ (p : Loc) (v0 : ipv4port.IPv4Port) (a : GoString), a ∈ VsrWire.addrs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ∗
      p ↦ v0 }}
    (App (Val (p @!! go.GoType.PointerType ipv4port.IPv4Port.ty @!! go!"FromHostPort"))
      (Val #a))
  {{ RET #(interface.nil : GoInterface); ∃ v : ipv4port.IPv4Port, p ↦ v ∗ ipv4port.ipCfg v a }}

/-- `FromAddrString(s)`: a value whose string is `s`. -/
abbrev ipv4port.FromAddrString.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port }}
    (App (Val (@! ipv4port.FromAddrString)) (Val #s))
  {{ (v : ipv4port.IPv4Port), RET #v; ⌜ipv4port.ipOwn v s⌝ }}

/-- `v.String()`: its string. -/
abbrev ipv4port.IPv4Port.String.spec : Prop :=
  ∀ (v : ipv4port.IPv4Port),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port }}
    (App (Val (v @!! ipv4port.IPv4Port.ty @!! go!"String")) (Val #()))
  {{ RET #v.str'; True }}

/-- `p.String()` through a pointer (an addressable variable): its value's string. -/
abbrev ipv4port.IPv4Port.String_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (v : ipv4port.IPv4Port),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ∗
      p ↦{dq} v }}
    (App (Val (p @!! go.GoType.PointerType ipv4port.IPv4Port.ty @!! go!"String")) (Val #()))
  {{ RET #v.str'; p ↦{dq} v }}

/-- `ByLess(sl)` as a `sort.Interface` sorts a slice of parsed configured addresses by the port
order (`Less` compares their ports): `sort.Sort` leaves a permutation. -/
abbrev ipv4port.ByLess.sorter.spec : Prop :=
  ∀ (sl : GoSlice),
  isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ⊢
    sort.isSorter (⟨ipv4port.ByLess.ty, #sl⟩ : GoInterfaceOk) (ipv4port.cfgList sl)
      ipv4port.portLt

/-- The port order is a strict weak order (`sort.Sort`'s premise). -/
theorem ipv4port.ByLess.swo [GooseExts] :
    slices.StrictWeakOrder ipv4port.portLt where
  strict_weak_order_irrefl _ := by unfold ipv4port.portLt; omega
  strict_weak_order_trans _ _ _ h1 h2 := by unfold ipv4port.portLt at *; omega
  strict_weak_order_equiv :=
    ⟨fun _ => by unfold ipv4port.portLt; omega, fun h => by unfold ipv4port.portLt at *; omega,
      fun h1 h2 => by unfold ipv4port.portLt at *; omega⟩

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
