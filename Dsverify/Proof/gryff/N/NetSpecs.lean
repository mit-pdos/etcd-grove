/-
# Unit N: `Net/`'s `net` specs, as one hypothesis

The specs of `net` the replica's connection code calls (`Net/Spec/net/*`), bundled as a `Prop`
class (the import tiers: a defs module sees its callees through their specs, as `wire.BufioSpecs`).
Discharged at linking by `Net/`'s `wp_proof`s (`net.Conn.Read.wp_proof`, ...); no instance
anywhere. Not a library gap: every field is proved in `Net/`.
-/
module

public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__RemoteAddr
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Listen
public import Net.Spec.net.Dial
public import Net.Spec.net.DialTimeout

@[expose] public section

noncomputable section

namespace Perennial.gryff.netN

open Iris Iris.BI Net

/-- See the file header. -/
class NetSpecs [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] [net.Assumptions]
    : Prop where
  read : Perennial.net.Conn.Read.spec (GF := GF) (hG := hG)
  write : Perennial.net.Conn.Write.spec (GF := GF) (hG := hG)
  close : Perennial.net.Conn.Close.spec (GF := GF) (hG := hG)
  remoteAddr : Perennial.net.Conn.RemoteAddr.spec (GF := GF) (hG := hG)
  accept : Perennial.net.Listener.Accept.spec (GF := GF) (hG := hG)
  listen : Perennial.net.Listen.spec (GF := GF) (hG := hG)
  dial : Perennial.net.Dial.spec (GF := GF) (hG := hG)
  dialTimeout : Perennial.net.DialTimeout.spec (GF := GF) (hG := hG)

end Perennial.gryff.netN
