/-
The vr kit's addresses (notes/dsv-vr.md): the go-vsr addresses of its machines, one list,
`VsrWire.addrs`, what the kit's `Addrs()` returns (`examples/vsrnet/KitLib.lean`, `wp_Addrs`; the
wire's protocols (`Wire/Basic.lean`) and `ipv4port`'s configured addresses (`Spec/ipv4port.lean`)
are over it); the configuration addresses (`vsrnet.cfgAddrs`, `CfgAddrs()`) and the client
machines' (`vsrnet.clientAddrs`, `ClientAddrs()`).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace VsrWire

open Perennial

/-- The go-vsr addresses of the machines (the kit's `Addrs()`, `kit.go`: machine `i` at
`127.0.0.1:(7500 + i)`; 0 the orchestrator (unused), client `c` on `1 + c`, then the servers); the lab's
`github_com.tangledbytes.go_vsr.addrs` (`VsrNetSpec.lean`, its `Addrs()`). -/
def addrs : List GoString :=
  [go!"127.0.0.1:7500", go!"127.0.0.1:7501", go!"127.0.0.1:7502",
   go!"127.0.0.1:7503", go!"127.0.0.1:7504", go!"127.0.0.1:7505",
   go!"127.0.0.1:7506", go!"127.0.0.1:7507", go!"127.0.0.1:7508",
   go!"127.0.0.1:7509", go!"127.0.0.1:7510", go!"127.0.0.1:7511"]

end VsrWire

namespace Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet

/-- Every machine's configuration address (`CfgAddrs()`), machine `n` at `n`. -/
def cfgAddrs : List GoString :=
  [go!"127.0.0.1:7520", go!"127.0.0.1:7521", go!"127.0.0.1:7522", go!"127.0.0.1:7523",
   go!"127.0.0.1:7524", go!"127.0.0.1:7525", go!"127.0.0.1:7526", go!"127.0.0.1:7527",
   go!"127.0.0.1:7528", go!"127.0.0.1:7529", go!"127.0.0.1:7530", go!"127.0.0.1:7531"]

/-- The client machines' addresses (`ClientAddrs()`), client `c`'s at `c`. -/
def clientAddrs : List GoString :=
  [go!"127.0.0.1:7541", go!"127.0.0.1:7542", go!"127.0.0.1:7543", go!"127.0.0.1:7544",
   go!"127.0.0.1:7545", go!"127.0.0.1:7546"]

end Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet
